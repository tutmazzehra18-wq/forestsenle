const http = require('http');
const fs = require('fs');
const path = require('path');
const crypto = require('crypto');
const zlib = require('zlib');
let DatabaseSync = null;
try {
  ({ DatabaseSync } = require('node:sqlite'));
} catch (_) {
  DatabaseSync = null;
}
const { Server } = require('socket.io');
const NetworkPhysics = require('./game/networkPhysics.js');
const LootCatalog = require('./game/lootCatalog.js');
const ResourceYield = require('./game/resourceYield.js');

function loadDotEnv(filePath) {
  if (!fs.existsSync(filePath)) return;
  const lines = fs.readFileSync(filePath, 'utf8').split(/\r?\n/);
  for (const line of lines) {
    const trimmed = line.trim();
    if (!trimmed || trimmed.startsWith('#')) continue;
    const match = trimmed.match(/^([A-Za-z_][A-Za-z0-9_]*)\s*=\s*(.*)$/);
    if (!match) continue;
    const [, key, rawValue] = match;
    let value = rawValue.trim();
    if ((value.startsWith('"') && value.endsWith('"')) || (value.startsWith("'") && value.endsWith("'"))) {
      value = value.slice(1, -1);
    }
    process.env[key] = value;
  }
}

loadDotEnv(path.join(__dirname, '.env'));

const isProduction = process.env.NODE_ENV === 'production' || Boolean(process.env.RENDER);
const PORT = Number(process.env.PORT || 3000);
const root = path.join(__dirname, 'game');
const players = new Map();
const buildings = new Map();
const rooms = new Map();
const BUILDING_CELL_SIZE = 180;
const SERVER_BUILD_LIMITS = { 3: 25, 4: 7, 5: 12, 6: 8, 7: 4, 8: 35, 9: 12, 10: 2 };
const TRAP_MAX_HP = 240;
const BUILD_COSTS = { 3: [20, 5, 0], 4: [40, 20, 0], 5: [10, 20, 0], 6: [30, 10, 0], 7: [60, 40, 0], 8: [30, 0, 0], 9: [80, 60, 0], 10: [25, 0, 0] };
const BUILD_RADII = { 3: 34, 4: 44, 5: 22, 6: 78, 7: 58, 8: 24, 9: 52, 10: 30 };
const BUILD_OVERLAP_RADII = { 3: 42, 4: 54, 5: 40, 6: 55, 7: 66, 8: 40, 9: 56, 10: 32 };
const BUILD_MAX_HP = { 3: 180, 4: 120, 5: 100, 6: 240, 7: 200, 8: 350, 9: 800, 10: 100 };
const BUILD_TIER_HP_MULTIPLIERS = Object.freeze([1, 1.6, 2.5, 4, 6.5, 10]);
const BUILD_DURABILITY_MULTIPLIER = 2;
const BUILDING_MELEE_DAMAGE_MULTIPLIER = 0.4;
const SCYTHE_DAMAGE_MULTIPLIER = 0.55;
const BUILDING_HIT_COOLDOWN_MS = 250;
const MOB_TRAP_HOLD_MS = 3000;
const MOB_TRAP_REENTRY_COOLDOWN_MS = 1500;
const WEAPON_TIER_DAMAGE_MULTIPLIERS = Object.freeze([1, 1.35, 1.8, 2.4, 3.2, 4.2, 5.4, 6.8, 8.4, 10.2, 12.2, 14.5]);
const BUILD_ACTION_COOLDOWN = 50;
const TRAP_CAPTURE_DEPTH = 4;

function calculateMeleeDamage(weapon, tier, { isScythe = false, damageMultiplier = 1, maxDamage = 420, buildingDamageMultiplier = 1 } = {}) {
  const tierIndex = Math.max(0, Math.min(11, Math.floor(Number(tier) || 0)));
  const rawDamage = Math.min(maxDamage, Math.round((weapon === 2 ? 30 : 22) * WEAPON_TIER_DAMAGE_MULTIPLIERS[tierIndex] * damageMultiplier));
  const weaponMultiplier = isScythe ? SCYTHE_DAMAGE_MULTIPLIER : 1;
  return Math.max(1, Math.round(rawDamage * weaponMultiplier * buildingDamageMultiplier));
}

function getBuildingMaxHp(type, tier = 0) {
  const tierIndex = Math.max(0, Math.min(5, Math.floor(Number(tier) || 0)));
  const baseHp = type === 6 ? TRAP_MAX_HP : (BUILD_MAX_HP[type] || 100);
  return Math.round(baseHp * BUILD_DURABILITY_MULTIPLIER * BUILD_TIER_HP_MULTIPLIERS[tierIndex]);
}

function trapCaptureRadius(trap, targetRadius = 35) {
  const trapRadius = Number(trap?.radius) || 78;
  const target = Number(targetRadius) || 35;
  // Keep the capture shell inside the visible trap edge, but still allow a small
  // overlap so targets can be caught cleanly without slipping through the ring.
  return Math.max(22, Math.min(trapRadius * 0.92, trapRadius - target * 0.45 + 18));
}
const TURRET_RANGE_BY_TIER = Object.freeze([340, 380, 420, 470, 530, 600]);
const TURRET_DAMAGE_MULTIPLIERS = Object.freeze([1, 1.5, 2.2, 3.5, 5, 8]);

function turretTier(turret) {
  return Math.max(0, Math.min(5, Math.floor(Number(turret?.tier) || 0)));
}

function turretDamage(turret) {
  return Math.min(240, Math.round(45 * TURRET_DAMAGE_MULTIPLIERS[turretTier(turret)]));
}

function turretProjectileDamage(turret) {
  return turretDamage(turret);
}

function turretRange(turret) {
  return TURRET_RANGE_BY_TIER[turretTier(turret)];
}

function buildingCollisionRadius(building) {
  if (!building) return 36;
  return Number(building.radius) || BUILD_RADII[Number(building.type)] || 36;
}

function resolveMobBuildingCollision(mob, building, previousPosition = null, now = Date.now()) {
  if (!mob || !building || (building.hp ?? 100) <= 0 || building.type === 5) {
    return { collided: false, trapped: false };
  }

  const mobRadius = Number(mob.radius) || 36;
  const buildingX = Number(building.x) || 0;
  const buildingY = Number(building.y) || 0;
  const currentX = Number(mob.x) || 0;
  const currentY = Number(mob.y) || 0;
  const startX = Number.isFinite(Number(previousPosition?.x)) ? Number(previousPosition.x) : currentX;
  const startY = Number.isFinite(Number(previousPosition?.y)) ? Number(previousPosition.y) : currentY;
  const segmentX = currentX - startX;
  const segmentY = currentY - startY;
  const segmentLengthSquared = segmentX * segmentX + segmentY * segmentY;
  const closestPointOnPath = () => {
    const t = segmentLengthSquared > 1e-9
      ? Math.max(0, Math.min(1, ((buildingX - startX) * segmentX + (buildingY - startY) * segmentY) / segmentLengthSquared))
      : 1;
    const x = startX + segmentX * t;
    const y = startY + segmentY * t;
    const dx = x - buildingX;
    const dy = y - buildingY;
    return { x, y, dx, dy, distanceSquared: dx * dx + dy * dy };
  };

  if (building.type === 6) {
    if (mob.trapIgnoreBuildingId === building.id && now < (mob.trapIgnoreUntil || 0)) {
      return { collided: false, trapped: false };
    }
    const captureRadius = trapCaptureRadius(building, mobRadius);
    let captureX = currentX;
    let captureY = currentY;
    let dx = currentX - buildingX;
    let dy = currentY - buildingY;
    let distanceSquared = dx * dx + dy * dy;
    if (distanceSquared > captureRadius * captureRadius) {
      const closest = closestPointOnPath();
      if (closest.distanceSquared > captureRadius * captureRadius) return { collided: false, trapped: false };
      const distance = Math.sqrt(closest.distanceSquared);
      const fallbackX = segmentLengthSquared > 1e-9 ? -segmentX : Math.cos(Number(mob.angle) || 0);
      const fallbackY = segmentLengthSquared > 1e-9 ? -segmentY : Math.sin(Number(mob.angle) || 0);
      const fallbackLength = Math.hypot(fallbackX, fallbackY) || 1;
      const normalX = distance > 1e-6 ? closest.dx / distance : fallbackX / fallbackLength;
      const normalY = distance > 1e-6 ? closest.dy / distance : fallbackY / fallbackLength;
      const lockRadius = Math.max(1, captureRadius - 2);
      captureX = buildingX + normalX * lockRadius;
      captureY = buildingY + normalY * lockRadius;
      dx = captureX - buildingX;
      dy = captureY - buildingY;
      distanceSquared = dx * dx + dy * dy;
    }
    mob.x = captureX;
    mob.y = captureY;
    mob.trappedBy = building.id;
    mob.trappedX = captureX;
    mob.trappedY = captureY;
    mob.trappedUntil = now + MOB_TRAP_HOLD_MS;
    mob.vx = 0;
    mob.vy = 0;
    mob.state = 'walk';
    mob.angle = Math.atan2(dy, dx);
    return { collided: false, trapped: true };
  }

  const buildingRadius = Number(building.radius) || BUILD_RADII[building.type] || 36;
  const minimumDistance = mobRadius + buildingRadius;
  let contactX = currentX;
  let contactY = currentY;
  let dx = currentX - buildingX;
  let dy = currentY - buildingY;
  let distanceSquared = dx * dx + dy * dy;
  if (distanceSquared >= minimumDistance * minimumDistance) {
    const closest = closestPointOnPath();
    if (closest.distanceSquared >= minimumDistance * minimumDistance) return { collided: false, trapped: false };
    contactX = closest.x;
    contactY = closest.y;
    dx = closest.dx;
    dy = closest.dy;
    distanceSquared = closest.distanceSquared;
  }

  const distance = Math.sqrt(distanceSquared);
  const angle = Number.isFinite(Number(mob.angle)) ? Number(mob.angle) : 0;
  const fallbackX = segmentLengthSquared > 1e-9 ? -segmentX : Math.cos(angle);
  const fallbackY = segmentLengthSquared > 1e-9 ? -segmentY : Math.sin(angle);
  const fallbackLength = Math.hypot(fallbackX, fallbackY) || 1;
  const normalX = distance > 1e-6 ? dx / distance : fallbackX / fallbackLength;
  const normalY = distance > 1e-6 ? dy / distance : fallbackY / fallbackLength;
  const overlap = minimumDistance - distance;
  mob.x = buildingX + normalX * minimumDistance;
  mob.y = buildingY + normalY * minimumDistance;

  const inwardVelocity = (Number(mob.vx) || 0) * normalX + (Number(mob.vy) || 0) * normalY;
  if (inwardVelocity < 0) {
    mob.vx -= inwardVelocity * normalX;
    mob.vy -= inwardVelocity * normalY;
  }
  return { collided: true, trapped: false, overlap };
}

let buildingGrid = new Map();
function rebuildBuildingGrid() {
  const nextGrid = new Map();
  for (const building of buildings.values()) {
    if (!building || (building.hp ?? 1) <= 0) continue;
    const key = `${Math.floor((Number(building.x) || 0) / BUILDING_CELL_SIZE)},${Math.floor((Number(building.y) || 0) / BUILDING_CELL_SIZE)}`;
    const bucket = nextGrid.get(key);
    if (bucket) bucket.push(building);
    else nextGrid.set(key, [building]);
  }
  buildingGrid = nextGrid;
  buildingGridNeedsRebuild = false;
}

function scheduleBuildingGridRebuild() {
  buildingGridNeedsRebuild = true;
}
function nearbyBuildings(x, y, radius) {
  const minX = Math.floor((x - radius) / BUILDING_CELL_SIZE);
  const maxX = Math.floor((x + radius) / BUILDING_CELL_SIZE);
  const minY = Math.floor((y - radius) / BUILDING_CELL_SIZE);
  const maxY = Math.floor((y + radius) / BUILDING_CELL_SIZE);
  const nearby = [];
  for (let cellX = minX; cellX <= maxX; cellX++) {
    for (let cellY = minY; cellY <= maxY; cellY++) {
      const bucket = buildingGrid.get(`${cellX},${cellY}`);
      if (bucket) {
        for (let bi = 0; bi < bucket.length; bi++) {
          const b = bucket[bi];
          if (b && (b.hp ?? 1) > 0 && buildings.has(b.id)) nearby.push(b);
        }
      }
    }
  }
  return nearby;
}
function buildingsOverlap(first, second) {
  const firstWall = Number(first.type) === 8;
  const secondWall = Number(second.type) === 8;
  if (firstWall && secondWall) {
    return Math.abs(first.x - second.x) < 84 && Math.abs(first.y - second.y) < 80;
  }
  const firstRadius = BUILD_OVERLAP_RADII[Number(first.type)] || 30;
  const secondRadius = BUILD_OVERLAP_RADII[Number(second.type)] || 30;
  return Math.hypot(first.x - second.x, first.y - second.y) < firstRadius + secondRadius - 2;
}
const parties = new Map();
const clans = new Map();
const sessions = new Map();
setInterval(() => {
  const cutoff = Date.now() - 14 * 24 * 60 * 60 * 1000;
  const entriesToDelete = [];
  for (const [token, data] of sessions) {
    const time = typeof data === 'object' && data ? data.createdAt : null;
    if (time && time < cutoff) entriesToDelete.push(token);
  }
  for (const token of entriesToDelete) {
    sessions.delete(token);
  }
  if (sessions.size > 10000) {
    const sortedByAge = [...sessions.entries()].sort((a, b) => {
      const timeA = typeof a[1] === 'object' && a[1] ? a[1].createdAt : 0;
      const timeB = typeof b[1] === 'object' && b[1] ? b[1].createdAt : 0;
      return timeA - timeB;
    });
    const excess = sessions.size - 10000;
    for (let i = 0; i < excess && i < sortedByAge.length; i++) {
      sessions.delete(sortedByAge[i][0]);
    }
  }
}, 60 * 60 * 1000).unref();
const ownerSessions = new Map();
const ownerSessionTtl = 12 * 60 * 60 * 1000;
const ownerAuditLog = [];
const adminConfig = {
  maintenance: false,
  pvpEnabled: true,
  xpRate: 1,
  mobSpawnMultiplier: 1,
  resourceRespawnMultiplier: 1,
  announcement: '',
  mainMenuLayout: {
    portrait: {
      leftEventsContainer: { xPercent: 10, yPercent: 20, widthPercent: 84, heightPercent: 16 },
      headerMain: { xPercent: 50, yPercent: 8, widthPercent: 96, heightPercent: 12 },
      headerRightPanel: { xPercent: 82, yPercent: 10, widthPercent: 18, heightPercent: 22 },
      profileHud: { xPercent: 26, yPercent: 8, widthPercent: 42, heightPercent: 10 },
      inviteEvent: { xPercent: 18, yPercent: 27, widthPercent: 34, heightPercent: 20 },
      creatorEvent: { xPercent: 18, yPercent: 48, widthPercent: 34, heightPercent: 20 },
      mainMenu: { xPercent: 50, yPercent: 58, widthPercent: 86, heightPercent: 50 },
      nameInput: { xPercent: 50, yPercent: 34, widthPercent: 78, heightPercent: 9 },
      activePetBtn: { xPercent: 50, yPercent: 48, widthPercent: 78, heightPercent: 16 },
      playBtn: { xPercent: 50, yPercent: 65, widthPercent: 88, heightPercent: 15 },
      actionButtons: { xPercent: 50, yPercent: 77, widthPercent: 82, heightPercent: 12 },
      profileModal: { xPercent: 50, yPercent: 50, widthPercent: 90, heightPercent: 72 },
      cosmeticsModal: { xPercent: 50, yPercent: 50, widthPercent: 94, heightPercent: 82 },
      shopModal: { xPercent: 50, yPercent: 50, widthPercent: 96, heightPercent: 86 },
      levelRewardsModal: { xPercent: 50, yPercent: 50, widthPercent: 90, heightPercent: 72 },
      newsModal: { xPercent: 50, yPercent: 50, widthPercent: 88, heightPercent: 64 },
      friendInviteModal: { xPercent: 50, yPercent: 50, widthPercent: 94, heightPercent: 84 },
      creatorEventModal: { xPercent: 50, yPercent: 50, widthPercent: 96, heightPercent: 86 },
      leadersModal: { xPercent: 50, yPercent: 50, widthPercent: 92, heightPercent: 78 },
      challengesModal: { xPercent: 50, yPercent: 50, widthPercent: 92, heightPercent: 78 },
      dailyRewardModal: { xPercent: 50, yPercent: 50, widthPercent: 92, heightPercent: 70 },
      partyModal: { xPercent: 50, yPercent: 50, widthPercent: 88, heightPercent: 64 },
      helpModal: { xPercent: 50, yPercent: 50, widthPercent: 88, heightPercent: 64 }
    },
    landscape: {
      leftEventsContainer: { xPercent: 2, yPercent: 20, widthPercent: 22, heightPercent: 42 },
      headerMain: { xPercent: 50, yPercent: 8, widthPercent: 98, heightPercent: 14 },
      headerRightPanel: { xPercent: 75, yPercent: 8, widthPercent: 22, heightPercent: 36 },
      profileHud: { xPercent: 21, yPercent: 8, widthPercent: 26, heightPercent: 10 },
      inviteEvent: { xPercent: 12, yPercent: 32, widthPercent: 22, heightPercent: 26 },
      creatorEvent: { xPercent: 12, yPercent: 62, widthPercent: 22, heightPercent: 26 },
      mainMenu: { xPercent: 50, yPercent: 50, widthPercent: 42, heightPercent: 75 },
      nameInput: { xPercent: 50, yPercent: 32, widthPercent: 72, heightPercent: 7 },
      activePetBtn: { xPercent: 50, yPercent: 42, widthPercent: 72, heightPercent: 14 },
      playBtn: { xPercent: 50, yPercent: 60, widthPercent: 80, heightPercent: 12 },
      actionButtons: { xPercent: 50, yPercent: 72, widthPercent: 72, heightPercent: 11 },
      profileModal: { xPercent: 50, yPercent: 50, widthPercent: 34, heightPercent: 72 },
      cosmeticsModal: { xPercent: 50, yPercent: 50, widthPercent: 54, heightPercent: 82 },
      shopModal: { xPercent: 50, yPercent: 50, widthPercent: 64, heightPercent: 86 },
      levelRewardsModal: { xPercent: 50, yPercent: 50, widthPercent: 38, heightPercent: 72 },
      newsModal: { xPercent: 50, yPercent: 50, widthPercent: 34, heightPercent: 64 },
      friendInviteModal: { xPercent: 50, yPercent: 50, widthPercent: 46, heightPercent: 84 },
      creatorEventModal: { xPercent: 50, yPercent: 50, widthPercent: 54, heightPercent: 86 },
      leadersModal: { xPercent: 50, yPercent: 50, widthPercent: 42, heightPercent: 78 },
      challengesModal: { xPercent: 50, yPercent: 50, widthPercent: 42, heightPercent: 78 },
      dailyRewardModal: { xPercent: 50, yPercent: 50, widthPercent: 40, heightPercent: 70 },
      partyModal: { xPercent: 50, yPercent: 50, widthPercent: 32, heightPercent: 64 },
      helpModal: { xPercent: 50, yPercent: 50, widthPercent: 34, heightPercent: 64 }
    }
  }
};

function clampRange(value, min, max, fallback = min) {
  const numeric = Number(value);
  if (!Number.isFinite(numeric)) return fallback;
  return Math.min(Math.max(numeric, min), max);
}

function normalizeMainMenuLayout(layout) {
  const fallback = adminConfig.mainMenuLayout || { portrait: {}, landscape: {} };
  const safe = {
    portrait: { ...(fallback.portrait || {}) },
    landscape: { ...(fallback.landscape || {}) }
  };

  if (!layout || typeof layout !== 'object') return safe;

  const layoutEntries = layout.portrait || layout.landscape ? ['portrait', 'landscape'] : ['landscape'];
  for (const mode of layoutEntries) {
    const source = layout[mode] || layout || {};
    const target = safe[mode] || {};
    const keys = Object.keys(target).length ? Object.keys(target) : Object.keys(source);

    for (const key of keys) {
      const value = source[key] || target[key];
      if (!value || typeof value !== 'object') continue;
      target[key] = {
        xPercent: clampRange(Number(value.xPercent ?? value.x ?? target[key]?.xPercent ?? 50), 0, 100),
        yPercent: clampRange(Number(value.yPercent ?? value.y ?? target[key]?.yPercent ?? 50), 0, 100),
        widthPercent: clampRange(Number(value.widthPercent ?? value.w ?? target[key]?.widthPercent ?? 20), 8, 100),
        heightPercent: clampRange(Number(value.heightPercent ?? value.h ?? target[key]?.heightPercent ?? 20), 8, 100)
      };
    }
    safe[mode] = { ...target };
  }

  if (!layout.portrait && !layout.landscape && Object.keys(layout).length) {
    const flatKeys = Object.keys(layout);
    for (const key of flatKeys) {
      const value = layout[key];
      if (!value || typeof value !== 'object') continue;
      safe.landscape[key] = {
        xPercent: clampRange(Number(value.xPercent ?? value.x ?? safe.landscape[key]?.xPercent ?? 50), 0, 100),
        yPercent: clampRange(Number(value.yPercent ?? value.y ?? safe.landscape[key]?.yPercent ?? 50), 0, 100),
        widthPercent: clampRange(Number(value.widthPercent ?? value.w ?? safe.landscape[key]?.widthPercent ?? 20), 8, 100),
        heightPercent: clampRange(Number(value.heightPercent ?? value.h ?? safe.landscape[key]?.heightPercent ?? 20), 8, 100)
      };
      safe.portrait[key] = { ...safe.landscape[key] };
    }
  }

  return safe;
}
function getOwnerCredentials() {
  loadDotEnv(path.join(__dirname, '.env'));
  const envUser = String(process.env.OWNER_USERNAME || '').trim().toLowerCase();
  const envPass = String(process.env.OWNER_PASSWORD || '').trim();
  if (isProduction) {
    return { username: envUser, password: envPass };
  }
  const username = envUser || 'owner';
  const password = envPass || 'admin';
  return { username, password };
}
function timingSafeEqualText(left, right) {
  const leftBuffer = Buffer.from(String(left));
  const rightBuffer = Buffer.from(String(right));
  return leftBuffer.length === rightBuffer.length && crypto.timingSafeEqual(leftBuffer, rightBuffer);
}
function ownerTokenFor(username) {
  return crypto.createHmac('sha256', authSecret).update(`owner:${username}:${Date.now()}:${crypto.randomBytes(16).toString('hex')}`).digest('hex');
}
function getOwnerSession(request) {
  const header = String(request.headers.authorization || '');
  const token = header.startsWith('Bearer ') ? header.slice(7) : '';
  const session = ownerSessions.get(token);
  if (!session || session.expiresAt <= Date.now()) {
    if (token) ownerSessions.delete(token);
    return null;
  }
  session.lastSeenAt = Date.now();
  return session;
}
function ownerAudit(action, meta = {}) {
  ownerAuditLog.unshift({ action, at: Date.now(), ...meta });
  if (ownerAuditLog.length > 100) ownerAuditLog.length = 100;
  if (sqliteDb) {
    try {
      sqliteDb.prepare('INSERT INTO game_state (state_key, state_json, updated_at) VALUES (?, ?, ?) ON CONFLICT(state_key) DO UPDATE SET state_json = excluded.state_json, updated_at = excluded.updated_at').run('owner_audit', JSON.stringify(ownerAuditLog), Date.now());
    } catch (_) {}
  }
}
function ownerRequired(request, response) {
  const session = getOwnerSession(request);
  if (!session) {
    sendJson(response, 401, { error: 'Owner oturumu gerekli.' });
    return null;
  }
  return session;
}
function pvpAllowed() {
  return adminConfig.pvpEnabled !== false;
}

function deletePlayerBuildings(playerId) {
  if (!playerId) return;
  const deletedIds = [];
  for (const [id, b] of buildings) {
    if (b.ownerId === playerId || b._ownerId === playerId) {
      if (Number(b.type) === 6) releaseTrapVictims(id);
      buildings.delete(id);
      deletedIds.push(id);
    }
  }
  if (deletedIds.length > 0) {
    scheduleBuildingGridRebuild();
    for (const id of deletedIds) {
      io.emit('build_destroy', { id });
      io.emit('trap_freed', { buildingId: id });
    }
  }
}

const reconnectSessions = new Map();
setInterval(() => {
  const cutoff = Date.now() - 60000;
  for (const [guestId, session] of reconnectSessions) {
    if (session.savedAt < cutoff) {
      if (session.socketId) {
        deletePlayerBuildings(session.socketId);
      }
      reconnectSessions.delete(guestId);
    }
  }
}, 30000).unref();
const mobs = new Map();
const mobHitCooldowns = new Map();
const trapPushCooldowns = new Map();
setInterval(() => {
  const now = Date.now();
  if (trapPushCooldowns.size > 150) {
    for (const [key, time] of trapPushCooldowns) {
      if (now - time > 10000) trapPushCooldowns.delete(key);
    }
  }
  if (mobHitCooldowns.size > 300) {
    for (const [key, time] of mobHitCooldowns) {
      if (now - time > 15000) mobHitCooldowns.delete(key);
    }
  }
}, 30000);

const authRateLimits = new Map();
const autoBannedIps = new Map();
const AUTO_BAN_THRESHOLD = 30;
const AUTO_BAN_DURATION_MS = 60 * 60 * 1000;

const AUTH_LIMITS = {
  login: { max: 12, windowMs: 10 * 60 * 1000 },
  register: { max: 5, windowMs: 60 * 60 * 1000 },
  profile_state: { max: 12, windowMs: 60 * 1000 },
  profile_xp: { max: 2, windowMs: 30 * 1000 },
  shop_buy: { max: 10, windowMs: 60 * 1000 },
  diamond_buy: { max: 10, windowMs: 60 * 1000 },
  daily_reward_claim: { max: 5, windowMs: 60 * 1000 },
  quests_claim: { max: 15, windowMs: 60 * 1000 },
  level_reward: { max: 10, windowMs: 60 * 1000 },
  invite_claim: { max: 10, windowMs: 60 * 1000 },
  creator_claim: { max: 10, windowMs: 60 * 1000 }
};
const claimLocks = new Set();
const MAX_ACCOUNT_XP = 25_000_000;
const MAX_ACCOUNT_COINS = 50_000_000;
const MAX_ACCOUNT_SCORE = 25_000_000;

function clampNumber(value, fallback = 0, min = 0, max = Number.MAX_SAFE_INTEGER) {
  const numeric = Number(value);
  if (!Number.isFinite(numeric)) return fallback;
  return Math.min(Math.max(numeric, min), max);
}

function normalizeWorldCoord(value, fallback = 0, limit = 11200) {
  const numeric = Number(value);
  if (!Number.isFinite(numeric)) return fallback;
  return Math.max(-limit, Math.min(limit, numeric));
}

function normalizePlayerSnapshot(player) {
  if (!player || typeof player !== 'object') return null;
  player.x = normalizeWorldCoord(player.x, 0);
  player.y = normalizeWorldCoord(player.y, 0);
  player.angle = Number.isFinite(Number(player.angle)) ? Number(player.angle) : 0;
  player.hp = clampNumber(player.hp, player.maxHp ?? 250, 0, player.maxHp ?? 250);
  player.maxHp = clampNumber(player.maxHp, 250, 1, 5000);
  player.gold = clampNumber(player.gold, 0, 0, MAX_ACCOUNT_COINS);
  player.xp = clampNumber(player.xp, 0, 0, MAX_ACCOUNT_XP);
  player.score = clampNumber(player.score, 0, 0, MAX_ACCOUNT_SCORE);
  player.sc = player.score;
  player.wood = clampNumber(player.wood, 0, 0, 2_000_000);
  player.stone = clampNumber(player.stone, 0, 0, 2_000_000);
  player.apples = clampNumber(player.apples, 0, 0, 10000);
  return player;
}

function sanitizeOwnedItems(rawValue) {
  if (!Array.isArray(rawValue)) return [];
  const seen = new Set();
  const items = [];
  for (const item of rawValue.slice(0, 200)) {
    const next = String(item || '').trim();
    if (!next || seen.has(next)) continue;
    seen.add(next);
    items.push(next);
  }
  return items;
}

function sanitizeLootBag(rawValue) {
  if (!Array.isArray(rawValue)) return [];
  const seen = new Set();
  const items = [];
  for (const entry of rawValue.slice(0, 32)) {
    const id = String(entry?.id || '');
    const uid = String(entry?.uid || '');
    if (!LootCatalog.ITEM_BY_ID[id] || !/^[a-f0-9-]{36}$/i.test(uid) || seen.has(uid)) continue;
    seen.add(uid);
    items.push({ uid, id });
  }
  return items;
}

function sanitizeLootEquipment(rawValue, bag) {
  const equipped = {};
  const used = new Set(bag.map(item => item.uid));
  const slots = new Set(['head', 'amulet', 'gloves', 'chest', 'ring1', 'ring2', 'mainhand', 'pants', 'offhand', 'boots']);
  if (!rawValue || typeof rawValue !== 'object' || Array.isArray(rawValue)) return equipped;
  for (const [slot, itemValue] of Object.entries(rawValue)) {
    const uid = String(itemValue?.uid || '');
    const id = String(itemValue?.id || '');
    const definition = LootCatalog.ITEM_BY_ID[id];
    const slotMatches = definition && /^[a-f0-9-]{36}$/i.test(uid)
      && (definition.slot === slot || (definition.slot === 'ring' && (slot === 'ring1' || slot === 'ring2')));
    if (!slots.has(slot) || !slotMatches || used.has(uid)) continue;
    equipped[slot] = { uid, id };
    used.add(uid);
  }
  return equipped;
}

const SOCKET_EVENT_LIMITS = {
  state: [90, 1000], swing: [35, 1000], pvp_hit: [35, 1000], arrow_hit: [16, 1000],
  spike_hit: [20, 1000], trap_touch: [25, 1000], mob_trap_hit: [12, 1000],
  trap_owner_push: [35, 1000], res_hit: [25, 1000], mob_hit_req: [20, 1000],
  world_boss_hit_req: [20, 1000], world_boss_turret_hit_req: [20, 1000],
  place_building: [25, 1000], building_hit: [20, 1000], build_hp_update: [20, 1000], build_tier_update: [60, 1000], build_repair: [4, 1000],
  chat: [4, 2000], quick_chat: [8, 2000], eat_apple: [12, 1000],
  sync_combat_stats: [2, 1000],
  craft_blacksmith_item: [15, 1000], equip_blacksmith_item: [10, 1000], helmet_equip: [5, 1000],
  scythe_purchase: [5, 1000], scythe_equip: [10, 1000],
  loot_inventory_init: [3, 10000], loot_item_action: [12, 1000]
};

function socketEventRateLimited(socket, eventName) {
  const limit = SOCKET_EVENT_LIMITS[eventName];
  if (!limit) return false;
  const now = Date.now();
  const [max, windowMs] = limit;
  const rates = socket.data.rateLimits || (socket.data.rateLimits = new Map());
  const current = rates.get(eventName);
  if (!current || now - current.startedAt >= windowMs) {
    rates.set(eventName, { startedAt: now, count: 1 });
    return false;
  }
  current.count++;
  return current.count > max;
}
function requestClientKey(request) {
  const forwarded = String(request.headers['x-forwarded-for'] || '').split(',')[0].trim();
  return forwarded || request.socket.remoteAddress || 'unknown';
}
function authRateLimited(request, action) {
  const policy = AUTH_LIMITS[action];
  if (!policy) return false;
  const clientKey = requestClientKey(request);
  const key = `${action}:${clientKey}`;
  const now = Date.now();
  const entry = authRateLimits.get(key);
  if (!entry || now - entry.startedAt >= policy.windowMs) {
    authRateLimits.set(key, { startedAt: now, count: 1 });
    return false;
  }
  entry.count++;
  const isLimited = entry.count > policy.max;
  
  if (isLimited) {
    const banKey = clientKey;
    const banEntry = autoBannedIps.get(banKey);
    if (!banEntry) {
      autoBannedIps.set(banKey, { count: 1, firstAt: now });
    } else {
      banEntry.count++;
      if (banEntry.count >= AUTO_BAN_THRESHOLD) {
        bannedList.add(banKey);
        bannedList.add(usernameKey(banKey));
        saveBannedList();
        console.warn(`[Security] Auto-banned IP ${banKey} for exceeding rate limit threshold ${AUTO_BAN_THRESHOLD} times`);
      }
    }
  }
  
  return isLimited;
}
setInterval(() => {
  const now = Date.now();
  for (const [key, entry] of authRateLimits) {
    const action = key.split(':', 1)[0];
    if (!AUTH_LIMITS[action] || now - entry.startedAt >= AUTH_LIMITS[action].windowMs) authRateLimits.delete(key);
  }
  for (const [key, entry] of autoBannedIps) {
    if (now - entry.firstAt > AUTO_BAN_DURATION_MS) autoBannedIps.delete(key);
  }
}, 15 * 60 * 1000).unref();
const MOB_TYPES = [
  // Village Outskirts Starter Peaceful Wildlife (Lv 1 - 3)
  { shape: 'wild_hare', biome: 'forest', color: '#b59373', outline: '#3b2512', eyes: '#222222', typeName: '🐰 Yaban Tavşanı', radius: 75, hp: 100, dmg: 15, speed: 22, wanderSpeed: 12, xpReward: 35, goldReward: 12, baseLevel: 1, minLevel: 1, maxLevel: 2, isPeaceful: true },
  { shape: 'forest_deer', biome: 'forest', color: '#966039', outline: '#3b200e', eyes: '#2b1810', typeName: '🦌 Orman Geyiği', radius: 95, hp: 240, dmg: 25, speed: 20, wanderSpeed: 11, xpReward: 60, goldReward: 18, baseLevel: 2, minLevel: 2, maxLevel: 3, isPeaceful: true },
  // Forest (Orman Biyomu) — Outskirts (Lv 3-6) to Deep Woods (Lv 7-28)
  { shape: 'forest_hornet', biome: 'forest', color: '#d8a628', outline: '#4a3108', eyes: '#ff4422', typeName: '🐝 Orman Eşek Arısı', radius: 85, hp: 280, dmg: 40, speed: 23, wanderSpeed: 13, xpReward: 105, goldReward: 26, baseLevel: 4, minLevel: 3, maxLevel: 5 },
  { shape: 'wolf', biome: 'forest', color: '#6b4932', outline: '#28170d', eyes: '#ffcc66', typeName: '🐺 Kurt', radius: 90, hp: 320, dmg: 50, speed: 19, wanderSpeed: 10, xpReward: 90, goldReward: 24, baseLevel: 4, minLevel: 4, maxLevel: 6 },
  { shape: 'wild_boar', biome: 'forest', color: '#70503b', outline: '#2d1c12', eyes: '#ffcf9a', typeName: '🐗 Yaban Domuzu', radius: 110, hp: 480, dmg: 65, speed: 17, wanderSpeed: 10, xpReward: 145, goldReward: 36, baseLevel: 7, minLevel: 6, maxLevel: 9 },
  { shape: 'spider', biome: 'forest', color: '#2a1a38', outline: '#0f0814', eyes: '#ff1100', typeName: '🕷️ Örümcek', radius: 95, hp: 560, dmg: 75, speed: 17, wanderSpeed: 9, xpReward: 180, goldReward: 44, baseLevel: 10, minLevel: 8, maxLevel: 12 },
  { shape: 'scorpion', biome: 'forest', color: '#4a2818', outline: '#1a0d06', eyes: '#ff4400', typeName: '🦂 Akrep', radius: 105, hp: 700, dmg: 90, speed: 15, wanderSpeed: 9, xpReward: 220, goldReward: 54, baseLevel: 12, minLevel: 10, maxLevel: 15 },
  { shape: 'bear', biome: 'forest', color: '#4a2f1b', outline: '#1a1008', eyes: '#ffaa00', typeName: '🐻 Ayı', radius: 130, hp: 1020, dmg: 110, speed: 14, wanderSpeed: 8, xpReward: 330, goldReward: 85, baseLevel: 14, minLevel: 12, maxLevel: 17 },
  { shape: 'grizzly_bear', biome: 'forest', color: '#765137', outline: '#2d1a10', eyes: '#ffb347', typeName: '🐻 Boz Ayı', radius: 150, hp: 1450, dmg: 140, speed: 13, wanderSpeed: 7, xpReward: 450, goldReward: 110, baseLevel: 18, minLevel: 16, maxLevel: 21 },
  { shape: 'elder_wendigo', biome: 'forest', color: '#8d9b79', outline: '#263126', eyes: '#b9ffcf', typeName: '👹 Kadim Wendigo', radius: 185, hp: 2350, dmg: 175, speed: 14, wanderSpeed: 8, xpReward: 680, goldReward: 185, baseLevel: 22, minLevel: 20, maxLevel: 25 },
  { shape: 'treant_boss', biome: 'forest', color: '#56713a', outline: '#1e3218', eyes: '#aaff66', typeName: '🌳 Ağaç Devi', radius: 230, hp: 7000, dmg: 200, speed: 10, wanderSpeed: 6, xpReward: 1000, goldReward: 280, baseLevel: 26, minLevel: 25, maxLevel: 28, isBoss: true },

  // Winter (Kış / Buzul Zirveleri Biyomu) — Lv 22 - 45
  { shape: 'frost_fox', biome: 'winter', color: '#e2edff', outline: '#2c3e55', eyes: '#38b6ff', typeName: '🦊 Kutup Tilkisi', radius: 85, hp: 620, dmg: 80, speed: 20, wanderSpeed: 12, xpReward: 280, goldReward: 70, baseLevel: 24, minLevel: 22, maxLevel: 26 },
  { shape: 'polar_bear', biome: 'winter', color: '#f0f5fb', outline: '#3b4b5e', eyes: '#00e5ff', typeName: '🐻‍❄️ Kutup Ayısı', radius: 150, hp: 1550, dmg: 150, speed: 15, wanderSpeed: 9, xpReward: 520, goldReward: 130, baseLevel: 30, minLevel: 28, maxLevel: 34 },
  { shape: 'mammoth', biome: 'winter', color: '#46382f', outline: '#1c1510', eyes: '#82c8ff', typeName: '🦣 Mamut', radius: 205, hp: 2800, dmg: 200, speed: 12, wanderSpeed: 7, xpReward: 820, goldReward: 220, baseLevel: 38, minLevel: 35, maxLevel: 45 },

  // Desert (Çöl / Kum Tepeleri Biyomu) — Lv 24 - 45
  { shape: 'sand_viper', biome: 'desert', color: '#c89a42', outline: '#4a330e', eyes: '#ffe600', typeName: '🐍 Çöl Engereği', radius: 85, hp: 660, dmg: 90, speed: 19, wanderSpeed: 11, xpReward: 300, goldReward: 75, baseLevel: 26, minLevel: 24, maxLevel: 28 },
  { shape: 'dune_scorpion', biome: 'desert', color: '#9e6d2b', outline: '#382306', eyes: '#00ff66', typeName: '🦂 Kum Akrebi', radius: 115, hp: 980, dmg: 120, speed: 16, wanderSpeed: 10, xpReward: 410, goldReward: 100, baseLevel: 32, minLevel: 30, maxLevel: 36 },
  { shape: 'dune_lizard', biome: 'desert', color: '#7a7042', outline: '#2b2711', eyes: '#ff9900', typeName: '🦎 Dikenli Kertenkele', radius: 135, hp: 1550, dmg: 145, speed: 17, wanderSpeed: 10, xpReward: 560, goldReward: 140, baseLevel: 38, minLevel: 36, maxLevel: 45 },

  // Lava (Lav / Volkanik Caldera Biyomu) — Lv 38 - 65
  { shape: 'magma_hound', biome: 'lava', color: '#2a1410', outline: '#ff3700', eyes: '#ffcc00', typeName: '🐺 Magma Tazısı', radius: 110, hp: 1020, dmg: 135, speed: 19, wanderSpeed: 11, xpReward: 450, goldReward: 115, baseLevel: 40, minLevel: 38, maxLevel: 46 },
  { shape: 'fire_drake', biome: 'lava', color: '#420d09', outline: '#ff1e00', eyes: '#ffee33', typeName: '🐉 Lav Ejderhası', radius: 170, hp: 2050, dmg: 195, speed: 17, wanderSpeed: 10, xpReward: 760, goldReward: 205, baseLevel: 48, minLevel: 46, maxLevel: 56 },
  { shape: 'obsidian_golem', biome: 'lava', color: '#18121a', outline: '#ff4400', eyes: '#ff0033', typeName: '🗿 Obsidyen Devi', radius: 220, hp: 10000, dmg: 240, speed: 11, wanderSpeed: 6, xpReward: 1050, goldReward: 290, baseLevel: 56, minLevel: 54, maxLevel: 65, isBoss: true },
];
const databaseFile = process.env.DATABASE_FILE || path.join(__dirname, 'forestbrawl.db');
let sqliteDb = null;
let databaseLastError = null;
try {
  if (DatabaseSync) {
    fs.mkdirSync(path.dirname(databaseFile), { recursive: true });
    sqliteDb = new DatabaseSync(databaseFile);
    sqliteDb.exec('PRAGMA journal_mode = WAL; PRAGMA synchronous = FULL; CREATE TABLE IF NOT EXISTS game_state (state_key TEXT PRIMARY KEY, state_json TEXT NOT NULL, updated_at INTEGER NOT NULL)');
    console.log(`[Database] SQLite ready: ${databaseFile}`);
  } else {
    console.warn('[Database] node:sqlite not available in this Node runtime; running in-memory state.');
  }
} catch (error) {
  databaseLastError = error.message;
  console.warn(`[Database] SQLite unavailable; starting with empty in-memory state: ${error.message}`);
}
function loadAdminConfig() {
  if (!sqliteDb) return;
  try {
    const row = sqliteDb.prepare('SELECT state_json FROM game_state WHERE state_key = ?').get('admin_config');
    if (!row) return;
    const saved = JSON.parse(row.state_json);
    for (const key of Object.keys(adminConfig)) {
      if (saved[key] !== undefined) {
        adminConfig[key] = key === 'mainMenuLayout'
          ? normalizeMainMenuLayout(saved[key])
          : saved[key];
      }
    }
  } catch (error) {
    console.warn(`[Database] Admin config read failed: ${error.message}`);
  }
}
function loadOwnerAudit() {
  if (!sqliteDb) return;
  try {
    const row = sqliteDb.prepare('SELECT state_json FROM game_state WHERE state_key = ?').get('owner_audit');
    if (!row) return;
    const saved = JSON.parse(row.state_json);
    if (Array.isArray(saved)) ownerAuditLog.push(...saved.slice(0, 100));
  } catch (_) {}
}
function saveAdminConfig() {
  if (!sqliteDb) return false;
  try {
    sqliteDb.prepare('INSERT INTO game_state (state_key, state_json, updated_at) VALUES (?, ?, ?) ON CONFLICT(state_key) DO UPDATE SET state_json = excluded.state_json, updated_at = excluded.updated_at').run('admin_config', JSON.stringify(adminConfig), Date.now());
    return true;
  } catch (error) {
    console.warn(`[Database] Admin config write failed: ${error.message}`);
    return false;
  }
}
loadAdminConfig();
loadOwnerAudit();
const bannedList = new Set();
function loadBannedList() {
  if (!sqliteDb) return;
  try {
    const row = sqliteDb.prepare('SELECT state_json FROM game_state WHERE state_key = ?').get('banned_list');
    if (!row) return;
    const saved = JSON.parse(row.state_json);
    if (Array.isArray(saved)) saved.forEach(item => bannedList.add(String(item)));
  } catch (_) {}
}
function saveBannedList() {
  if (!sqliteDb) return false;
  try {
    sqliteDb.prepare('INSERT INTO game_state (state_key, state_json, updated_at) VALUES (?, ?, ?) ON CONFLICT(state_key) DO UPDATE SET state_json = excluded.state_json, updated_at = excluded.updated_at').run('banned_list', JSON.stringify([...bannedList]), Date.now());
    return true;
  } catch (_) { return false; }
}
loadBannedList();
function isClientBanned(clientKey, username) {
  if (clientKey && bannedList.has(clientKey)) return true;
  if (username && bannedList.has(usernameKey(username))) return true;
  return false;
}
const configuredAuthSecret = String(process.env.AUTH_SECRET || '').trim();
const authSecret = configuredAuthSecret || crypto.createHash('sha256').update(`forestbrawl:${path.resolve(databaseFile)}`).digest('hex');
const AUTH_TOKEN_TTL_MS = 14 * 24 * 60 * 60 * 1000;
// isProduction is declared at top of file
if (!configuredAuthSecret) {
  if (isProduction) {
    console.error('[Security] AUTH_SECRET is required in production. Server cannot start without AUTH_SECRET.');
    process.exit(1);
  } else {
    console.warn('[Security] AUTH_SECRET is not set; using a stable development secret. Set AUTH_SECRET in production.');
  }
}
if (isProduction && (!process.env.OWNER_USERNAME?.trim() || !process.env.OWNER_PASSWORD?.trim())) {
  console.error('[Security] OWNER_USERNAME and OWNER_PASSWORD are required in production. Server cannot start without both values.');
  process.exit(1);
}
function normalizeAllowedOrigin(origin) {
  return String(origin || '')
    .trim()
    .replace(/\/+$/, '')
    .replace(/^https?:\/\//, '')
    .toLowerCase();
}
const configuredAllowedOrigins = String(process.env.ALLOWED_ORIGINS || '')
  .split(',')
  .map(origin => normalizeAllowedOrigin(origin))
  .filter(Boolean);
const defaultAllowedOrigins = [
  'https://forestbrawl.fun',
  'https://www.forestbrawl.fun',
  'https://titotu.io',
  'https://www.titotu.io',
  'https://titotu.ru',
  'https://www.titotu.ru',
  'http://localhost:3000',
  'http://127.0.0.1:3000',
  'http://0.0.0.0:3000',
  'http://localhost',
  'http://127.0.0.1',
  'http://0.0.0.0',
];
const allowedOrigins = new Set([
  ...configuredAllowedOrigins,
  ...defaultAllowedOrigins.map(normalizeAllowedOrigin),
].filter(Boolean));
const allowedOriginHostnames = new Set([...allowedOrigins].map(origin => {
  return origin.replace(/^https?:\/\//, '').split(':')[0];
}));
allowedOriginHostnames.add('localhost');
allowedOriginHostnames.add('127.0.0.1');
allowedOriginHostnames.add('0.0.0.0');

function isAllowedOrigin(origin) {
  if (!origin) return true;
  const normalized = normalizeAllowedOrigin(origin);
  if (allowedOrigins.has(normalized)) return true;
  const hostname = normalized.replace(/^https?:\/\//, '').split(':')[0];
  return allowedOriginHostnames.has(hostname);
}
const worldSeed = 0x4F524553;
let nextMobId = 1;
const BOUNTY_EVENT_ENABLED = process.env.BOUNTY_EVENT_ENABLED !== 'false';
let currentBountyId = null;
let buildingGridNeedsRebuild = false;
setInterval(() => {
  if (buildingGridNeedsRebuild) {
    rebuildBuildingGrid();
    buildingGridNeedsRebuild = false;
  }
}, 500);

const QUESTS_LIST = [
  { id: 'q_wolf_100', title: 'Kurt Sürüsünün Sonu', desc: 'Ormanda 100 vahşi kurt avla', icon: '🐺', key: 'wolves', target: 100, rewardCoins: 1800, rewardXp: 1600 },
  { id: 'q_bear_40', title: 'Ayıların Efendisi', desc: '40 orman ayısını savaşta alt et', icon: '🐻', key: 'bears', target: 40, rewardCoins: 3200, rewardXp: 3000 },
  { id: 'q_scorpion_60', title: 'Çölün Zehir Ustası', desc: 'Çölde 60 akrebi yok et', icon: '🦂', key: 'scorpions', target: 60, rewardCoins: 2800, rewardXp: 2600 },
  { id: 'q_spider_60', title: 'Mağara Temizliği', desc: '60 zehirli örümceği ortadan kaldır', icon: '🕷️', key: 'spiders', target: 60, rewardCoins: 2800, rewardXp: 2600 },
  { id: 'q_pvp_kill_25', title: 'Arena Celladı', desc: '25 düşman oyuncuyu PvP’de katlet', icon: '⚔️', key: 'kills', target: 25, rewardCoins: 5000, rewardXp: 4500 },
  { id: 'q_bounty_king_3', title: 'Altın Kralların Sonu', desc: '3 kez hüküm süren ödül kralını indir', icon: '👑', key: 'kingKills', target: 3, rewardCoins: 6500, rewardXp: 6000 },
  { id: 'q_build_100', title: 'Orman Kalesi', desc: '100 savunma yapısı inşa et', icon: '🪵', key: 'buildings', target: 100, rewardCoins: 3500, rewardXp: 3200 },
  { id: 'q_gold_10000', title: 'Ormanın Hazinedarı', desc: 'Kaynaklardan toplam 10.000 altın çıkar', icon: '🪙', key: 'gold', target: 10000, rewardCoins: 6000, rewardXp: 5500 }
];

const DAILY_QUEST_POOL = [
  { id: 'daily_wood_250', title: 'Genç Oduncu', desc: '250 odun topla', icon: '🪵', key: 'wood', target: 250, rewardCoins: 180, rewardXp: 120, difficulty: 'easy' },
  { id: 'daily_stone_150', title: 'Taşın İlk Sırrı', desc: '150 taş topla', icon: '🪨', key: 'stone', target: 150, rewardCoins: 180, rewardXp: 120, difficulty: 'easy' },
  { id: 'daily_gold_100', title: 'Parlayan Damar', desc: '100 altın çıkar', icon: '🪙', key: 'gold', target: 100, rewardCoins: 220, rewardXp: 150, difficulty: 'easy' },
  { id: 'daily_survive_4', title: 'İlk Nöbet', desc: 'Toplam 4 dakika hayatta kal', icon: '⏱️', key: 'time', target: 4, rewardCoins: 220, rewardXp: 160, difficulty: 'easy' },
  { id: 'daily_build_8', title: 'Siper Kur', desc: '8 yapı inşa et', icon: '🧱', key: 'buildings', target: 8, rewardCoins: 240, rewardXp: 180, difficulty: 'easy' },
  { id: 'daily_kills_3', title: 'İlk Av', desc: '3 düşman oyuncuyu alt et', icon: '⚔️', key: 'pvpKills', target: 3, rewardCoins: 260, rewardXp: 200, difficulty: 'easy' },
  { id: 'daily_wood_900', title: 'Orman Maratonu', desc: '900 odun topla', icon: '🌲', key: 'wood', target: 900, rewardCoins: 650, rewardXp: 500, difficulty: 'medium' },
  { id: 'daily_stone_700', title: 'Kaya Ustası', desc: '700 taş topla', icon: '⛏️', key: 'stone', target: 700, rewardCoins: 700, rewardXp: 560, difficulty: 'medium' },
  { id: 'daily_gold_500', title: 'Altın Damarı', desc: '500 altın çıkar', icon: '💰', key: 'gold', target: 500, rewardCoins: 850, rewardXp: 700, difficulty: 'medium' },
  { id: 'daily_survive_12', title: 'Uzun Nöbet', desc: 'Toplam 12 dakika hayatta kal', icon: '⌛', key: 'time', target: 12, rewardCoins: 800, rewardXp: 720, difficulty: 'medium' },
  { id: 'daily_build_30', title: 'Kale Mühendisi', desc: '30 yapı inşa et', icon: '🏗️', key: 'buildings', target: 30, rewardCoins: 900, rewardXp: 760, difficulty: 'medium' },
  { id: 'daily_kills_12', title: 'Arena Takibi', desc: '8 düşman oyuncuyu alt et', icon: '🗡️', key: 'pvpKills', target: 8, rewardCoins: 1100, rewardXp: 900, difficulty: 'medium' },
  { id: 'daily_wolves_35', title: 'Kurt Sürücüsü', desc: '35 vahşi kurt avla', icon: '🐺', key: 'wolves', target: 35, rewardCoins: 760, rewardXp: 620, difficulty: 'medium' },
  { id: 'daily_bears_12', title: 'Ayı Avcısı', desc: '12 orman ayısını alt et', icon: '🐻', key: 'bears', target: 12, rewardCoins: 1000, rewardXp: 850, difficulty: 'medium' },
  { id: 'daily_kills_35', title: 'Kızıl Arena', desc: '12 düşman oyuncuyu alt et', icon: '🩸', key: 'pvpKills', target: 12, rewardCoins: 2600, rewardXp: 2200, difficulty: 'hard' },
  { id: 'daily_kills_60', title: 'Avcıların Avcısı', desc: '15 düşman oyuncuyu alt et', icon: '☠️', key: 'pvpKills', target: 15, rewardCoins: 3300, rewardXp: 2800, difficulty: 'hard' },
  { id: 'daily_survive_30', title: 'Karanlık Nöbet', desc: 'Toplam 20 dakika hayatta kal', icon: '🌙', key: 'time', target: 20, rewardCoins: 2200, rewardXp: 1900, difficulty: 'hard' },
  { id: 'daily_wood_3000', title: 'Orman Yutan', desc: '1.200 odun topla', icon: '🌳', key: 'wood', target: 1200, rewardCoins: 1800, rewardXp: 1500, difficulty: 'hard' },
  { id: 'daily_stone_2500', title: 'Dağ Söken', desc: '1.000 taş topla', icon: '⛰️', key: 'stone', target: 1000, rewardCoins: 1800, rewardXp: 1500, difficulty: 'hard' },
  { id: 'daily_gold_2000', title: 'Hazine Lordu', desc: '1.000 altın çıkar', icon: '👑', key: 'gold', target: 1000, rewardCoins: 2200, rewardXp: 1800, difficulty: 'hard' },
  { id: 'daily_build_100', title: 'Sınır Kalesi', desc: '40 yapı inşa et', icon: '🏰', key: 'buildings', target: 40, rewardCoins: 1800, rewardXp: 1500, difficulty: 'hard' },
  { id: 'daily_wolves_120', title: 'Sürülerin Sonu', desc: '20 vahşi kurt avla', icon: '🐺', key: 'wolves', target: 20, rewardCoins: 1600, rewardXp: 1300, difficulty: 'hard' },
  { id: 'daily_bears_45', title: 'Ayıların Kâbusu', desc: '10 orman ayısını alt et', icon: '🐻', key: 'bears', target: 10, rewardCoins: 1800, rewardXp: 1500, difficulty: 'hard' },
  { id: 'daily_scorpions_70', title: 'Zehir Tahtı', desc: '12 akrebi yok et', icon: '🦂', key: 'scorpions', target: 12, rewardCoins: 1800, rewardXp: 1500, difficulty: 'hard' },
  { id: 'daily_spiders_80', title: 'Mağara Fatihi', desc: '12 zehirli örümceği yok et', icon: '🕷️', key: 'spiders', target: 12, rewardCoins: 1800, rewardXp: 1500, difficulty: 'hard' },
  { id: 'daily_boss_1', title: 'Birlikte Daha Güçlü', desc: 'Bir dünya boss savaşına katkı ver', icon: '🐉', key: 'bosses', target: 1, rewardCoins: 2400, rewardXp: 2000, difficulty: 'hard' },
  { id: 'daily_build_180', title: 'Orman İmparatorluğu', desc: '80 yapı inşa et', icon: '🛡️', key: 'buildings', target: 80, rewardCoins: 2800, rewardXp: 2400, difficulty: 'hard' }
];

const ULTRA_QUESTS = [
  { id: 'ultra_kills_500', title: 'Savaş Tanrısı', desc: '500 düşman oyuncuyu PvP’de alt et', icon: '⚔️', key: 'pvpKills', target: 500, rewardCoins: 30000, rewardXp: 24000, difficulty: 'ultra' },
  { id: 'ultra_time_600', title: 'Sonsuz Nöbet', desc: 'Toplam 10 saat hayatta kal', icon: '⌛', key: 'time', target: 600, rewardCoins: 24000, rewardXp: 20000, difficulty: 'ultra' },
  { id: 'ultra_gold_100000', title: 'Altın İmparatorluğu', desc: 'Kaynaklardan toplam 100.000 altın çıkar', icon: '💰', key: 'gold', target: 100000, rewardCoins: 35000, rewardXp: 28000, difficulty: 'ultra' },
  { id: 'ultra_buildings_1000', title: 'Büyük Orman Kalesi', desc: '1.000 savunma yapısı inşa et', icon: '🏰', key: 'buildings', target: 1000, rewardCoins: 28000, rewardXp: 22000, difficulty: 'ultra' },
  { id: 'ultra_king_25', title: 'Kralların Kralı', desc: '25 ödül kralını alt et', icon: '👑', key: 'kingKills', target: 25, rewardCoins: 32000, rewardXp: 26000, difficulty: 'ultra' },
  { id: 'ultra_wolves_1000', title: 'Sürülerin Hükümdarı', desc: '1.000 vahşi kurt avla', icon: '🐺', key: 'wolves', target: 1000, rewardCoins: 22000, rewardXp: 18000, difficulty: 'ultra' },
  { id: 'ultra_spiders_500', title: 'Derinliklerin Fatihi', desc: '500 zehirli örümceği yok et', icon: '🕷️', key: 'spiders', target: 500, rewardCoins: 20000, rewardXp: 16000, difficulty: 'ultra' }
];

const DAILY_REWARDS = [25, 40, 60, 90, 130, 180, 250];
const MATCH_XP_RATE = 0.04;
const QUEST_XP_RATE = 0.2;
const BATTLE_PASS_SEASON_MS = 28 * 24 * 60 * 60 * 1000;
const BATTLE_PASS_TIERS = Object.freeze([
  { tier: 1, xp: 100, type: 'coins', value: 200, label: '+200 Altın' },
  { tier: 2, xp: 200, type: 'accountXp', value: 500, label: '+500 Hesap XP' },
  { tier: 3, xp: 350, type: 'coins', value: 300, label: '+300 Altın' },
  { tier: 4, xp: 550, type: 'coins', value: 250, label: '+250 Altın' },
  { tier: 5, xp: 800, type: 'accountXp', value: 1000, label: '+1.000 Hesap XP' },
  { tier: 6, xp: 1100, type: 'coins', value: 350, label: '+350 Altın' },
  { tier: 7, xp: 1450, type: 'coins', value: 500, label: '+500 Altın' },
  { tier: 8, xp: 1850, type: 'accountXp', value: 1500, label: '+1.500 Hesap XP' },
  { tier: 9, xp: 2300, type: 'coins', value: 500, label: '+500 Altın' },
  { tier: 10, xp: 2800, type: 'coins', value: 500, label: '+500 Altın' },
  { tier: 11, xp: 3400, type: 'accountXp', value: 2000, label: '+2.000 Hesap XP' },
  { tier: 12, xp: 4100, type: 'coins', value: 1000, label: '+1.000 Altın' },
  { tier: 13, xp: 4900, type: 'coins', value: 700, label: '+700 Altın' },
  { tier: 14, xp: 5800, type: 'accountXp', value: 3000, label: '+3.000 Hesap XP' },
  { tier: 15, xp: 6800, type: 'coins', value: 1000, label: '+1.000 Altın' },
  { tier: 16, xp: 7900, type: 'coins', value: 2000, label: '+2.000 Altın' },
  { tier: 17, xp: 9100, type: 'accountXp', value: 5000, label: '+5.000 Hesap XP' },
  { tier: 18, xp: 10400, type: 'coins', value: 1200, label: '+1.200 Altın' },
  { tier: 19, xp: 11800, type: 'coins', value: 1500, label: '+1.500 Altın' },
  { tier: 20, xp: 13300, type: 'coins', value: 3000, label: '+3.000 Altın' }
]);
const BATTLE_PASS_MAX_XP = BATTLE_PASS_TIERS[BATTLE_PASS_TIERS.length - 1].xp;
const LEVEL_REWARD_BASE_COINS = 25;
const LEVEL_REWARD_STEP_COINS = 5;
const XP_RESET_VERSION = 3;
const COIN_RESET_VERSION = 1;

const CHEST_CONFIG = {
  wood_chest: { cost: 5, rewards: ['penguin', 'frog', 'croc', 'fox', 'panda', 'rabbit', 'skin_desert', 'skin_emerald', 'skin_reef', 'skin_steam', 'skin_blossom', 'robot'] },
  gold_chest: { cost: 15, rewards: ['dragon', 'phoenix', 'skin_aurora', 'skin_storm', 'skin_sapphire', 'skin_ruby', 'skin_frostwolf', 'skin_cyber', 'yeti', 'robot', 'ninja', 'kiz_orman'] },
  rare_chest: { cost: 30, rewards: ['dragon', 'phoenix', 'kiz_ates', 'kiz_buz', 'skin_void', 'skin_moon', 'skin_amethyst', 'skin_icefire', 'skin_reef', 'skin_shadow', 'skin_thunder', 'yeti', 'robot', 'shark'] },
  ame_chest: { cost: 60, rewards: ['kiz_ates', 'kiz_buz', 'kiz_samurai', 'skin_magma', 'skin_solar', 'skin_icefire', 'skin_thunder', 'skin_chroma', 'skin_void', 'kiz_karanlik', 'phoenix', 'dragon'] }
};
const cosmeticCatalog = [];
const COSMETIC_TYPES = new Set(['skin', 'axe', 'sword']);
const COSMETIC_RARITIES = new Set(['common', 'rare', 'epic', 'legendary', 'mythic']);
const FREE_SHOP_ITEMS = new Set(['wolf', 'default', 'ki_tier_0', 'ba_tier_0']);
function normalizeShopItemId(itemId) {
  return String(itemId || '').trim().toLowerCase();
}
function normalizedShopPrice(value, rarity = 'common') {
  const key = String(rarity || 'common').toLowerCase();
  const scale = { common: 0.02, rare: 0.04, epic: 0.06, legendary: 0.08, mythic: 0.1 }[key] || 0.1;
  const floor = { common: 2, rare: 4, epic: 8, legendary: 15, mythic: 30 }[key] || 8;
  return Math.max(floor, Math.round((Number(value) || 0) * scale));
}
const BUILTIN_SHOP_PRICES = Object.freeze({
  fox: 12, dragon: 96, ninja: 48, skull: 54, polarbear: 18,
  lion: 51, croc: 16, frog: 14, phoenix: 120, robot: 60,
  panda: 20, shark: 57, rabbit: 16, penguin: 4, octopus: 54,
  yeti: 51, kiz_ates: 112, kiz_buz: 112, kiz_samurai: 128,
  kiz_peri: 144, kiz_neon: 160, kiz_vampir: 176, kiz_orman: 120,
  kiz_deniz: 128, kiz_sakura: 136, kiz_karanlik: 192,
  skin_aurora: 8, skin_storm: 8, skin_magma: 15, skin_void: 15,
  skin_solar: 15, skin_moon: 8, skin_emerald: 4, skin_sapphire: 4,
  skin_ruby: 8, skin_amethyst: 8, skin_cyber: 15, skin_steam: 4,
  skin_icefire: 15, skin_thunder: 15, skin_blossom: 4, skin_reef: 4,
  skin_desert: 2, skin_frostwolf: 8, skin_shadow: 8, skin_chroma: 15,
  ninja_4k_asset: 150, deniz_4k_asset: 150, ates_4k_asset: 180,
  tavsan_4k_asset: 130, panda_4k_asset: 140, robot_4k_asset: 180,
  kafatasi_4k_asset: 150, ejder_4k_asset: 220, savasci_4k_asset: 170,
  kurt_4k_asset: 130, zehir_kralicesi_god_tier: 520,
  gunes_tanrisi_god_tier: 560, serafim_god_tier: 620,
  kristal_ejder_god_tier: 660, hiclik_tirpani_god_tier: 500,
  toprak_titani_god_tier: 540, biyo_mutant_god_tier: 560,
  siber_iblis_god_tier: 620, kadim_dehset_god_tier_2: 700,
  kozmik_varlik_god_tier: 780,
  ki_tier_1: 4, ki_tier_2: 9, ki_tier_3: 15, ki_tier_4: 22,
  ki_tier_5: 32, ki_tier_6: 50,
  ba_tier_1: 4, ba_tier_2: 9, ba_tier_3: 15, ba_tier_4: 22,
  ba_tier_5: 32, ba_tier_6: 50
});
function findShopItem(itemId) {
  const id = normalizeShopItemId(itemId);
  const catalogItem = cosmeticCatalog.find(item => item.id === id);
  if (catalogItem) return { ...catalogItem, price: normalizedShopPrice(catalogItem.price, catalogItem.rarity) };
  const price = BUILTIN_SHOP_PRICES[id];
  if (price === undefined) return null;
  return { id, type: id.startsWith('ki_') ? 'sword' : id.startsWith('ba_') ? 'axe' : 'skin', price };
}
const COSMETIC_ASSET_DIR = path.join(root, 'cosmetics');
const MAX_COSMETIC_PNG_BYTES = 6 * 1024 * 1024;
try { fs.mkdirSync(COSMETIC_ASSET_DIR, { recursive: true }); } catch (_) {}

function parsePngInfo(buffer) {
  const signature = Buffer.from([137, 80, 78, 71, 13, 10, 26, 10]);
  if (!Buffer.isBuffer(buffer) || buffer.length < 24) return null;
  if (!buffer.subarray(0, 8).equals(signature)) return null;
  if (buffer.toString('ascii', 12, 16) !== 'IHDR') return null;
  
  const width = buffer.readUInt32BE(16);
  const height = buffer.readUInt32BE(20);
  const bitDepth = buffer.readUInt8(24);
  const colorType = buffer.readUInt8(25);
  const compression = buffer.readUInt8(26);
  const filter = buffer.readUInt8(27);
  const interlace = buffer.readUInt8(28);
  
  if (!width || !height || width > 4096 || height > 4096) return null;
  if (bitDepth !== 8 && bitDepth !== 4 && bitDepth !== 2 && bitDepth !== 1 && bitDepth !== 16) return null;
  if (colorType < 0 || colorType > 6) return null;
  if (compression !== 0) return null;
  if (filter !== 0) return null;
  if (interlace !== 0 && interlace !== 1) return null;
  
  return { width, height, orientation: width === height ? 'square' : width > height ? 'landscape' : 'portrait' };
}

function saveCosmeticPng(itemId, assetData, previousAsset = '') {
  const match = String(assetData || '').match(/^data:image\/png;base64,([A-Za-z0-9+/=\s]+)$/i);
  if (!match) throw new Error('Yalnızca PNG dosyası yükleyebilirsiniz.');
  const buffer = Buffer.from(match[1].replace(/\s/g, ''), 'base64');
  if (!buffer.length || buffer.length > MAX_COSMETIC_PNG_BYTES) throw new Error('PNG dosyası en fazla 6 MB olabilir.');
  const info = parsePngInfo(buffer);
  if (!info) throw new Error('Geçerli bir PNG dosyası yükleyin.');
  const fileName = `${itemId}-${Date.now()}-${crypto.randomBytes(4).toString('hex')}.png`;
  fs.writeFileSync(path.join(COSMETIC_ASSET_DIR, fileName), buffer, { flag: 'wx' });
  if (String(previousAsset).startsWith('cosmetics/')) {
    const previousPath = path.resolve(root, previousAsset);
    if (previousPath.startsWith(`${COSMETIC_ASSET_DIR}${path.sep}`)) fs.rmSync(previousPath, { force: true });
  }
  return { asset: `cosmetics/${fileName}`, ...info };
}

function broadcastCosmeticCatalog(action, item) {
  try { io.emit('cosmetic_catalog_updated', { action, item: item ? publicCosmetic(item) : null }); } catch (_) {}
}
function loadCosmeticCatalog() {
  if (!sqliteDb) return;
  try {
    const row = sqliteDb.prepare('SELECT state_json FROM game_state WHERE state_key = ?').get('cosmetic_catalog');
    if (!row) return;
    const saved = JSON.parse(row.state_json);
    if (Array.isArray(saved)) cosmeticCatalog.push(...saved.filter(item => item && item.id && COSMETIC_TYPES.has(item.type)));
  } catch (_) {}
}
function saveCosmeticCatalog() {
  if (!sqliteDb) return false;
  try {
    sqliteDb.prepare('INSERT INTO game_state (state_key, state_json, updated_at) VALUES (?, ?, ?) ON CONFLICT(state_key) DO UPDATE SET state_json = excluded.state_json, updated_at = excluded.updated_at').run('cosmetic_catalog', JSON.stringify(cosmeticCatalog), Date.now());
    return true;
  } catch (_) { return false; }
}
function publicCosmetic(item) {
  return { id: item.id, type: item.type, name: item.name, rarity: item.rarity, color: item.color, asset: item.asset, price: item.price, width: item.width || 0, height: item.height || 0, orientation: item.orientation || 'unknown', chests: [...(item.chests || [])], createdAt: item.createdAt, updatedAt: item.updatedAt || item.createdAt };
}

function normalizeCatalogSkinId(fileName) {
  const baseName = path.basename(String(fileName || ''), path.extname(String(fileName || '')));
  if (!baseName) return '';
  const normalized = baseName.toLowerCase().replace(/[^a-z0-9]+/g, '_').replace(/^_+|_+$/g, '');
  return normalized || '';
}

function titleCaseCosmeticName(id) {
  return String(id || '')
    .replace(/[_-]+/g, ' ')
    .replace(/\b\w/g, char => char.toUpperCase())
    .replace(/\b4k\b/gi, '4K')
    .replace(/\bGod\b/gi, 'God')
    .replace(/\bTier\b/gi, 'Tier')
    .trim();
}

function rarityForCatalogSkinId(id) {
  const value = String(id || '').toLowerCase();
  if (value.includes('god_tier') || value.includes('varlik') || value.includes('kral') || value.includes('tanrisi') || value.includes('iblis')) return 'mythic';
  if (value.includes('4k') || value.includes('asset') || value.includes('savasci') || value.includes('ejder') || value.includes('robot')) return 'epic';
  if (value.includes('tavsan') || value.includes('panda') || value.includes('kurt') || value.includes('deniz')) return 'rare';
  return 'epic';
}

function priceForCatalogSkinId(id) {
  const value = String(id || '').toLowerCase();
  if (value.includes('god_tier') || value.includes('varlik') || value.includes('iblis') || value.includes('kralicesi')) return 4800;
  if (value.includes('4k') || value.includes('asset') || value.includes('savasci') || value.includes('robot')) return 1800;
  if (value.includes('kurt') || value.includes('tavsan') || value.includes('panda')) return 1400;
  return 2200;
}

function hydrateCatalogFromAssets() {
  if (!fs.existsSync(COSMETIC_ASSET_DIR)) return false;
  let changed = false;
  const pngFiles = fs.readdirSync(COSMETIC_ASSET_DIR)
    .filter(fileName => /\.png$/i.test(fileName))
    .sort((a, b) => a.localeCompare(b, 'tr', { sensitivity: 'base' }));
  const seen = new Set();
  for (const fileName of pngFiles) {
    const id = normalizeCatalogSkinId(fileName);
    if (!id || seen.has(id)) continue;
    seen.add(id);
    const existing = cosmeticCatalog.find(item => item.id === id);
    const asset = `cosmetics/${fileName}`;
    const imagePath = path.join(COSMETIC_ASSET_DIR, fileName);
    let width = 0; let height = 0; let orientation = 'square';
    try {
      const buffer = fs.readFileSync(imagePath);
      const info = parsePngInfo(buffer);
      if (info) { width = info.width; height = info.height; orientation = info.orientation; }
    } catch (_) {}
    const item = {
      id,
      type: 'skin',
      name: String(existing?.name || titleCaseCosmeticName(id)).trim().slice(0, 40) || titleCaseCosmeticName(id),
      rarity: existing?.rarity || rarityForCatalogSkinId(id),
      color: existing?.color || '#b8f36b',
      asset,
      price: existing?.price ?? priceForCatalogSkinId(id),
      width,
      height,
      orientation,
      chests: Array.isArray(existing?.chests) ? existing.chests.slice() : [],
      createdAt: existing?.createdAt || Date.now(),
      updatedAt: Date.now()
    };
    if (existing) {
      const changedEntry = JSON.stringify(existing) !== JSON.stringify(item);
      if (changedEntry) {
        const idx = cosmeticCatalog.indexOf(existing);
        cosmeticCatalog[idx] = item;
        changed = true;
      }
    } else {
      cosmeticCatalog.push(item);
      changed = true;
    }
  }
  if (changed) saveCosmeticCatalog();
  return changed;
}
loadCosmeticCatalog();
hydrateCatalogFromAssets();
const CHEST_LEGENDARY_REWARDS = new Set([
  'dragon', 'phoenix', 'kiz_ates', 'kiz_buz', 'kiz_samurai', 'kiz_orman', 'kiz_karanlik',
  'skin_magma', 'skin_solar', 'skin_void', 'skin_cyber', 'skin_icefire', 'skin_thunder', 'skin_chroma'
]);

function chestRewardWeight(rewardId) {
  if (CHEST_LEGENDARY_REWARDS.has(rewardId)) return 0.05;
  if (String(rewardId).startsWith('skin_')) return 0.22;
  return 1;
}

function chooseChestReward(rewards) {
  const totalWeight = rewards.reduce((sum, rewardId) => sum + chestRewardWeight(rewardId), 0);
  let roll = Math.random() * totalWeight;
  for (const rewardId of rewards) {
    roll -= chestRewardWeight(rewardId);
    if (roll <= 0) return rewardId;
  }
  return rewards[rewards.length - 1];
}

const RANKS = Array.from({ length: 100 }, (_, index) => index === 0 ? 0 : Math.round(1000 * Math.pow(index, 2.1)));
const RANK_NAMES = ['Tohum', 'Taş', 'Köylü', 'Acemi', 'Savaşçı', 'Muhafız', 'Ateş Efendisi', 'Kristal', 'Fırtına', 'Gece Hanı', 'Efsane', 'Tanrısal'];

function rankInfo(xp) {
  let rankId = 0;
  for (let i = 0; i < RANKS.length; i++) {
    if (xp >= RANKS[i]) rankId = i;
    else break;
  }
  const currentMin = RANKS[rankId];
  const isMaxRank = rankId >= RANKS.length - 1;
  const nextMin = isMaxRank ? currentMin : RANKS[rankId + 1];
  const xpProgress = isMaxRank ? 1 : Math.max(0, Math.min(1, (xp - currentMin) / (nextMin - currentMin)));
  const xpToNextRank = isMaxRank ? 0 : Math.max(0, nextMin - xp);
  return {
    rankId,
    visualRankId: Math.min(11, Math.floor((rankId / Math.max(1, RANKS.length - 1)) * 12)),
    level: rankId + 1,
    name: RANK_NAMES[rankId % RANK_NAMES.length],
    minXP: currentMin,
    nextMinXP: nextMin,
    xpProgress: Math.round(xpProgress * 100) / 100,
    xpToNextRank
  };
}

function dailyQuestDayKey(timestamp = Date.now()) {
  return new Date(timestamp).toISOString().slice(0, 10);
}

function dailyRewardState(user, timestamp = Date.now()) {
  const current = user.dailyReward && typeof user.dailyReward === 'object' ? user.dailyReward : {};
  const day = Number(current.day);
  const today = dailyQuestDayKey(timestamp);
  const claimedDate = /^\d{4}-\d{2}-\d{2}$/.test(String(current.claimedDate || '')) ? String(current.claimedDate) : '';
  const isNewDay = Boolean(claimedDate && claimedDate !== today);
  const currentDay = Number.isInteger(day) ? Math.max(1, Math.min(7, day)) : 1;
  const nextDay = isNewDay ? (currentDay >= 7 ? 1 : currentDay + 1) : currentDay;
  return {
    day: nextDay,
    claimedDate: isNewDay ? '' : claimedDate
  };
}

function dailyQuestExpiry(timestamp = Date.now()) {
  const nextDay = new Date(timestamp);
  nextDay.setUTCHours(24, 0, 0, 0);
  return nextDay.getTime();
}

function buildDailyQuestSnapshot(identity, timestamp = Date.now()) {
  const dayKey = dailyQuestDayKey(timestamp);
  const seed = crypto.createHash('sha256').update(`${identity}:${dayKey}`).digest('hex');
  const orderPool = pool => pool.slice().sort((a, b) => {
    const aHash = crypto.createHash('sha256').update(`${seed}:${a.id}`).digest('hex');
    const bHash = crypto.createHash('sha256').update(`${seed}:${b.id}`).digest('hex');
    return aHash.localeCompare(bHash);
  });
  const selected = [
    ...orderPool(DAILY_QUEST_POOL.filter(quest => quest.difficulty === 'easy')).slice(0, 3),
    ...orderPool(DAILY_QUEST_POOL.filter(quest => quest.difficulty === 'medium')).slice(0, 3),
    ...orderPool(DAILY_QUEST_POOL.filter(quest => quest.difficulty === 'hard')).slice(0, 4)
  ];
  return {
    dayKey,
    expiresAt: dailyQuestExpiry(timestamp),
    progress: {},
    tasks: selected.map(quest => ({ ...quest, progress: 0, claimed: false }))
  };
}

function syncQuestProgressToTasks(user, daily, ultra) {
  const questProgress = user && typeof user.questProgress === 'object' ? user.questProgress : {};
  const dailyProgress = user && typeof user.dailyQuestProgress === 'object' ? user.dailyQuestProgress : {};
  for (const task of daily?.tasks || []) {
    task.progress = Math.min(task.target, Math.max(0, Number(dailyProgress[task.key] || 0)));
  }
  for (const task of ultra?.tasks || []) {
    const runningTotal = Math.max(0, Number(questProgress[task.key] || 0));
    task.progress = Math.min(task.target, Math.max(Number(task.progress || 0), runningTotal));
  }
  return daily;
}

function ensureDailyQuests(user, identity = 'guest') {
  if (!user || typeof user !== 'object') {
    throw new TypeError('Daily quest state requires a user object.');
  }
  const today = dailyQuestDayKey();
  const previousTasks = Array.isArray(user.dailyQuests?.tasks) ? user.dailyQuests.tasks : [];
  const schemaChanged = previousTasks.some(task => {
    const current = DAILY_QUEST_POOL.find(quest => quest.id === task?.id);
    return !current || current.key !== task.key || current.target !== task.target;
  });
  const hasRemovedChestQuest = Array.isArray(user.dailyQuests?.tasks)
    && user.dailyQuests.tasks.some(task => task?.key === 'airdrops' || task?.key === 'chests' || String(task?.id || '').includes('airdrop'));
  if (!user.dailyQuests || user.dailyQuests.dayKey !== today || !Array.isArray(user.dailyQuests.tasks) || user.dailyQuests.tasks.length !== 10 || hasRemovedChestQuest) {
    user.dailyQuests = buildDailyQuestSnapshot(identity);
    user.dailyQuestProgress = {};
  } else if (schemaChanged) {
    const claimed = new Map(previousTasks.map(task => [task.id, Boolean(task.claimed)]));
    user.dailyQuests = buildDailyQuestSnapshot(identity);
    user.dailyQuests.tasks.forEach(task => { task.claimed = claimed.get(task.id) || false; });
    user.dailyQuestProgress = {};
  } else if (!user.dailyQuestProgress || typeof user.dailyQuestProgress !== 'object') {
    user.dailyQuestProgress = {};
    user.dailyQuests.progress = {};
  }
  syncQuestProgressToTasks(user, user.dailyQuests, user.ultraQuests);
  return user.dailyQuests;
}

function ensureUltraQuests(user) {
  const schemaChanged = Array.isArray(user.ultraQuests?.tasks)
    && user.ultraQuests.tasks.some(task => ULTRA_QUESTS.find(quest => quest.id === task.id)?.key !== task.key);
  if (!user.ultraQuests || !Array.isArray(user.ultraQuests.tasks) || user.ultraQuests.tasks.length !== ULTRA_QUESTS.length || schemaChanged) {
    const previous = new Map((user.ultraQuests?.tasks || []).map(task => [task.id, task]));
    user.ultraQuests = {
      tasks: ULTRA_QUESTS.map(quest => ({
        ...quest,
        progress: previous.get(quest.id)?.key === quest.key
          ? Math.min(quest.target, Number(previous.get(quest.id)?.progress || 0))
          : 0,
        claimed: previous.get(quest.id)?.key === quest.key && Boolean(previous.get(quest.id)?.claimed)
      }))
    };
  }
  syncQuestProgressToTasks(user, user.dailyQuests, user.ultraQuests);
  return user.ultraQuests;
}

function applyDailyQuestProgress(user, deltas = {}) {
  const daily = ensureDailyQuests(user, usernameKey(user.username));
  const normalizedDeltas = {};
  for (const [key, rawValue] of Object.entries(deltas || {})) {
    const delta = Math.min(1000000, Math.max(0, Number(rawValue) || 0));
    if (delta > 0) normalizedDeltas[key] = delta;
  }
  user.questProgress = { ...(user.questProgress || {}) };
  user.dailyQuestProgress = { ...(user.dailyQuestProgress || {}) };
  for (const [key, delta] of Object.entries(normalizedDeltas)) {
    user.questProgress[key] = Math.max(0, Number(user.questProgress[key]) || 0) + delta;
    user.dailyQuestProgress[key] = Math.max(0, Number(user.dailyQuestProgress[key]) || 0) + delta;
  }
  daily.progress = { ...user.dailyQuestProgress };
  const ultra = ensureUltraQuests(user);
  syncQuestProgressToTasks(user, daily, ultra);
  return daily;
}

function recordServerQuestProgress(player, deltas = {}) {
  if (!player?._authUser || !deltas || typeof deltas !== 'object') return;
  const daily = applyDailyQuestProgress(player._authUser, deltas);
  const ultra = ensureUltraQuests(player._authUser);
  saveAccountData();
  io.to(player.id).emit('quest_progress_update', {
    quests: daily.tasks,
    ultraQuests: ultra.tasks
  });
}

function battlePassSeason(now = Date.now()) {
  return Math.floor(now / BATTLE_PASS_SEASON_MS);
}

function ensureBattlePass(user, now = Date.now()) {
  const season = battlePassSeason(now);
  const saved = user.battlePass;
  if (!saved || Number(saved.season) !== season) {
    user.battlePass = { season, xp: 0, claimedTiers: [] };
  } else {
    user.battlePass = {
      season,
      xp: Math.min(BATTLE_PASS_MAX_XP, Math.max(0, Math.floor(Number(saved.xp) || 0))),
      claimedTiers: Array.isArray(saved.claimedTiers)
        ? [...new Set(saved.claimedTiers.map(Number).filter(tier => Number.isInteger(tier) && BATTLE_PASS_TIERS.some(item => item.tier === tier)))]
        : []
    };
  }
  return user.battlePass;
}

function grantBattlePassMatchXp(user, kills, timeSeconds, score, now = Date.now()) {
  const state = ensureBattlePass(user, now);
  const matchXp = Math.max(5, Math.floor(kills) * 80 + Math.floor(timeSeconds / 60) * 25 + Math.floor(Math.max(0, score) / 20));
  state.xp = Math.min(BATTLE_PASS_MAX_XP, state.xp + matchXp);
  return state;
}

function questMobKey(mob) {
  const shape = String(mob?.shape || '').toLowerCase();
  if (shape.includes('wolf')) return 'wolves';
  if (shape.includes('bear')) return 'bears';
  if (shape.includes('scorpion')) return 'scorpions';
  if (shape.includes('spider') || shape.includes('orumcek')) return 'spiders';
  return null;
}

function hashPassword(password, salt = crypto.randomBytes(16).toString('hex')) {
  return { salt, hash: crypto.scryptSync(password, salt, 64).toString('hex') };
}

let accountData = { users: {}, clans: {}, leaderboard: {}, recentDeaths: [], nextId: 1, revokedTokens: {} };

function readSqliteSnapshot() {
  if (!sqliteDb) return null;
  try {
    const row = sqliteDb.prepare('SELECT state_json FROM game_state WHERE state_key = ?').get('account');
    return row ? JSON.parse(row.state_json) : null;
  } catch (error) {
    databaseLastError = error.message;
    console.warn(`[Database] SQLite read failed: ${error.message}`);
    return null;
  }
}

function writeSqliteSnapshot(snapshot) {
  if (!sqliteDb) return false;
  try {
    sqliteDb.prepare('INSERT INTO game_state (state_key, state_json, updated_at) VALUES (?, ?, ?) ON CONFLICT(state_key) DO UPDATE SET state_json = excluded.state_json, updated_at = excluded.updated_at').run('account', JSON.stringify(snapshot), Date.now());
    databaseLastError = null;
    return true;
  } catch (error) {
    databaseLastError = error.message;
    console.warn(`[Database] SQLite write failed: ${error.message}`);
    return false;
  }
}

const BASILISK_USERNAME_KEY = 'basilisk';
function canUseThor(user) {
  return Boolean(user && usernameKey(user.username) === BASILISK_USERNAME_KEY);
}

function ownedItemsForUser(user, items) {
  const ownedItems = Array.isArray(items) ? [...new Set(items.map(normalizeShopItemId).filter(Boolean))] : [];
  return canUseThor(user) ? ownedItems : ownedItems.filter(itemId => itemId !== 'thor');
}

function normalizeOwnedTiers(values) {
  const tiers = Array.isArray(values)
    ? values.map(Number).filter(tier => Number.isInteger(tier) && tier >= 0 && tier <= 11)
    : [];
  return [...new Set([0, ...tiers])];
}

function normalizeOwnedItemIds(values, pattern) {
  if (!Array.isArray(values)) return [];
  return [...new Set(values
    .filter(value => typeof value === 'string' && pattern.test(value))
    .map(value => value.trim()))];
}

function equippedItemsForUser(user, items) {
  const equippedItems = items && typeof items === 'object' ? { ...items } : {};
  if (!canUseThor(user)) {
    if (equippedItems.deriler === 'thor') equippedItems.deriler = 'wolf';
    if (equippedItems.profil_avatar === 'thor') equippedItems.profil_avatar = 'wolf';
  }
  for (const category of ['deriler', 'kiliclar', 'baltalar']) {
    if (equippedItems[category] && !canEquipShopItem(user, category, equippedItems[category])) delete equippedItems[category];
  }
  return equippedItems;
}

function canEquipShopItem(user, category, itemId) {
  const id = normalizeShopItemId(itemId);
  if (!['deriler', 'kiliclar', 'baltalar'].includes(category)) return true;
  if (id === 'thor') return canUseThor(user);
  if (FREE_SHOP_ITEMS.has(id)) return true;
  const catalogItem = cosmeticCatalog.find(item => item.id === id);
  if (catalogItem && Number(catalogItem.price) <= 0) return true;
  return Array.isArray(user?.ownedItems) && user.ownedItems.some(ownedId => normalizeShopItemId(ownedId) === id);
}

function cosmeticAssetForSkin(skinId) {
  const item = cosmeticCatalog.find(entry => entry.type === 'skin' && entry.id === String(skinId));
  return item?.asset || null;
}

function loadAccountData() {
  const parsed = readSqliteSnapshot();
  if (parsed && typeof parsed === 'object') {
    const rawUsers = parsed.users || {};
    const cleanUsers = {};
    for (const [k, u] of Object.entries(rawUsers)) {
      if (u && typeof u === 'object' && u.username && (u.hash || u.password)) {
        const uKey = String(u.username).trim().toLowerCase();
        const loadedUser = {
          id: u.id || 1,
          username: u.username,
          email: u.email || '',
          salt: u.salt || '',
          hash: u.hash || '',
          rankId: rankInfo(Number(u.xp || 0)).rankId,
          xp: Math.max(0, Number(u.xp || 0)),
          coins: Math.max(0, Number(u.coins ?? u.gold ?? 0)),
          gold: Math.max(0, Number(u.coins ?? u.gold ?? 0)),
          diamonds: Math.max(0, Number(u.diamonds) || 0),
          kills: Math.max(0, Number(u.kills || 0)),
          deaths: Math.max(0, Number(u.deaths || 0)),
          meleeLevel: Math.max(1, Math.min(100, Number(u.meleeLevel) || 1)),
          meleeXp: Math.max(0, Number(u.meleeXp) || 0),
          defenceLevel: Math.max(1, Math.min(100, Number(u.defenceLevel) || 1)),
          defenceXp: Math.max(0, Number(u.defenceXp) || 0),
          games: Math.max(0, Number(u.gamesPlayed || u.games || 0)),
          gamesPlayed: Math.max(0, Number(u.gamesPlayed || u.games || 0)),
          score: Math.max(0, Number(u.score || 0)),
          bestScore: Math.max(0, Number(u.bestScore || u.score || 0)),
          timePlayed: Math.max(0, Number(u.timePlayed || 0)),
          ownedItems: [],
          equippedItems: {},
          ownedAxes: normalizeOwnedTiers(u.ownedAxes),
          ownedSwords: normalizeOwnedTiers(u.ownedSwords),
          ownedHelmets: normalizeOwnedItemIds(u.ownedHelmets, /^helmet_[a-z0-9_]{1,48}$/),
          ownedScythes: normalizeOwnedItemIds(u.ownedScythes, /^scythe_tier_[1-8]$/),
          axeTier: Math.max(0, Math.min(11, Math.floor(Number(u.axeTier) || 0))),
          swordTier: Math.max(0, Math.min(11, Math.floor(Number(u.swordTier) || 0))),
          scytheId: typeof u.scytheId === 'string' ? u.scytheId : null,
          helmetSkin: typeof u.helmetSkin === 'string' ? u.helmetSkin : null,
          lootBag: sanitizeLootBag(u.lootBag),
          lootEquipment: {},
          battlePass: (u.battlePass && typeof u.battlePass === 'object') ? u.battlePass : null,
          questProgress: (u.questProgress && typeof u.questProgress === 'object') ? { ...u.questProgress } : {},
          dailyQuestProgress: (u.dailyQuestProgress && typeof u.dailyQuestProgress === 'object') ? { ...u.dailyQuestProgress } : {},
          claimedQuests: Array.isArray(u.claimedQuests) ? [...new Set(u.claimedQuests)] : [],
          dailyQuests: (u.dailyQuests && typeof u.dailyQuests === 'object') ? u.dailyQuests : null,
          ultraQuests: (u.ultraQuests && typeof u.ultraQuests === 'object') ? u.ultraQuests : null,
          dailyReward: (u.dailyReward && typeof u.dailyReward === 'object') ? u.dailyReward : null,
          claimedLevelRewards: Array.isArray(u.claimedLevelRewards) ? [...new Set(u.claimedLevelRewards.map(Number).filter(Number.isInteger))] : [],
          settings: (u.settings && typeof u.settings === 'object') ? { ...u.settings } : {},
          referralCode: u.referralCode || u.username,
          referredBy: u.referredBy || null,
          inviteEvent: (u.inviteEvent && typeof u.inviteEvent === 'object') ? u.inviteEvent : { claimedMilestones: [false, false, false, false, false], invitedFriends: [] },
          creatorEvent: (u.creatorEvent && typeof u.creatorEvent === 'object') ? u.creatorEvent : { submissions: [], claimedTiers: [false, false, false, false], totalViews: 0, isVerifiedCreator: false },
          createdAt: u.createdAt || Date.now(),
          lastLoginAt: u.lastLoginAt || Date.now(),
          lastMatchAt: u.lastMatchAt || u.lastLoginAt || u.createdAt || Date.now()
        };
        loadedUser.ownedItems = ownedItemsForUser(loadedUser, u.ownedItems);
        loadedUser.equippedItems = equippedItemsForUser(loadedUser, u.equippedItems);
        if (!loadedUser.ownedAxes.includes(loadedUser.axeTier)) loadedUser.axeTier = 0;
        if (!loadedUser.ownedSwords.includes(loadedUser.swordTier)) loadedUser.swordTier = 0;
        if (!loadedUser.ownedScythes.includes(loadedUser.scytheId)) loadedUser.scytheId = null;
        if (!loadedUser.ownedHelmets.includes(loadedUser.helmetSkin)) loadedUser.helmetSkin = null;
        loadedUser.lootEquipment = sanitizeLootEquipment(u.lootEquipment, loadedUser.lootBag);
        cleanUsers[uKey] = loadedUser;
      }
    }
    accountData = {
      users: cleanUsers,
      clans: parsed.clans || {},
      leaderboard: parsed.leaderboard || {},
      recentDeaths: Array.isArray(parsed.recentDeaths) ? parsed.recentDeaths : [],
      nextId: Math.max(parsed.nextId || 1, Object.keys(cleanUsers).length + 1),
      xpResetVersion: Number(parsed.xpResetVersion || 0),
      coinResetVersion: Number(parsed.coinResetVersion || 0),
      revokedTokens: (parsed.revokedTokens && typeof parsed.revokedTokens === 'object') ? parsed.revokedTokens : {}
    };
    console.log(`[Database] Loaded ${Object.keys(cleanUsers).length} users and ${Object.keys(accountData.clans).length} clans.`);
  } else {
    console.log('[Database] Starting with fresh database.');
    accountData = { users: {}, clans: {}, leaderboard: {}, recentDeaths: [], nextId: 1, coinResetVersion: 0, revokedTokens: {} };
  }

  if (Object.keys(accountData.users || {}).length === 0) {
    const ownerCreds = getOwnerCredentials();
    const username = ownerCreds.username || 'owner';
    const password = ownerCreds.password || 'admin';
    const seed = hashPassword(password);
    const key = usernameKey(username);
    accountData.users = {
      [key]: {
        id: 1,
        username,
        email: 'owner@forestbrawl.local',
        salt: seed.salt,
        hash: seed.hash,
        rankId: rankInfo(0).rankId,
        xp: 0,
        coins: 0,
        gold: 0,
        diamonds: 0,
        kills: 0,
        deaths: 0,
        meleeLevel: 1,
        meleeXp: 0,
        defenceLevel: 1,
        defenceXp: 0,
        games: 0,
        gamesPlayed: 0,
        score: 0,
        bestScore: 0,
        timePlayed: 0,
        ownedItems: [],
        equippedItems: {},
        ownedAxes: [0],
        ownedSwords: [0],
        ownedHelmets: [],
        ownedScythes: [],
        axeTier: 0,
        swordTier: 0,
        scytheId: null,
        helmetSkin: null,
        lootBag: [],
        lootEquipment: {},
        questProgress: {},
        claimedQuests: [],
        dailyQuests: null,
        ultraQuests: null,
        dailyReward: { day: 1, claimedDate: '' },
        claimedLevelRewards: [],
        settings: {},
        referralCode: username,
        referredBy: null,
        inviteEvent: { claimedMilestones: [false, false, false, false, false], invitedFriends: [] },
        creatorEvent: { submissions: [], claimedTiers: [false, false, false, false], totalViews: 0, isVerifiedCreator: false },
        createdAt: Date.now(),
        lastLoginAt: Date.now(),
        lastMatchAt: Date.now(),
      }
    };
    accountData.nextId = 2;
    accountData.leaderboard = accountData.leaderboard || {};
    accountData.recentDeaths = Array.isArray(accountData.recentDeaths) ? accountData.recentDeaths : [];
    console.warn('[Database] Account snapshot missing; created environment-owner recovery account in account data.');
    writeSqliteSnapshot(accountData);
  }

  // Progress is never reset on startup. Version markers are retained only for
  // backwards compatibility with older snapshots; migrations must be additive.
  accountData.xpResetVersion = Math.max(Number(accountData.xpResetVersion) || 0, XP_RESET_VERSION);
  accountData.coinResetVersion = Math.max(Number(accountData.coinResetVersion) || 0, COIN_RESET_VERSION);
  writeSqliteSnapshot(accountData);
}

loadAccountData();

function ensureOwnerAccountMatchesEnvironment() {
  const ownerCreds = getOwnerCredentials();
  const username = String(ownerCreds.username || 'owner').trim();
  const password = String(ownerCreds.password || 'admin').trim();
  if (!username || !password) {
    console.warn('[Owner] OWNER_USERNAME and OWNER_PASSWORD must be configured in the environment.');
    return;
  }

  const userKey = usernameKey(username);
  const seeded = hashPassword(password);
  const existing = accountData.users?.[userKey] || Object.values(accountData.users || {}).find(user => usernameKey(user.username) === userKey);

  if (existing) {
    existing.username = username;
    existing.email = existing.email || 'owner@forestbrawl.local';
    existing.salt = seeded.salt;
    existing.hash = seeded.hash;
    existing.lastLoginAt = existing.lastLoginAt || Date.now();
    existing.lastMatchAt = existing.lastMatchAt || Date.now();
    console.log(`[Owner] Synced owner account ${username} from environment credentials.`);
  } else {
    const id = Math.max(1, Number(accountData.nextId) || 1);
    const user = {
      id,
      username,
      email: 'owner@forestbrawl.local',
      salt: seeded.salt,
      hash: seeded.hash,
      rankId: rankInfo(0).rankId,
      xp: 0,
      coins: 0,
      gold: 0,
      diamonds: 0,
      kills: 0,
      deaths: 0,
      meleeLevel: 1,
      meleeXp: 0,
      defenceLevel: 1,
      defenceXp: 0,
      games: 0,
      gamesPlayed: 0,
      score: 0,
      bestScore: 0,
      timePlayed: 0,
      ownedItems: [],
      equippedItems: {},
      ownedAxes: [0],
      ownedSwords: [0],
      ownedHelmets: [],
      ownedScythes: [],
      axeTier: 0,
      swordTier: 0,
      scytheId: null,
      helmetSkin: null,
      lootBag: [],
      lootEquipment: {},
      questProgress: {},
      claimedQuests: [],
      dailyQuests: null,
      ultraQuests: null,
      dailyReward: { day: 1, claimedDate: '' },
      claimedLevelRewards: [],
      settings: {},
      referralCode: username,
      referredBy: null,
      inviteEvent: { claimedMilestones: [false, false, false, false, false], invitedFriends: [] },
      createdAt: Date.now(),
      lastLoginAt: Date.now(),
      lastMatchAt: Date.now(),
    };
    accountData.users[userKey] = user;
    accountData.nextId = id + 1;
    console.warn(`[Owner] Created owner account ${username} from environment credentials.`);
  }

  writeSqliteSnapshot(accountData);
}

ensureOwnerAccountMatchesEnvironment();
for (const clan of Object.values(accountData.clans || {})) clans.set(clan.id, clan);

let _saveTimeout = null;
let _saveInFlight = null;
let _saveQueued = false;
function saveAccountData(immediate = false) {
  const doSave = async () => {
    if (_saveInFlight) {
      _saveQueued = true;
      return _saveInFlight;
    }
    try {
      accountData.users = { ...(accountData.users || {}) };
      accountData.clans = Object.fromEntries(clans);
      writeSqliteSnapshot(accountData);
      _saveInFlight = Promise.resolve();
      await _saveInFlight;
    } catch (error) {
      console.warn('Could not save account data:', error.message);
    } finally {
      _saveInFlight = null;
      if (_saveQueued) {
        _saveQueued = false;
        void doSave();
      }
    }
  };

  if (immediate) {
    if (_saveTimeout) { clearTimeout(_saveTimeout); _saveTimeout = null; }
    return doSave();
  } else {
    if (!_saveTimeout) {
      _saveTimeout = setTimeout(() => {
        _saveTimeout = null;
        doSave();
      }, 250);
    }
  }
}

function updateReferredFriendProgress(user, extraResources = 0, extraKills = 0, extraAliveSec = 0) {
  if (!user || !user.referredBy) return false;
  const inviter = Object.values(accountData.users || {}).find(u => u && (u.id === user.referredBy || u.username === user.referredBy));
  if (!inviter) return false;
  if (!inviter.inviteEvent) {
    inviter.inviteEvent = { claimedMilestones: [false, false, false, false, false], invitedFriends: [] };
  }
  if (!Array.isArray(inviter.inviteEvent.invitedFriends)) inviter.inviteEvent.invitedFriends = [];

  let friendEntry = inviter.inviteEvent.invitedFriends.find(f => f.id === user.id || f.username === user.username);
  if (!friendEntry) {
    friendEntry = {
      id: user.id,
      username: user.username,
      joinedAt: user.createdAt || Date.now(),
      tasks: {
        level: { name: "Seviye 3'e Ulaş", current: 1, target: 3, done: false },
        resources: { name: "500 Kaynak Topla", current: 0, target: 500, done: false },
        kills: { name: "1 Rakip Alt Et", current: 0, target: 1, done: false },
        survival: { name: "3 Dk Hayatta Kal", current: 0, target: 3, done: false }
      },
      completed: false
    };
    inviter.inviteEvent.invitedFriends.push(friendEntry);
  }

  if (!friendEntry.tasks) {
    friendEntry.tasks = {
      level: { name: "Seviye 3'e Ulaş", current: 1, target: 3, done: false },
      resources: { name: "500 Kaynak Topla", current: 0, target: 500, done: false },
      kills: { name: "1 Rakip Alt Et", current: 0, target: 1, done: false },
      survival: { name: "3 Dk Hayatta Kal", current: 0, target: 3, done: false }
    };
  }

  const lvl = rankInfo(Number(user.xp) || 0).level;
  const res = Math.max(Number(extraResources) || 0, Number(friendEntry.tasks.resources?.current || 0));
  const kls = Math.max(Number(user.kills) || 0, Number(extraKills) || 0, Number(friendEntry.tasks.kills?.current || 0));
  const survMinutes = Math.max(
    Math.floor((Number(user.timePlayed) || 0) / 60),
    Math.floor((Number(extraAliveSec) || 0) / 60),
    Number(friendEntry.tasks.survival?.current || 0)
  );

  friendEntry.tasks.level.current = lvl;
  friendEntry.tasks.level.done = lvl >= 3;
  friendEntry.tasks.resources.current = Math.min(500, res);
  friendEntry.tasks.resources.done = res >= 500;
  friendEntry.tasks.kills.current = kls;
  friendEntry.tasks.kills.done = kls >= 1;
  friendEntry.tasks.survival.current = Math.min(3, survMinutes);
  friendEntry.tasks.survival.done = survMinutes >= 3;

  if (friendEntry.tasks.level.done && friendEntry.tasks.resources.done && friendEntry.tasks.kills.done && friendEntry.tasks.survival.done) {
    friendEntry.completed = true;
  }

  return true;
}

function syncLivePlayerProgress(player) {
  const user = player?._authUser;
  if (!user || !user.username) return false;
  const score = Math.max(0, Number(player.score) || 0);
  const gold = Math.max(0, Number(player.gold) || 0);
  const kills = Math.max(0, Number(player.kills) || 0);
  const previous = `${user.score}|${user.gold}|${user.kills}|${user.bestScore}`;
  user.score = score;
  user.bestScore = Math.max(Number(user.bestScore) || 0, score);
  user.gold = Math.max(Number(user.gold) || 0, gold);
  user.coins = user.gold;
  user.kills = Math.max(Number(user.kills) || 0, kills);
  user.rankId = rankInfo(Number(user.xp) || 0).rankId;

  // Davet edilen arkadaşın görev ilerlemesini davet eden kişinin hesabına senkronize et
  if (user.referredBy) {
    const liveSec = Math.floor((Date.now() - (player.stateAt || Date.now())) / 1000);
    updateReferredFriendProgress(user, (Number(player.wood) || 0) + (Number(player.stone) || 0), player.kills || 0, liveSec);
  }

  const current = `${user.score}|${user.gold}|${user.kills}|${user.bestScore}`;
  return previous !== current;
}

function syncAllLivePlayerProgress() {
  let changed = false;
  for (const player of players.values()) changed = syncLivePlayerProgress(player) || changed;
  if (changed) saveAccountData();
}

// Auto-save every 20 seconds and flush on process exit
setInterval(() => {
  syncAllLivePlayerProgress();
  saveAccountData(true);
}, 20000);
process.on('SIGINT', async () => { await saveAccountData(true); process.exit(0); });
process.on('SIGTERM', async () => { await saveAccountData(true); process.exit(0); });

function publicUser(user) {
  const rInfo = rankInfo(user.xp || 0);
  const battlePass = ensureBattlePass(user);
  return {
    id: user.id,
    username: user.username,
    email: user.email || '',
    rankId: rInfo.rankId,
    rankName: rInfo.name,
    rankIcon: rInfo.icon,
    nextRankName: rInfo.rankId < RANKS.length - 1 ? RANK_NAMES[(rInfo.rankId + 1) % RANK_NAMES.length] : null,
    nextRankIcon: rInfo.nextIcon,
    level: rInfo.level,
    score: user.score || 0,
    bestScore: user.bestScore || user.score || 0,
    kills: user.kills || 0,
    deaths: user.deaths || 0,
    games: user.games || user.gamesPlayed || 0,
    gamesPlayed: user.gamesPlayed || user.games || 0,
    timePlayed: user.timePlayed || 0,
    xp: user.xp || 0,
    meleeLevel: Math.max(1, Number(user.meleeLevel) || 1),
    meleeXp: Math.max(0, Number(user.meleeXp) || 0),
    defenceLevel: Math.max(1, Number(user.defenceLevel) || 1),
    defenceXp: Math.max(0, Number(user.defenceXp) || 0),
    xpProgress: rInfo.xpProgress,
    xpToNextRank: rInfo.xpToNextRank,
    ownedItems: ownedItemsForUser(user, user.ownedItems),
    equippedItems: equippedItemsForUser(user, user.equippedItems),
    ownedAxes: normalizeOwnedTiers(user.ownedAxes),
    ownedSwords: normalizeOwnedTiers(user.ownedSwords),
    ownedHelmets: normalizeOwnedItemIds(user.ownedHelmets, /^helmet_[a-z0-9_]{1,48}$/),
    ownedScythes: normalizeOwnedItemIds(user.ownedScythes, /^scythe_tier_[1-8]$/),
    axeTier: Number(user.axeTier) || 0,
    swordTier: Number(user.swordTier) || 0,
    scytheId: user.scytheId || null,
    helmetSkin: user.helmetSkin || null,
    settings: user.settings || {},
    coins: user.coins ?? 0,
    gold: user.coins ?? 0,
    diamonds: Math.max(0, Number(user.diamonds) || 0),
    battlePass,
    questProgress: user.questProgress || {},
    claimedQuests: user.claimedQuests || [],
    ultraQuests: user.ultraQuests || null,
    claimedLevelRewards: user.claimedLevelRewards || [],
    dailyReward: dailyRewardState(user),
    referralCode: user.referralCode || user.username,
    inviteEvent: user.inviteEvent || { claimedMilestones: [false, false, false, false, false], invitedFriends: [] },
    creatorEvent: user.creatorEvent || { submissions: [], claimedTiers: [false, false, false, false], totalViews: 0, isVerifiedCreator: false },
    profileCosmetics: {
      avatarId: equippedItemsForUser(user, user.equippedItems).profil_avatar || 'wolf',
      skinId: equippedItemsForUser(user, user.equippedItems).deriler || 'wolf',
      effectId: user.equippedItems?.profil_efekt || user.equippedItems?.efektler || 'effect_none',
      frameId: user.equippedItems?.profil_cerceve || 'frame_woodland'
    },
    quests: QUESTS_LIST
  };
}

function profileResponse(user) {
  const rank = rankInfo(user.xp || 0);
  const nextRank = rank.rankId < RANKS.length - 1 ? { id: rank.rankId + 1, name: RANK_NAMES[rank.rankId + 1], minXP: rank.nextMinXP } : null;
  return {
    user: publicUser(user),
    rank,
    nextRank,
    level: rank.level,
    xp: user.xp || 0,
    xpProgress: rank.xpProgress,
    xpToNextRank: rank.xpToNextRank,
    currentRankIcon: rank.icon,
    nextRankIcon: rank.nextIcon,
    nextRankName: rank.rankId < RANKS.length - 1 ? RANK_NAMES[(rank.rankId + 1) % RANK_NAMES.length] : null
  };
}

function usernameKey(username) { return String(username || '').trim().toLowerCase(); }
function loginIdentifier(value) {
  return String(value || '').trim().toLocaleLowerCase('tr-TR').replace(/ı/g, 'i').normalize('NFD').replace(/[\u0300-\u036f]/g, '');
}
function findUserForLogin(identifier) {
  const normalized = loginIdentifier(identifier);
  return Object.values(accountData.users).find(user => loginIdentifier(user.username) === normalized || (user.email && loginIdentifier(user.email) === normalized)) || null;
}

function createToken(user) {
  const issuedAt = Date.now();
  const payload = {
    u: user.username,
    id: user.id,
    iat: issuedAt,
    exp: issuedAt + AUTH_TOKEN_TTL_MS
  };
  const encoded = Buffer.from(JSON.stringify(payload), 'utf8').toString('base64url');
  const signature = crypto.createHmac('sha256', authSecret).update(encoded).digest('base64url');
  const token = `${encoded}.${signature}`;
  sessions.set(token, { username: usernameKey(user.username), createdAt: Date.now() });
  return token;
}

function verifyToken(token) {
  if (!token || typeof token !== 'string') return null;
  if (accountData.revokedTokens && accountData.revokedTokens[token]) {
    if (Date.now() < accountData.revokedTokens[token]) return null;
    delete accountData.revokedTokens[token];
  }
  const rawSession = sessions.get(token);
  const directUsername = typeof rawSession === 'object' && rawSession ? rawSession.username : rawSession;
  if (directUsername && accountData.users[directUsername]) {
    const user = accountData.users[directUsername];
    if (user && user.lastLogoutAt && typeof rawSession === 'object' && rawSession?.createdAt && rawSession.createdAt <= user.lastLogoutAt) {
      sessions.delete(token);
      return null;
    }
    return user;
  }
  if (!token.includes('.')) return null;
  const parts = token.split('.');
  if (parts.length !== 2) return null;
  const [encoded, signature] = parts;
  try {
    const expectedSig = crypto.createHmac('sha256', authSecret).update(encoded).digest('base64url');
    if (signature.length !== expectedSig.length || !crypto.timingSafeEqual(Buffer.from(signature), Buffer.from(expectedSig))) {
      return null;
    }
    const decodedStr = Buffer.from(encoded, 'base64url').toString('utf8');
    let username = '';
    let issuedAt = 0;
    if (decodedStr.startsWith('{')) {
      const parsed = JSON.parse(decodedStr);
      issuedAt = Number(parsed.iat) || 0;
      const expiresAt = Number(parsed.exp) || issuedAt + AUTH_TOKEN_TTL_MS;
      if (!issuedAt || Date.now() >= expiresAt || Date.now() - issuedAt > AUTH_TOKEN_TTL_MS) return null;
      username = parsed.u;
    } else {
      return null;
    }
    const key = usernameKey(username);
    const user = accountData.users[key];
    if (user) {
      if (user.lastLogoutAt && issuedAt <= user.lastLogoutAt) {
        return null;
      }
      sessions.set(token, { username: key, createdAt: issuedAt || Date.now() });
      return user;
    }
  } catch (e) {
    return null;
  }
  return null;
}

function getAuthUser(request) {
  const header = request.headers.authorization || '';
  const token = header.startsWith('Bearer ') ? header.slice(7) : (header || '');
  return verifyToken(token);
}

function sendJson(response, status, body) {
  response.writeHead(status, {
    'Content-Type': 'application/json; charset=utf-8',
    'Cache-Control': 'no-store',
    'Access-Control-Allow-Origin': '*',
    'Access-Control-Allow-Headers': 'Content-Type, Authorization'
  });
  response.end(JSON.stringify(body));
}

function readJson(request) {
  return new Promise((resolve, reject) => {
    let body = '';
    const maxBytes = 10 * 1024 * 1024;
    let bodyBytes = 0;
    let tooLarge = false;
    request.on('data', chunk => {
      if (tooLarge) return;
      bodyBytes += chunk.length;
      if (bodyBytes > maxBytes) {
        tooLarge = true;
        body = '';
        reject(new Error('payload too large'));
        return;
      }
      body += chunk;
    });
    request.on('end', () => {
      if (tooLarge) return;
      try { resolve(body ? JSON.parse(body) : {}); } catch { reject(new Error('invalid json')); }
    });
    request.on('error', reject);
  });
}

function recordDeathScore(name, score, gold, kills, timeAlive, userObj, updateUser = true) {
  const cleanName = String(name || 'forestbrawl').trim().slice(0, 20) || 'forestbrawl';
  const numScore = Math.max(0, Number(score) || 0);
  const numGold = Math.max(0, Number(gold) || 0);
  const numKills = Math.max(0, Number(kills) || 0);
  const numTime = Math.max(0, Number(timeAlive) || 0);
  const now = Date.now();

  const user = userObj || null;
  if (user && user.username && updateUser) {
    user.gold = Math.max(user.gold || 0, numGold);
    user.coins = Math.max(user.coins || 0, numGold);
    user.score = numScore;
    user.bestScore = Math.max(user.bestScore || 0, numScore);
    user.kills = (user.kills || 0) + numKills;
    user.deaths = (user.deaths || 0) + 1;
    user.gamesPlayed = (user.gamesPlayed || user.games || 0) + 1;
    user.games = user.gamesPlayed;
    user.timePlayed = (user.timePlayed || 0) + numTime;
    user.lastMatchAt = now;
    const runXp = Math.max(0, Math.round((numKills * 60 + Math.min(numTime * 2, 600) + (numScore > 0 ? Math.floor(Math.sqrt(numScore) * 8) : 0)) * MATCH_XP_RATE));
    user.xp = (user.xp || 0) + runXp;
    user.rankId = rankInfo(user.xp).rankId;
    const battlePass = grantBattlePassMatchXp(user, numKills, numTime, numScore);
    for (const livePlayer of players.values()) {
      if (livePlayer._authUser && usernameKey(livePlayer._authUser.username) === usernameKey(user.username)) {
        io.to(livePlayer.id).emit('battle_pass_update', battlePass);
      }
    }
    if (user.referredBy) {
      updateReferredFriendProgress(user, 0, numKills, numTime);
    }
    saveAccountData(true);
  }

  if (!accountData.leaderboard) accountData.leaderboard = {};
  const leadKey = user ? usernameKey(user.username) : usernameKey(cleanName);
  const prev = accountData.leaderboard[leadKey];
  const userXp = user ? (user.xp || 0) : (prev ? (prev.xp || 0) : 0);
  const rInfo = rankInfo(userXp);

  const highestScore = prev ? Math.max(prev.score || 0, numScore) : numScore;
  const highestGold = prev ? Math.max(prev.gold || 0, numGold) : numGold;
  const highestKills = prev ? Math.max(prev.kills || 0, numKills) : numKills;

  accountData.leaderboard[leadKey] = {
    name: user ? user.username : cleanName,
    xp: userXp,
    score: highestScore,
    gold: highestGold,
    kills: highestKills,
    rankId: rInfo.rankId,
    rankName: rInfo.name,
    lastScore: numScore,
    lastGold: numGold,
    lastKills: numKills,
    lastTimeAlive: numTime,
    lastDate: now,
    lastMatchAt: now,
    profileCosmetics: {
      avatarId: user?.equippedItems?.profil_avatar || 'wolf',
        skinId: user?.equippedItems?.deriler || 'wolf',
      effectId: user?.equippedItems?.profil_efekt || user?.equippedItems?.efektler || 'effect_none',
      frameId: user?.equippedItems?.profil_cerceve || 'frame_woodland'
    },
    isRegistered: !!(user && user.hash)
  };

  if (!Array.isArray(accountData.recentDeaths)) accountData.recentDeaths = [];
  accountData.recentDeaths.unshift({
    name: user ? user.username : cleanName,
    score: numScore,
    gold: numGold,
    kills: numKills,
    rankId: rInfo.rankId,
    rankName: rInfo.name,
    timeAlive: numTime,
    date: now,
    lastMatchAt: now,
    profileCosmetics: {
      avatarId: user?.equippedItems?.profil_avatar || 'wolf',
      skinId: user?.equippedItems?.deriler || 'wolf',
      effectId: user?.equippedItems?.profil_efekt || user?.equippedItems?.efektler || 'effect_none',
      frameId: user?.equippedItems?.profil_cerceve || 'frame_woodland'
    },
    isRegistered: !!(user && user.hash)
  });
  if (accountData.recentDeaths.length > 50) {
    accountData.recentDeaths.length = 50;
  }

  saveAccountData();
}

function persistPlayerScore(player) {
  if (!player || !player.name || player.isBot) return;
  recordDeathScore(player.name, player.score || player.gold, player.gold, player.kills, 0, player._authUser, false);
}

function isBotLeaderboardEntry(entry) {
  if (!entry) return true;
  if (entry.isBot || entry.bot === true) return true;
  const candidate = String(entry.name || '').replace(/^\[[^\]]+\]\s*/, '');
  return BOT_NAMES.includes(candidate);
}

function isBotLeaderboardName(name) {
  if (!name) return false;
  const candidate = String(name).replace(/^\[[^\]]+\]\s*/, '');
  return BOT_NAMES.includes(candidate);
}

function leaderboard(tab) {
  const safeNumber = (value, fallback = 0) => {
    const n = Number(value);
    return Number.isFinite(n) ? n : fallback;
  };

  if (tab === 'recent') {
    return (Array.isArray(accountData.recentDeaths) ? accountData.recentDeaths : []).filter(entry => !isBotLeaderboardEntry(entry)).map(entry => {
      const user = accountData.users?.[usernameKey(entry.name)];
      const currentRank = user ? rankInfo(user.xp || 0) : null;
      const profileCosmetics = user ? {
        avatarId: user.equippedItems?.profil_avatar || 'wolf',
        skinId: user.equippedItems?.deriler || 'wolf',
        effectId: user.equippedItems?.profil_efekt || user.equippedItems?.efektler || 'effect_none',
        frameId: user.equippedItems?.profil_cerceve || 'frame_woodland'
      } : (entry.profileCosmetics || { avatarId: 'wolf', effectId: 'effect_none', frameId: 'frame_woodland' });

      return {
        ...entry,
        xp: safeNumber(user?.xp ?? entry.xp ?? 0),
        rankId: currentRank?.rankId ?? safeNumber(entry.rankId ?? 0),
        rankName: currentRank?.name || entry.rankName || 'Tohum',
        level: currentRank?.level ?? Math.max(1, safeNumber(entry.rankId ?? 0) + 1),
        lastMatchAt: safeNumber(entry.lastMatchAt || entry.date || 0),
        playerKills: safeNumber(entry.playerKills ?? entry.kills ?? 0),
        minutesAgo: entry.date ? Math.max(0, Math.floor((Date.now() - safeNumber(entry.date)) / 60000)) : null,
        profileCosmetics
      };
    }).sort((a, b) => safeNumber(b.lastMatchAt) - safeNumber(a.lastMatchAt)).slice(0, 50).map((entry, index) => ({ ...entry, position: index + 1 }));
  }

  const allMap = new Map();
  // 1. Registered users
  for (const user of Object.values(accountData.users || {})) {
    if (isBotLeaderboardEntry(user)) continue;
    const key = usernameKey(user.username);
    const rInfo = rankInfo(user.xp || 0);
    const savedLeaderboardEntry = accountData.leaderboard?.[key];
    allMap.set(key, {
      name: user.username,
      xp: safeNumber(user.xp || 0),
      score: Math.max(safeNumber(user.bestScore), safeNumber(user.score), safeNumber(user.gold)),
      gold: safeNumber(savedLeaderboardEntry?.gold ?? user.gold ?? user.coins ?? 0),
      kills: safeNumber(user.kills || 0),
      playerKills: safeNumber(user.kills || 0),
      rankId: rInfo.rankId,
      rankName: rInfo.name,
      level: rInfo.level,
      lastDate: safeNumber(user.lastLoginAt || Date.now()),
      lastMatchAt: safeNumber(user.lastMatchAt || user.lastLoginAt || user.createdAt || Date.now()),
      gamesPlayed: safeNumber(user.gamesPlayed || user.games || 0),
      timePlayed: safeNumber(user.timePlayed || 0),
      profileCosmetics: {
        avatarId: user.equippedItems?.profil_avatar || 'wolf',
        skinId: user.equippedItems?.deriler || 'wolf',
        effectId: user.equippedItems?.profil_efekt || user.equippedItems?.efektler || 'effect_none',
        frameId: user.equippedItems?.profil_cerceve || 'frame_woodland'
      },
      isRegistered: true
    });
  }

  // 2. Guest leaderboard records
  for (const [key, entry] of Object.entries(accountData.leaderboard || {})) {
    if (isBotLeaderboardEntry(entry)) continue;
    if (!allMap.has(key)) {
      allMap.set(key, {
        ...entry,
        xp: safeNumber(entry.xp || 0),
        score: safeNumber(entry.score || 0),
        gold: safeNumber(entry.gold || 0),
        kills: safeNumber(entry.kills || 0),
        playerKills: safeNumber(entry.playerKills ?? entry.kills ?? 0),
        lastMatchAt: safeNumber(entry.lastMatchAt || entry.date || 0),
        profileCosmetics: entry.profileCosmetics || { avatarId: 'wolf', effectId: 'effect_none', frameId: 'frame_woodland' }
      });
    } else {
      const existing = allMap.get(key);
      existing.score = Math.max(existing.score, safeNumber(entry.score || 0));
      existing.xp = Math.max(existing.xp || 0, safeNumber(entry.xp || 0));
      existing.gold = Math.max(existing.gold, safeNumber(entry.gold || 0));
      existing.kills = Math.max(existing.kills, safeNumber(entry.kills || 0));
      existing.playerKills = existing.kills;
      existing.lastMatchAt = Math.max(existing.lastMatchAt || 0, safeNumber(entry.lastMatchAt || entry.date || 0));
    }
  }

  const list = [...allMap.values()];
  if (tab === 'kills') list.sort((a, b) => safeNumber(b.playerKills ?? b.kills ?? 0) - safeNumber(a.playerKills ?? a.kills ?? 0));
  else list.sort((a, b) => safeNumber(b.score) - safeNumber(a.score) || safeNumber(b.gold) - safeNumber(a.gold) || safeNumber(b.xp) - safeNumber(a.xp));

  return list.slice(0, 50).map((entry, index) => ({
    ...entry,
    position: index + 1,
    playerKills: safeNumber(entry.playerKills ?? entry.kills ?? 0),
    minutesAgo: safeNumber(entry.lastMatchAt) ? Math.max(0, Math.floor((Date.now() - safeNumber(entry.lastMatchAt)) / 60000)) : null,
  }));
}

async function handleApi(request, response, requestPath) {
  if (request.method === 'OPTIONS') { response.writeHead(204, { 'Access-Control-Allow-Origin': '*', 'Access-Control-Allow-Headers': 'Content-Type, Authorization' }); response.end(); return true; }
  if (!requestPath.startsWith('/api/')) return false;
  if (requestPath === '/api/owner/login' && request.method === 'POST') {
    const ownerCreds = getOwnerCredentials();
    if (authRateLimited(request, 'login')) {
      sendJson(response, 429, { error: 'Çok fazla deneme. Daha sonra tekrar deneyin.' });
      return true;
    }
    let body;
    try { body = await readJson(request); } catch (_) { sendJson(response, 400, { error: 'Geçersiz istek.' }); return true; }
    if (!body || typeof body !== 'object') {
      sendJson(response, 400, { error: 'Geçersiz istek.' });
      return true;
    }
    const incomingUsername = String(body.username || '').trim().toLowerCase();
    const incomingPassword = String(body.password || '').trim();
    const usernameMatches = timingSafeEqualText(incomingUsername, ownerCreds.username);
    const passwordMatches = timingSafeEqualText(incomingPassword, ownerCreds.password);
    if (!usernameMatches || !passwordMatches) {
      ownerAudit('owner_login_failed', { ip: requestClientKey(request), username: incomingUsername });
      console.warn(`[OwnerLogin] denied ip=${requestClientKey(request)} username=${incomingUsername} usernameMatches=${usernameMatches} passwordMatches=${passwordMatches} passwordLength=${incomingPassword.length}`);
      sendJson(response, 401, { error: 'Owner bilgileri geçersiz.' });
      return true;
    }
    const token = ownerTokenFor(ownerCreds.username);
    ownerSessions.set(token, { username: ownerCreds.username, role: 'owner', createdAt: Date.now(), lastSeenAt: Date.now(), expiresAt: Date.now() + ownerSessionTtl });
    ownerAudit('owner_login', { username: ownerCreds.username, ip: requestClientKey(request) });
    sendJson(response, 200, { token, user: { username: ownerCreds.username, role: 'owner', expiresAt: Date.now() + ownerSessionTtl } });
    return true;
  }
  if (requestPath === '/api/owner/logout' && request.method === 'POST') {
    const session = getOwnerSession(request);
    const token = String(request.headers.authorization || '').replace(/^Bearer\s+/, '');
    if (session) ownerAudit('owner_logout', { username: session.username });
    ownerSessions.delete(token);
    sendJson(response, 200, { ok: true });
    return true;
  }
  if (requestPath === '/api/owner/me' && request.method === 'GET') {
    const session = ownerRequired(request, response);
    if (!session) return true;
    sendJson(response, 200, { user: { username: session.username, role: session.role, expiresAt: session.expiresAt } });
    return true;
  }
  if (requestPath === '/api/owner/dashboard' && request.method === 'GET') {
    const session = ownerRequired(request, response);
    if (!session) return true;
    const registeredUsers = Object.values(accountData.users || {});
    const mem = process.memoryUsage();
    sendJson(response, 200, {
      stats: {
        online: players.size,
        buildings: buildings.size,
        mobs: mobs.size,
        registeredUsers: registeredUsers.length,
        clans: clans.size,
        parties: parties.size,
        database: Boolean(sqliteDb),
        maintenance: adminConfig.maintenance,
        pvpEnabled: adminConfig.pvpEnabled,
        uptimeSec: Math.floor(process.uptime()),
        ramMb: Math.round(mem.rss / 1024 / 1024),
        heapMb: Math.round(mem.heapUsed / 1024 / 1024),
        bannedCount: bannedList.size
      },
      players: [...players.values()].map(player => ({
        id: player.id,
        name: player.name || 'Oyuncu',
        hp: Number(player.hp || 0),
        maxHp: Number(player.maxHp || 250),
        score: Number(player.score || 0),
        gold: Number(player.gold || 0),
        xp: Number(player.xp || 0),
        kills: Number(player.kills || 0),
        x: Math.round(Number(player.x || 0)),
        y: Math.round(Number(player.y || 0)),
        skin: player.skin || 'default',
        frozen: Boolean(player._ownerFrozen),
        clanTag: player.clanTag || '',
        team: player.team || ''
      })),
      config: adminConfig,
      audit: ownerAuditLog.slice(0, 50),
      banned: [...bannedList]
    });
    return true;
  }
  if (requestPath === '/api/owner/users' && request.method === 'GET') {
    const session = ownerRequired(request, response);
    if (!session) return true;
    const query = String(new URL(request.url || '/', 'http://localhost').searchParams.get('q') || '').trim().toLowerCase();
    const users = Object.values(accountData.users || {}).filter(user => !query || `${user.username} ${user.email || ''}`.toLowerCase().includes(query)).slice(0, 200).map(user => ({
      id: user.id, username: user.username, email: user.email || '', xp: Number(user.xp || 0), coins: Number(user.coins || user.gold || 0), kills: Number(user.kills || 0), deaths: Number(user.deaths || 0), gamesPlayed: Number(user.gamesPlayed || user.games || 0), ownedItems: Array.isArray(user.ownedItems) ? user.ownedItems.length : 0, lastLoginAt: user.lastLoginAt || null, createdAt: user.createdAt || null
    }));
    sendJson(response, 200, { users });
    return true;
  }
  if (requestPath === '/api/owner/user-edit' && request.method === 'POST') {
    const session = ownerRequired(request, response);
    if (!session) return true;
    let body;
    try { body = await readJson(request); } catch (_) { sendJson(response, 400, { error: 'Geçersiz istek.' }); return true; }
    const targetId = Number(body.userId);
    const targetUsername = String(body.username || '').trim();
    const user = Object.values(accountData.users || {}).find(u => u.id === targetId || usernameKey(u.username) === usernameKey(targetUsername));
    if (!user) { sendJson(response, 404, { error: 'Kullanıcı bulunamadı.' }); return true; }
    if (body.action === 'delete') {
      const uKey = usernameKey(user.username);
      delete accountData.users[uKey];
      saveAccountData(true);
      ownerAudit('user_deleted', { username: session.username, targetUser: user.username });
      sendJson(response, 200, { ok: true, deleted: true });
      return true;
    }
    if (body.coins !== undefined) {
      user.coins = Math.max(0, Math.min(100000000, Number(body.coins) || 0));
      user.gold = user.coins;
    }
    if (body.xp !== undefined) {
      user.xp = Math.max(0, Math.min(100000000, Number(body.xp) || 0));
      user.rankId = rankInfo(user.xp).rankId;
    }
    if (body.password && String(body.password).length >= 4) {
      const passObj = hashPassword(String(body.password));
      user.hash = passObj.hash;
      user.salt = passObj.salt;
    }
    saveAccountData(true);
    ownerAudit('user_updated', { username: session.username, targetUser: user.username, coins: user.coins, xp: user.xp });
    sendJson(response, 200, { ok: true, user: publicUser(user) });
    return true;
  }
  if (requestPath === '/api/owner/ban-list' && request.method === 'GET') {
    const session = ownerRequired(request, response);
    if (!session) return true;
    sendJson(response, 200, { banned: [...bannedList] });
    return true;
  }
  if (requestPath === '/api/owner/ban' && request.method === 'POST') {
    const session = ownerRequired(request, response);
    if (!session) return true;
    let body;
    try { body = await readJson(request); } catch (_) { sendJson(response, 400, { error: 'Geçersiz istek.' }); return true; }
    const target = String(body.target || '').trim();
    if (!target) { sendJson(response, 400, { error: 'Hedef belirtilmedi.' }); return true; }
    if (body.action === 'unban') {
      bannedList.delete(target);
      bannedList.delete(usernameKey(target));
      saveBannedList();
      ownerAudit('unbanned', { username: session.username, target });
      sendJson(response, 200, { ok: true, banned: [...bannedList] });
      return true;
    }
    bannedList.add(target);
    saveBannedList();
    ownerAudit('banned', { username: session.username, target });
    for (const [sId, p] of players) {
      if (p.name && (p.name.toLowerCase() === target.toLowerCase() || usernameKey(p.name) === usernameKey(target))) {
        const s = io.sockets.sockets.get(sId);
        s?.disconnect(true);
      }
    }
    sendJson(response, 200, { ok: true, banned: [...bannedList] });
    return true;
  }
  if (requestPath === '/api/cosmetics/catalog' && request.method === 'GET') {
    sendJson(response, 200, { items: cosmeticCatalog.map(publicCosmetic), rarities: [...COSMETIC_RARITIES], types: [...COSMETIC_TYPES] });
    return true;
  }
  if (requestPath === '/api/owner/cosmetics/upload' && request.method === 'POST') {
    const session = ownerRequired(request, response);
    if (!session) return true;
    let body;
    try { body = await readJson(request); } catch (_) { sendJson(response, 400, { error: 'Geçersiz PNG yükleme isteği.' }); return true; }
    const itemId = String(body.id || '').trim().toLowerCase().replace(/[^a-z0-9_-]/g, '').slice(0, 48);
    const type = String(body.type || 'skin');
    const rarity = String(body.rarity || 'common');
    if (!itemId || type !== 'skin' || !COSMETIC_RARITIES.has(rarity)) {
      sendJson(response, 400, { error: 'PNG yüklemeleri yalnızca deri türünde olmalıdır; ID veya nadirlik geçersiz.' });
      return true;
    }
    const existing = cosmeticCatalog.find(item => item.id === itemId);
    if (!body.assetData && !existing?.asset) {
      sendJson(response, 400, { error: 'PNG dosyası seçilmedi.' });
      return true;
    }
    try {
      const assetInfo = body.assetData ? saveCosmeticPng(itemId, body.assetData, existing?.asset) : { asset: existing.asset, width: existing.width, height: existing.height, orientation: existing.orientation };
      const now = Date.now();
      const item = {
        id: itemId,
        type,
        name: String(body.name || itemId).trim().slice(0, 40),
        rarity,
        color: String(body.color || '#b8f36b').slice(0, 20),
        asset: assetInfo.asset,
        width: assetInfo.width,
        height: assetInfo.height,
        orientation: assetInfo.orientation,
        price: Math.max(0, Math.min(1000000, Math.round(Number(body.price) || 0))),
        chests: Array.isArray(body.chests) ? body.chests.filter(chestId => Object.prototype.hasOwnProperty.call(CHEST_CONFIG, chestId)) : (existing?.chests || []),
        createdAt: existing?.createdAt || now,
        updatedAt: now
      };
      if (existing) cosmeticCatalog[cosmeticCatalog.indexOf(existing)] = item;
      else cosmeticCatalog.push(item);
      saveCosmeticCatalog();
      ownerAudit(existing ? 'cosmetic_updated' : 'cosmetic_created', { username: session.username, itemId, type, rarity, price: item.price, asset: item.asset });
      broadcastCosmeticCatalog(existing ? 'updated' : 'created', item);
      sendJson(response, 200, { ok: true, item: publicCosmetic(item), items: cosmeticCatalog.map(publicCosmetic) });
    } catch (error) {
      sendJson(response, 400, { error: error.message || 'PNG yüklenemedi.' });
    }
    return true;
  }
  if (requestPath === '/api/owner/cosmetics' && (request.method === 'GET' || request.method === 'POST' || request.method === 'DELETE')) {
    const session = ownerRequired(request, response);
    if (!session) return true;
    if (request.method === 'GET') {
      sendJson(response, 200, { items: cosmeticCatalog.map(publicCosmetic), chests: Object.fromEntries(Object.entries(CHEST_CONFIG).map(([id, chest]) => [id, { cost: chest.cost, rewards: [...chest.rewards] }])) });
      return true;
    }
    let body;
    try { body = await readJson(request); } catch (_) { sendJson(response, 400, { error: 'Geçersiz kozmetik isteği.' }); return true; }
    const itemId = String(body.id || '').trim().toLowerCase().replace(/[^a-z0-9_-]/g, '').slice(0, 48);
    if (request.method === 'DELETE') {
      const index = cosmeticCatalog.findIndex(item => item.id === itemId);
      if (index < 0) { sendJson(response, 404, { error: 'Kozmetik bulunamadı.' }); return true; }
      const removed = cosmeticCatalog[index];
      cosmeticCatalog.splice(index, 1);
      for (const chest of Object.values(CHEST_CONFIG)) chest.rewards = chest.rewards.filter(reward => reward !== itemId);
      if (String(removed.asset || '').startsWith('cosmetics/')) {
        const assetPath = path.resolve(root, removed.asset);
        if (assetPath.startsWith(`${COSMETIC_ASSET_DIR}${path.sep}`)) fs.rmSync(assetPath, { force: true });
      }
      saveCosmeticCatalog();
      ownerAudit('cosmetic_deleted', { username: session.username, itemId });
      broadcastCosmeticCatalog('deleted', removed);
      sendJson(response, 200, { ok: true });
      return true;
    }
    if (!itemId || !COSMETIC_TYPES.has(body.type) || !COSMETIC_RARITIES.has(body.rarity)) { sendJson(response, 400, { error: 'ID, tür veya rarity geçersiz.' }); return true; }
    const item = { id: itemId, type: body.type, name: String(body.name || itemId).trim().slice(0, 40), rarity: body.rarity, color: String(body.color || '#b8f36b').slice(0, 20), asset: String(body.asset || `players/${itemId}.png`).trim().slice(0, 160), price: Math.max(0, Math.min(1000000, Number(body.price) || 0)), chests: Array.isArray(body.chests) ? body.chests.filter(chestId => Object.prototype.hasOwnProperty.call(CHEST_CONFIG, chestId)) : [], createdAt: Date.now() };
    const existing = cosmeticCatalog.findIndex(entry => entry.id === itemId);
    const nextItem = { ...item, createdAt: existing >= 0 && cosmeticCatalog[existing]?.createdAt ? cosmeticCatalog[existing].createdAt : Date.now(), updatedAt: Date.now() };
    if (existing >= 0) cosmeticCatalog[existing] = nextItem;
    else cosmeticCatalog.push(nextItem);
    for (const [chestId, chest] of Object.entries(CHEST_CONFIG)) chest.rewards = chest.rewards.filter(reward => reward !== itemId);
    for (const chestId of nextItem.chests) if (!CHEST_CONFIG[chestId].rewards.includes(itemId)) CHEST_CONFIG[chestId].rewards.push(itemId);
    saveCosmeticCatalog();
    ownerAudit(existing >= 0 ? 'cosmetic_updated' : 'cosmetic_created', { username: session.username, itemId, type: nextItem.type, rarity: nextItem.rarity, price: nextItem.price });
    broadcastCosmeticCatalog(existing >= 0 ? 'updated' : 'created', nextItem);
    sendJson(response, 200, { ok: true, item: publicCosmetic(nextItem), items: cosmeticCatalog.map(publicCosmetic) });
    return true;
  }
  if (requestPath === '/api/owner/config' && (request.method === 'GET' || request.method === 'POST')) {
    const session = ownerRequired(request, response);
    if (!session) return true;
    if (request.method === 'POST') {
      let body;
      try { body = await readJson(request); } catch (_) { sendJson(response, 400, { error: 'Geçersiz ayar isteği.' }); return true; }
      const allowed = ['maintenance', 'pvpEnabled', 'xpRate', 'mobSpawnMultiplier', 'resourceRespawnMultiplier', 'mainMenuLayout'];
      const previous = { ...adminConfig };
      for (const key of allowed) {
        if (body[key] === undefined) continue;
        if (key === 'mainMenuLayout') {
          adminConfig[key] = normalizeMainMenuLayout(body[key]);
          continue;
        }
        if (typeof adminConfig[key] === 'boolean') adminConfig[key] = Boolean(body[key]);
        else adminConfig[key] = Math.max(0.1, Math.min(20, Number(body[key]) || 1));
      }
      ownerAudit('config_updated', { username: session.username, previous, next: { ...adminConfig } });
      saveAdminConfig();
      io.emit('owner_config_updated', { pvpEnabled: adminConfig.pvpEnabled, maintenance: adminConfig.maintenance, mainMenuLayout: adminConfig.mainMenuLayout });
    }
    sendJson(response, 200, { config: adminConfig });
    return true;
  }
  if (requestPath === '/api/public/config' && request.method === 'GET') {
    sendJson(response, 200, {
      config: {
        mainMenuLayout: adminConfig.mainMenuLayout,
        maintenance: adminConfig.maintenance,
        pvpEnabled: adminConfig.pvpEnabled,
        announcement: adminConfig.announcement || ''
      }
    });
    return true;
  }
  if (requestPath === '/api/owner/announce' && request.method === 'POST') {
    const session = ownerRequired(request, response);
    if (!session) return true;
    let body;
    try { body = await readJson(request); } catch (_) { sendJson(response, 400, { error: 'Geçersiz duyuru.' }); return true; }
    if (body.clear) {
      adminConfig.announcement = '';
      saveAdminConfig();
      ownerAudit('announcement_cleared', { username: session.username });
      io.emit('server_announce_clear', {});
      sendJson(response, 200, { ok: true, cleared: true });
      return true;
    }
    const message = String(body.message || '').trim().slice(0, 300);
    if (!message) { sendJson(response, 400, { error: 'Duyuru boş olamaz.' }); return true; }
    const title = String(body.title || 'FORESTBRAWL DUYURUSU').trim().slice(0, 60);
    const level = ['info', 'warning', 'event', 'reward'].includes(body.level) ? body.level : 'info';
    const sound = ['bell', 'horn', 'fanfare', 'siren', 'none'].includes(body.sound) ? body.sound : 'bell';
    const durationMs = Math.max(500, Math.min(3000, Number(body.durationMs ?? 3000)));
    adminConfig.announcement = message;
    saveAdminConfig();
    ownerAudit('announcement_sent', { username: session.username, message, title, level, sound, durationMs });
    io.emit('server_announce', {
      message,
      msg: message,
      text: message,
      title,
      level,
      sound,
      durationMs,
      from: session.username.toUpperCase(),
      at: Date.now()
    });
    sendJson(response, 200, { ok: true, message, title, level, durationMs });
    return true;
  }
  if (requestPath === '/api/owner/player-action' && request.method === 'POST') {
    const session = ownerRequired(request, response);
    if (!session) return true;
    let body;
    try { body = await readJson(request); } catch (_) { sendJson(response, 400, { error: 'Geçersiz oyuncu işlemi.' }); return true; }
    const playerId = String(body.playerId || '');
    const player = players.get(playerId);
    const action = String(body.action || '');
    if (!player || !['kick', 'freeze', 'unfreeze', 'heal', 'kill', 'give_gold', 'give_xp', 'teleport', 'damage', 'ban'].includes(action)) { sendJson(response, 404, { error: 'Oyuncu veya işlem bulunamadı.' }); return true; }
    const targetSocket = io.sockets.sockets.get(playerId);
    if (action === 'kick') targetSocket?.disconnect(true);
    if (action === 'freeze') { player._ownerFrozen = true; player.vx = 0; player.vy = 0; }
    if (action === 'unfreeze') player._ownerFrozen = false;
    if (action === 'heal') { player.hp = player.maxHp || 250; targetSocket?.emit('self_state', { hp: player.hp, hpSeq: player.hpSeq || 0, hpAt: Date.now() }); }
    if (action === 'kill') { player.hp = 0; onPlayerDeath(playerId); targetSocket?.emit('player_take_damage', { id: playerId, hp: 0, dmg: player.maxHp || 250, sourceName: 'Owner' }); }
    if (action === 'damage') {
      const dmg = Math.max(1, Math.min(player.hp || 250, Number(body.amount) || 50));
      player.hp = Math.max(0, (player.hp || 250) - dmg);
      targetSocket?.emit('player_take_damage', { id: playerId, hp: player.hp, dmg, sourceName: 'Owner' });
      if (player.hp <= 0) onPlayerDeath(playerId);
    }
    if (action === 'give_gold') {
      const amount = Math.max(1, Math.min(1000000, Number(body.amount) || 1000));
      player.gold = (player.gold || 0) + amount;
      if (player._authUser) { player._authUser.coins = (player._authUser.coins || 0) + amount; player._authUser.gold = player._authUser.coins; saveAccountData(true); }
      targetSocket?.emit('self_state', { g: player.gold, sc: player.score });
      targetSocket?.emit('server_announce', { message: `🎁 Kurucu sana +${amount.toLocaleString('tr-TR')} Altın verdi!`, msg: `🎁 Kurucu sana +${amount.toLocaleString('tr-TR')} Altın verdi!`, text: `🎁 Kurucu sana +${amount.toLocaleString('tr-TR')} Altın verdi!`, level: 'reward', title: 'KURUCU ÖDÜLÜ' });
    }
    if (action === 'give_xp') {
      const amount = Math.max(1, Math.min(1000000, Number(body.amount) || 1000));
      player.xp = (player.xp || 0) + amount;
      if (player._authUser) { player._authUser.xp = (player._authUser.xp || 0) + amount; player._authUser.rankId = rankInfo(player._authUser.xp).rankId; saveAccountData(true); }
      targetSocket?.emit('self_state', { xp: player.xp });
      targetSocket?.emit('server_announce', { message: `⭐ Kurucu sana +${amount.toLocaleString('tr-TR')} XP verdi!`, msg: `⭐ Kurucu sana +${amount.toLocaleString('tr-TR')} XP verdi!`, text: `⭐ Kurucu sana +${amount.toLocaleString('tr-TR')} XP verdi!`, level: 'reward', title: 'KURUCU ÖDÜLÜ' });
    }
    if (action === 'teleport') {
      const targetX = Math.max(-7000, Math.min(7000, Number(body.x) || 0));
      const targetY = Math.max(-7000, Math.min(7000, Number(body.y) || 0));
      player.x = targetX;
      player.y = targetY;
      player.teleportSeq = (player.teleportSeq || 0) + 1;
      player.vx = 0;
      player.vy = 0;
      targetSocket?.emit('pos_correction', { x: targetX, y: targetY });
      targetSocket?.emit('self_state', { x: targetX, y: targetY });
    }
    if (action === 'ban') {
      const clientIp = requestClientKey(targetSocket?.request || { headers: {}, socket: targetSocket?.conn?.transport?.socket });
      bannedList.add(playerId);
      if (player.name) bannedList.add(usernameKey(player.name));
      if (clientIp && clientIp !== 'unknown') bannedList.add(clientIp);
      saveBannedList();
      targetSocket?.emit('server_announce', { message: 'Sunucudan yasaklandınız (Banned).', msg: 'Sunucudan yasaklandınız (Banned).', text: 'Sunucudan yasaklandınız (Banned).', level: 'warning', title: 'YASAKLANDINIZ' });
      targetSocket?.disconnect(true);
    }
    ownerAudit('player_action', { username: session.username, playerId, playerName: player.name, action, amount: body.amount });
    sendJson(response, 200, { ok: true, action, playerId });
    return true;
  }
  if (requestPath === '/api/owner/creator-events' && request.method === 'GET') {
    const session = ownerRequired(request, response);
    if (!session) return true;
    const allEvents = [];
    for (const [unameKey, u] of Object.entries(accountData.users)) {
      if (u.creatorEvent?.submissions?.length) {
        for (const sub of u.creatorEvent.submissions) {
          allEvents.push({
            username: u.username,
            ...sub
          });
        }
      }
    }
    allEvents.sort((a, b) => (b.submittedAt || 0) - (a.submittedAt || 0));
    sendJson(response, 200, { ok: true, submissions: allEvents });
    return true;
  }
  if (requestPath === '/api/owner/creator-event/review' && request.method === 'POST') {
    const session = ownerRequired(request, response);
    if (!session) return true;
    let reviewBody;
    try { reviewBody = await readJson(request); } catch (_) { sendJson(response, 400, { error: 'Geçersiz veri.' }); return true; }
    const targetUsername = String(reviewBody.username || '').trim();
    const submissionId = String(reviewBody.submissionId || '').trim();
    const status = String(reviewBody.status || '').trim().toLowerCase();
    const views = Math.max(100, Number(reviewBody.views) || 50000);
    if (!['approved', 'rejected'].includes(status)) {
      sendJson(response, 400, { error: 'Durum "approved" veya "rejected" olmalıdır.' });
      return true;
    }
    const targetUser = accountData.users[usernameKey(targetUsername)];
    if (!targetUser || !targetUser.creatorEvent?.submissions) {
      sendJson(response, 404, { error: 'Kullanıcı veya başvuru bulunamadı.' });
      return true;
    }
    const sub = targetUser.creatorEvent.submissions.find(s => s.id === submissionId);
    if (!sub) {
      sendJson(response, 404, { error: 'Başvuru bulunamadı.' });
      return true;
    }
    sub.status = status;
    if (status === 'approved') {
      sub.approvedAt = Date.now();
      sub.estimatedViews = views;
    } else {
      sub.rejectedAt = Date.now();
    }
    targetUser.creatorEvent.totalViews = (targetUser.creatorEvent.submissions || []).reduce((sum, s) => sum + (s.status === 'approved' ? (s.estimatedViews || 0) : 0), 0);
    saveAccountData(true);
    ownerAudit('creator_review', { username: session.username, targetUser: targetUser.username, submissionId, status, views });
    for (const p of players.values()) {
      if (p._authUser && usernameKey(p._authUser.username) === usernameKey(targetUser.username)) {
        const s = io.sockets.sockets.get(p.id);
        if (s?.connected) {
          s.emit('creator_status_update', { submissionId, status, estimatedViews: sub.estimatedViews });
          s.emit('server_announce', {
            message: status === 'approved' ? `🎬 Tebrikler! Video başvurunuz onaylandı (${sub.estimatedViews.toLocaleString('tr-TR')} izlenme)!` : '⚠️ Video başvurunuz incelendi ve reddedildi.',
            level: status === 'approved' ? 'reward' : 'warning',
            title: 'İÇERİK ÜRETİCİ'
          });
        }
      }
    }
    sendJson(response, 200, { ok: true, submission: sub, totalViews: targetUser.creatorEvent.totalViews });
    return true;
  }
  if (requestPath === '/api/health' && request.method === 'GET') {
    const databaseOk = Boolean(sqliteDb) && !databaseLastError;
    sendJson(response, databaseOk ? 200 : 503, { ok: databaseOk, database: Boolean(sqliteDb), online: io.engine.clientsCount });
    return true;
  }

  let body = {};
  if (request.method !== 'GET') {
    try {
      body = await readJson(request);
    } catch (error) {
      const status = error.message === 'payload too large' ? 413 : 400;
      sendJson(response, status, { error: status === 413 ? 'İstek gövdesi çok büyük.' : 'Geçersiz istek.' });
      return true;
    }
  }

  if (requestPath === '/api/auth/register' && request.method === 'POST') {
    if (authRateLimited(request, 'register')) { response.writeHead(429, { 'Content-Type': 'application/json; charset=utf-8', 'Retry-After': '3600' }); response.end(JSON.stringify({ error: 'Çok fazla kayıt denemesi. Lütfen daha sonra tekrar deneyin.' })); return true; }
    const username = String(body.username || '').trim();
    const key = usernameKey(username);
    const email = String(body.email || '').trim().toLowerCase();
    if (!/^[a-zA-Z0-9_ TürkÇĞİÖŞÜçğıöşü-]{3,20}$/.test(username)) { sendJson(response, 400, { error: 'Kullanıcı adı 3-20 karakter olmalı.' }); return true; }
    if (!body.password || String(body.password).length < 4) { sendJson(response, 400, { error: 'Şifre en az 4 karakter olmalı.' }); return true; }
    if (!/^[^\s@]+@[^\s@]+\.[^\s@]+$/.test(email)) { sendJson(response, 400, { error: 'Geçerli bir e-posta adresi gerekli.' }); return true; }
    if (accountData.users[key]) { sendJson(response, 409, { error: 'Bu kullanıcı adı zaten kayıtlı.' }); return true; }
    if (Object.values(accountData.users).some(user => String(user.email || '').trim().toLowerCase() === email)) { sendJson(response, 409, { error: 'Bu e-posta zaten kayıtlı.' }); return true; }
    const password = hashPassword(String(body.password));
    // Referans davet kodu kontrolü
    const referralCode = String(body.referralCode || body.ref || '').trim();
    let inviter = null;
    if (referralCode) {
      const refKey = usernameKey(referralCode);
      inviter = Object.values(accountData.users || {}).find(u =>
        u && (
          usernameKey(u.username) === refKey ||
          usernameKey(u.referralCode || '') === refKey ||
          String(u.id) === referralCode
        )
      );
    }

    // Davet koduyla katılan kullanıcıya başlangıçta +300 bonus altın verilir
    const initCoins = inviter ? 300 : 0;
    const user = {
      id: accountData.nextId++,
      username,
      email,
      ...password,
      rankId: rankInfo(0).rankId,
      xp: 0,
      score: 0,
      kills: 0,
      deaths: 0,
      games: 0,
      gamesPlayed: 0,
      bestScore: 0,
      timePlayed: 0,
      coins: initCoins,
      gold: initCoins,
      diamonds: 0,
      ownedItems: [],
      equippedItems: {},
      dailyReward: { day: 1, claimedDate: '' },
      claimedLevelRewards: [],
      settings: (body.initialSettings && typeof body.initialSettings === 'object') ? { ...body.initialSettings } : {},
      referralCode: username,
      referredBy: inviter ? inviter.id : null,
      inviteEvent: {
        claimedMilestones: [false, false, false, false, false],
        invitedFriends: []
      },
      createdAt: Date.now(),
      lastLoginAt: Date.now(),
      lastMatchAt: Date.now()
    };
    accountData.users[key] = user;

    // Davet eden kişinin hesabına bu arkadaşı görev takip kartı olarak ekle
    if (inviter) {
      if (!inviter.inviteEvent) {
        inviter.inviteEvent = { claimedMilestones: [false, false, false, false, false], invitedFriends: [] };
      }
      if (!Array.isArray(inviter.inviteEvent.invitedFriends)) inviter.inviteEvent.invitedFriends = [];
      if (!inviter.inviteEvent.invitedFriends.some(f => f.id === user.id || f.username === user.username)) {
        inviter.inviteEvent.invitedFriends.push({
          id: user.id,
          username: user.username,
          joinedAt: Date.now(),
          tasks: {
            level: { name: "Seviye 3'e Ulaş", current: rankInfo(0).level, target: 3, done: rankInfo(0).level >= 3 },
            resources: { name: "500 Kaynak Topla", current: 0, target: 500, done: false },
            kills: { name: "1 Rakip Alt Et", current: 0, target: 1, done: false },
            survival: { name: "3 Dk Hayatta Kal", current: 0, target: 3, done: false }
          },
          completed: false
        });
      }
    }

    saveAccountData(true);
    sendJson(response, 201, { token: createToken(user), user: publicUser(user) });
    return true;
  }
  if (requestPath === '/api/auth/login' && request.method === 'POST') {
    if (authRateLimited(request, 'login')) { response.writeHead(429, { 'Content-Type': 'application/json; charset=utf-8', 'Retry-After': '600' }); response.end(JSON.stringify({ error: 'Çok fazla giriş denemesi. Lütfen 10 dakika sonra tekrar deneyin.' })); return true; }
    const user = findUserForLogin(body.identifier || body.username);
    const password = String(body.password || '');
    const check = user && user.hash && user.salt && hashPassword(password, user.salt).hash;
    const bufA = check ? Buffer.from(check, 'hex') : null;
    const bufB = (user && user.hash) ? Buffer.from(user.hash, 'hex') : null;
    const isValid = bufA && bufB && bufA.length === bufB.length && crypto.timingSafeEqual(bufA, bufB);
    if (!user || !isValid) {
      sendJson(response, 401, { error: 'Kullanıcı adı veya şifre hatalı.' });
      return true;
    }
    user.lastLoginAt = Date.now();
    saveAccountData();
    sendJson(response, 200, { token: createToken(user), user: publicUser(user) });
    return true;
  }
  if (requestPath === '/api/auth/me' && request.method === 'GET') {
    const user = getAuthUser(request);
    if (!user) sendJson(response, 401, { error: 'Oturum geçersiz.' });
    else sendJson(response, 200, { user: publicUser(user) });
    return true;
  }
  if (requestPath === '/api/auth/logout' && request.method === 'POST') {
    const token = String(request.headers.authorization || '').replace(/^Bearer\s+/, '').trim();
    if (token) {
      accountData.revokedTokens = accountData.revokedTokens || {};
      accountData.revokedTokens[token] = Date.now() + AUTH_TOKEN_TTL_MS;
      const user = getAuthUser(request);
      if (user) {
        user.lastLogoutAt = Date.now();
      }
      sessions.delete(token);
      saveAccountData(true);
    }
    sendJson(response, 200, { ok: true });
    return true;
  }
  
  if (requestPath === '/api/leaderboard' && request.method === 'GET') {
    const tab = new URL(request.url, 'http://localhost').searchParams.get('tab') || 'all';
    sendJson(response, 200, {
      entries: leaderboard(tab),
      recent: leaderboard('recent'),
      top: leaderboard('all')
    });
    return true;
  }
  
  if (requestPath === '/api/leaderboard/submit' && request.method === 'POST') {
    const authUser = getAuthUser(request);
    if (!authUser) {
      sendJson(response, 401, { error: 'Leaderboard sonucu server tarafından oluşturulmalıdır.' });
      return true;
    }
    sendJson(response, 200, { ok: true, user: publicUser(authUser) });
    return true;
  }

  const user = getAuthUser(request);
  if (requestPath === '/api/profile' && request.method === 'GET') {
    if (!user) {
      sendJson(response, 401, { error: 'Oturum gerekli.' });
    } else {
      sendJson(response, 200, profileResponse(user));
    }
    return true;
  }
  if (requestPath === '/api/profile/state' && request.method === 'POST') {
    if (!user) {
      sendJson(response, 401, { error: 'Oturum gerekli.' });
      return true;
    }
    if (authRateLimited(request, 'profile_state')) {
      sendJson(response, 429, { error: 'Profil güncelleme limiti aşıldı.' });
      return true;
    }
    if (body.settings && typeof body.settings === 'object') {
      user.settings = { ...(user.settings || {}) };
      for (const [key, value] of Object.entries(body.settings).slice(0, 50)) {
        if (/^[a-zA-Z0-9_-]{1,64}$/.test(key) && (typeof value === 'boolean' || typeof value === 'number' || typeof value === 'string')) {
          user.settings[key] = value;
        }
      }
    }
    if (body.equippedItems && typeof body.equippedItems === 'object') user.equippedItems = equippedItemsForUser(user, { ...(user.equippedItems || {}), ...body.equippedItems });
    saveAccountData(true);
    sendJson(response, 200, { ok: true, user: publicUser(user) });
    return true;
  }
  if (requestPath === '/api/profile/xp' && request.method === 'POST') {
    if (!user) {
      const gainedXp = Math.max(0, Math.min(600, Math.round(clampNumber(body.xp, 0, 0, 6000) * MATCH_XP_RATE)));
      const startXP = Math.max(0, Number(body.startXP) || 0);
      const startRank = rankInfo(startXP);
      sendJson(response, 200, {
        ok: true, isGuest: true, gainedXp, coinsEarned: 0,
        currentLevel: startRank.level, startXP, gainedXP: gainedXp,
        maxXPForCurrentLevel: Math.max(0, startRank.nextMinXP - startRank.minXP),
      });
      return true;
    }
    if (authRateLimited(request, 'profile_xp')) {
      sendJson(response, 429, { error: 'Maç sonucu gönderme limiti aşıldı.' });
      return true;
    }
    const startXP = Math.max(0, Number(user.xp) || 0);
    const previousRank = rankInfo(user.xp || 0).rankId;
    const currentRank = rankInfo(user.xp);

    sendJson(response, 200, {
      ...profileResponse(user),
      newXp: user.xp,
      xpGained: 0,
      rankUp: currentRank.rankId > previousRank,
      newRankName: currentRank.name,
      newRankIcon: currentRank.icon,
      currentLevel: previousRank + 1,
      startXP,
      gainedXP: 0,
      maxXPForCurrentLevel: Math.max(0, rankInfo(startXP).nextMinXP - rankInfo(startXP).minXP),
    });
    return true;
  }
  if (requestPath === '/api/battle-pass/state' && request.method === 'GET') {
    if (!user) {
      sendJson(response, 401, { error: 'Battle Pass ilerlemesini kaydetmek için giriş yapmalısınız.' });
      return true;
    }
    const state = ensureBattlePass(user);
    saveAccountData();
    sendJson(response, 200, {
      ok: true,
      season: state.season,
      xp: state.xp,
      maxXp: BATTLE_PASS_MAX_XP,
      claimedTiers: state.claimedTiers,
      tiers: BATTLE_PASS_TIERS.map(tier => ({ ...tier, claimed: state.claimedTiers.includes(tier.tier) })),
      user: publicUser(user)
    });
    return true;
  }
  if (requestPath === '/api/battle-pass/claim' && request.method === 'POST') {
    if (authRateLimited(request, 'battle_pass_claim')) {
      sendJson(response, 429, { error: 'Çok fazla istek. Lütfen biraz bekleyin.' });
      return true;
    }
    if (!user) {
      sendJson(response, 401, { error: 'Battle Pass ödülü için giriş yapmalısınız.' });
      return true;
    }
    const lockKey = `battle-pass:${usernameKey(user.username)}`;
    if (claimLocks.has(lockKey)) {
      sendJson(response, 409, { error: 'İşlem devam ediyor, lütfen bekleyin.' });
      return true;
    }
    claimLocks.add(lockKey);
    try {
      const state = ensureBattlePass(user);
      const tierNumber = Number(body.tier);
      const requestedSeason = Number(body.season);
      if (!Number.isInteger(tierNumber) || !Number.isInteger(requestedSeason)) {
        sendJson(response, 400, { error: 'Geçersiz Battle Pass ödül isteği.' });
        return true;
      }
      if (requestedSeason !== state.season) {
        sendJson(response, 409, { error: 'Sezon değişti. Battle Pass yenilendi.', season: state.season, xp: state.xp, claimedTiers: state.claimedTiers });
        return true;
      }
      const tier = BATTLE_PASS_TIERS.find(item => item.tier === tierNumber);
      if (!tier) {
        sendJson(response, 400, { error: 'Geçersiz Battle Pass seviyesi.' });
        return true;
      }
      if (state.claimedTiers.includes(tierNumber)) {
        sendJson(response, 409, { error: 'Bu Battle Pass ödülü zaten alındı.', tier: tierNumber, user: publicUser(user) });
        return true;
      }
      if (state.xp < tier.xp) {
        sendJson(response, 400, { error: 'Bu Battle Pass ödülü henüz açılmadı.', tier: tierNumber, user: publicUser(user) });
        return true;
      }
      if ((tier.type === 'coins' && (Number(user.coins) || 0) >= MAX_ACCOUNT_COINS) ||
          (tier.type === 'accountXp' && (Number(user.xp) || 0) >= MAX_ACCOUNT_XP)) {
        sendJson(response, 409, { error: 'Hesap bakiyesi bu ödülü alabilmek için üst sınıra ulaştı.' });
        return true;
      }

      state.claimedTiers.push(tierNumber);
      let granted = tier.value;
      if (tier.type === 'coins') {
        const updatedCoins = Math.min(MAX_ACCOUNT_COINS, (Number(user.coins) || 0) + tier.value);
        granted = updatedCoins - (Number(user.coins) || 0);
        user.coins = updatedCoins;
        user.gold = updatedCoins;
      } else {
        const updatedXp = Math.min(MAX_ACCOUNT_XP, (Number(user.xp) || 0) + tier.value);
        granted = updatedXp - (Number(user.xp) || 0);
        user.xp = updatedXp;
        user.rankId = rankInfo(updatedXp).rankId;
        for (const livePlayer of players.values()) {
          if (livePlayer._authUser && usernameKey(livePlayer._authUser.username) === usernameKey(user.username)) {
            livePlayer.xp = updatedXp;
            io.to(livePlayer.id).emit('self_state', { xp: updatedXp });
          }
        }
      }
      saveAccountData(true);
      sendJson(response, 200, {
        ok: true,
        tier: tierNumber,
        reward: { type: tier.type, amount: granted, label: tier.label },
        season: state.season,
        xp: state.xp,
        claimedTiers: state.claimedTiers,
        user: publicUser(user)
      });
      return true;
    } finally {
      claimLocks.delete(lockKey);
    }
  }
  if (requestPath === '/api/quests/list' && request.method === 'GET') {
    if (user) {
      user.questProgress = { ...(user.questProgress || {}) };
      const daily = ensureDailyQuests(user, usernameKey(user.username));
      const ultra = ensureUltraQuests(user);
      syncQuestProgressToTasks(user, daily, ultra);
      saveAccountData();
      sendJson(response, 200, { dayKey: daily.dayKey, expiresAt: daily.expiresAt, serverNow: Date.now(), quests: daily.tasks, ultraQuests: ultra.tasks, user: publicUser(user) });
      return true;
    }
    const daily = buildDailyQuestSnapshot(`guest:${requestClientKey(request)}`);
    const ultra = { tasks: ULTRA_QUESTS.map(quest => ({ ...quest, progress: 0, claimed: false })) };
    sendJson(response, 200, { dayKey: daily.dayKey, expiresAt: daily.expiresAt, serverNow: Date.now(), quests: daily.tasks, ultraQuests: ultra.tasks, user: null, guestLocalOnly: true });
    return true;
  }
  if (requestPath === '/api/quests/claim' && request.method === 'POST') {
    if (authRateLimited(request, 'quests_claim')) {
      sendJson(response, 429, { error: 'Çok fazla istek. Lütfen biraz bekleyin.' });
      return true;
    }
    const lockKey = `quests:${user ? user.username : requestClientKey(request)}`;
    if (claimLocks.has(lockKey)) {
      sendJson(response, 409, { error: 'İşlem devam ediyor, lütfen bekleyin.' });
      return true;
    }
    claimLocks.add(lockKey);
    try {
      const questId = String(body.questId || '');
      const questType = body.questType === 'ultra' ? 'ultra' : 'daily';

      if (user) {
        const daily = ensureDailyQuests(user, usernameKey(user.username));
        const ultra = ensureUltraQuests(user);
        const quest = (questType === 'ultra' ? ultra.tasks : daily.tasks).find(q => q.id === questId);
        if (!quest) {
          sendJson(response, 400, { error: 'Geçersiz görev.' });
          return true;
        }
        if (quest.claimed) {
          sendJson(response, 400, { error: 'Bu ödül zaten alınmış.' });
          return true;
        }
        const currentProg = Number(quest.progress || 0);
        if (currentProg < quest.target) {
          sendJson(response, 400, { error: 'Görev henüz tamamlanmadı.' });
          return true;
        }
        quest.claimed = true;
        const earnedQuestXp = Math.max(1, Math.round(Number(quest.rewardXp || 0) * QUEST_XP_RATE));
        const rewardCoins = Math.max(1, Math.round(Number(quest.rewardCoins || 0) * 1.35));
        user.xp = Math.min(MAX_ACCOUNT_XP, (user.xp || 0) + earnedQuestXp);
        user.coins = Math.min(MAX_ACCOUNT_COINS, (user.coins || 0) + rewardCoins);
        user.gold = user.coins;
        user.rankId = rankInfo(user.xp).rankId;
        for (const livePlayer of players.values()) {
          if (livePlayer._authUser && usernameKey(livePlayer._authUser.username) === usernameKey(user.username)) {
            livePlayer.xp = user.xp;
            io.to(livePlayer.id).emit('self_state', { xp: livePlayer.xp });
          }
        }
        saveAccountData(true);
        sendJson(response, 200, {
          ok: true,
          message: `${quest.title} tamamlandı! +${rewardCoins} Altın ve +${earnedQuestXp} XP kazandınız!`,
          claimedQuestId: questId,
          rewardCoins,
          rewardXp: earnedQuestXp,
          dailyQuests: daily,
          ultraQuests: ultra,
          user: publicUser(user)
        });
        return true;
      } else {
        sendJson(response, 401, {
          error: 'Görev ödüllerini sunucuya kaydetmek için bir hesaba giriş yapmalısınız.'
        });
        return true;
      }
    } finally {
      claimLocks.delete(lockKey);
    }
  }
  if (requestPath === '/api/profile/level-reward' && request.method === 'POST') {
    if (authRateLimited(request, 'level_reward')) {
      sendJson(response, 429, { error: 'Çok fazla istek. Lütfen biraz bekleyin.' });
      return true;
    }
    if (!user) {
      sendJson(response, 401, { error: 'Seviye ödülü için giriş yapmalısınız.' });
      return true;
    }
    const lockKey = `level:${user.username}`;
    if (claimLocks.has(lockKey)) {
      sendJson(response, 409, { error: 'İşlem devam ediyor, lütfen bekleyin.' });
      return true;
    }
    claimLocks.add(lockKey);
    try {
      const level = Math.floor(Number(body.level));
      if (!Number.isInteger(level) || level < 1 || level > RANKS.length) {
        sendJson(response, 400, { error: 'Geçersiz seviye.' });
        return true;
      }
      if ((user.xp || 0) < RANKS[level - 1]) {
        sendJson(response, 400, { error: 'Bu seviye henüz açılmadı.' });
        return true;
      }
      const claimed = Array.isArray(user.claimedLevelRewards) ? user.claimedLevelRewards : [];
      if (claimed.includes(level)) {
        sendJson(response, 409, { error: 'Bu seviye ödülü zaten alındı.', level, user: publicUser(user) });
        return true;
      }
      const rewardCoins = LEVEL_REWARD_BASE_COINS + (level - 1) * LEVEL_REWARD_STEP_COINS;
      user.claimedLevelRewards = [...new Set([...claimed, level])].sort((a, b) => a - b);
      user.coins = (user.coins || 0) + rewardCoins;
      user.gold = user.coins;
      saveAccountData(true);
      sendJson(response, 200, { ok: true, level, rewardCoins, coins: user.coins, user: publicUser(user) });
      return true;
    } finally {
      claimLocks.delete(lockKey);
    }
  }
  if (requestPath === '/api/daily-reward' && request.method === 'GET') {
    if (!user) {
      sendJson(response, 401, { error: 'Günlük ödül için giriş yapmalısınız.' });
      return true;
    }
    const state = dailyRewardState(user);
    user.dailyReward = state;
    const today = dailyQuestDayKey();
    saveAccountData(true);
    sendJson(response, 200, {
      day: state.day,
      claimedDate: state.claimedDate,
      claimedToday: state.claimedDate === today,
      today,
      rewards: DAILY_REWARDS
    });
    return true;
  }
  if (requestPath === '/api/daily-reward/claim' && request.method === 'POST') {
    if (authRateLimited(request, 'daily_reward_claim')) {
      sendJson(response, 429, { error: 'Çok fazla istek. Lütfen biraz bekleyin.' });
      return true;
    }
    if (!user) {
      sendJson(response, 401, { error: 'Günlük ödül için giriş yapmalısınız.' });
      return true;
    }
    const lockKey = `daily:${user.username}`;
    if (claimLocks.has(lockKey)) {
      sendJson(response, 409, { error: 'İşlem devam ediyor, lütfen bekleyin.' });
      return true;
    }
    claimLocks.add(lockKey);
    try {
      const today = dailyQuestDayKey();
      const state = dailyRewardState(user);
      if (state.claimedDate === today) {
        sendJson(response, 409, { error: 'Bugünkü günlük ödül zaten alındı.', ...state, claimedToday: true });
        return true;
      }
      const reward = DAILY_REWARDS[state.day - 1];
      user.coins = (user.coins || 0) + reward;
      user.gold = user.coins;
      user.dailyReward = {
        day: state.day,
        claimedDate: today
      };
      saveAccountData(true);
      sendJson(response, 200, {
        ok: true,
        reward,
        day: state.day,
        claimedDate: today,
        nextDay: state.day >= DAILY_REWARDS.length ? 1 : state.day + 1,
        coins: user.coins,
        user: publicUser(user)
      });
      return true;
    } finally {
      claimLocks.delete(lockKey);
    }
  }

  /* ════════════════════════════════════════════════════════════════
     ARKADAŞ DAVET ETKİNLİĞİ API (DATABASE / SQLITE PERSISTENT)
  ════════════════════════════════════════════════════════════════ */
  if (requestPath === '/api/invite-event/state' && request.method === 'GET') {
    if (!user) {
      sendJson(response, 401, { error: 'Oturum gereklidir.' });
      return true;
    }
    if (!user.inviteEvent) {
      user.inviteEvent = { claimedMilestones: [false, false, false, false, false], invitedFriends: [] };
    }
    if (!user.referralCode) {
      user.referralCode = user.username;
    }
    sendJson(response, 200, {
      ok: true,
      referralCode: user.referralCode,
      referralUrl: `https://forestbrawl.fun/?ref=${encodeURIComponent(user.referralCode)}`,
      claimedMilestones: user.inviteEvent.claimedMilestones || [false, false, false, false, false],
      friends: user.inviteEvent.invitedFriends || []
    });
    return true;
  }

  if (requestPath === '/api/invite-event/claim' && request.method === 'POST') {
    if (authRateLimited(request, 'invite_claim')) {
      sendJson(response, 429, { error: 'Çok fazla istek. Lütfen biraz bekleyin.' });
      return true;
    }
    if (!user) {
      sendJson(response, 401, { error: 'Oturum gereklidir.' });
      return true;
    }
    const lockKey = `invite:${user.username}`;
    if (claimLocks.has(lockKey)) {
      sendJson(response, 409, { error: 'İşlem devam ediyor, lütfen bekleyin.' });
      return true;
    }
    claimLocks.add(lockKey);
    try {
      const step = parseInt(body.stepIndex, 10);
      if (isNaN(step) || step < 0 || step > 4) {
        sendJson(response, 400, { error: 'Geçersiz aşama.' });
        return true;
      }
      if (!user.inviteEvent) {
        user.inviteEvent = { claimedMilestones: [false, false, false, false, false], invitedFriends: [] };
      }
      if (!Array.isArray(user.inviteEvent.invitedFriends)) user.inviteEvent.invitedFriends = [];
      if (!Array.isArray(user.inviteEvent.claimedMilestones)) user.inviteEvent.claimedMilestones = [false, false, false, false, false];

      const completedCount = user.inviteEvent.invitedFriends.filter(f => f.completed).length;
      if (completedCount < step + 1) {
        sendJson(response, 400, { error: `Bu ödül için en az ${step + 1} davet edilmiş arkadaşının görevleri tamamlaması gerekir.` });
        return true;
      }
      if (user.inviteEvent.claimedMilestones[step]) {
        sendJson(response, 409, { error: 'Bu aşamanın ödülü zaten alındı.' });
        return true;
      }

      const milestoneRewards = [
        { gold: 500, xp: 100, title: '1. Davet Ödülü' },
        { gold: 1000, xp: 250, title: '2. Davet Ödülü' },
        { gold: 2000, xp: 500, frameId: 'frame_flame', title: '3. Davet Ödülü (Alev Mührü)' },
        { gold: 3500, xp: 1000, title: '4. Davet Ödülü' },
        { gold: 5000, xp: 2500, skinId: 'kiz_ates', title: '5. Efsanevi Ödül (Ateş Büyücüsü)' }
      ];
      const m = milestoneRewards[step];

      user.coins = (user.coins || 0) + m.gold;
      user.gold = user.coins;
      user.xp = (user.xp || 0) + m.xp;
      user.rankId = rankInfo(user.xp).rankId;

      if (m.frameId) {
        user.ownedItems = ownedItemsForUser(user, [...(user.ownedItems || []), m.frameId]);
      }
      if (m.skinId) {
        user.ownedItems = ownedItemsForUser(user, [...(user.ownedItems || []), m.skinId]);
        user.equippedItems = equippedItemsForUser(user, { ...(user.equippedItems || {}), deriler: m.skinId });
      }

      user.inviteEvent.claimedMilestones[step] = true;
      saveAccountData(true);

      sendJson(response, 200, {
        ok: true,
        stepIndex: step,
        reward: m,
        claimedMilestones: user.inviteEvent.claimedMilestones,
        coins: user.coins,
        gold: user.gold,
        xp: user.xp,
        user: publicUser(user)
      });
      return true;
    } finally {
      claimLocks.delete(lockKey);
    }
  }

  if (requestPath === '/api/invite-event/simulate' && request.method === 'POST') {
    if (!user) {
      sendJson(response, 401, { error: 'Oturum gereklidir.' });
      return true;
    }
    if (!user.inviteEvent) {
      user.inviteEvent = { claimedMilestones: [false, false, false, false, false], invitedFriends: [] };
    }
    if (!Array.isArray(user.inviteEvent.invitedFriends)) user.inviteEvent.invitedFriends = [];

    // Devam eden arkadaş varsa görevlerini tamamla
    const uncompleted = user.inviteEvent.invitedFriends.find(f => !f.completed);
    if (uncompleted) {
      uncompleted.tasks.level.current = 3; uncompleted.tasks.level.done = true;
      uncompleted.tasks.resources.current = 500; uncompleted.tasks.resources.done = true;
      uncompleted.tasks.kills.current = 1; uncompleted.tasks.kills.done = true;
      uncompleted.tasks.survival.current = 3; uncompleted.tasks.survival.done = true;
      uncompleted.completed = true;
      saveAccountData(true);
      sendJson(response, 200, { ok: true, friends: user.inviteEvent.invitedFriends, completedFriend: uncompleted.username });
      return true;
    }

    // Yeni arkadaş ekle ve görevlerini tamamla
    if (user.inviteEvent.invitedFriends.length < 5) {
      const names = ['Kral_Savasci', 'Atesli_Buyucu', 'Orman_Golgesi', 'Buz_Kralicesi', 'Sampiyon_Panda'];
      const idx = user.inviteEvent.invitedFriends.length;
      const newFriend = {
        id: 9000 + idx,
        username: names[idx] || `Davetli_${idx + 1}`,
        joinedAt: Date.now(),
        tasks: {
          level: { name: "Seviye 3'e Ulaş", current: 3, target: 3, done: true },
          resources: { name: "500 Kaynak Topla", current: 500, target: 500, done: true },
          kills: { name: "1 Rakip Alt Et", current: 1, target: 1, done: true },
          survival: { name: "3 Dk Hayatta Kal", current: 3, target: 3, done: true }
        },
        completed: true
      };
      user.inviteEvent.invitedFriends.push(newFriend);
      saveAccountData(true);
      sendJson(response, 200, { ok: true, friends: user.inviteEvent.invitedFriends, newFriend: newFriend.username });
      return true;
    }

    sendJson(response, 200, { ok: true, friends: user.inviteEvent.invitedFriends, full: true });
    return true;
  }

  if (requestPath === '/api/invite-event/reset' && request.method === 'POST') {
    if (!user) {
      sendJson(response, 401, { error: 'Oturum gereklidir.' });
      return true;
    }
    user.inviteEvent = { claimedMilestones: [false, false, false, false, false], invitedFriends: [] };
    saveAccountData(true);
    sendJson(response, 200, { ok: true, claimedMilestones: user.inviteEvent.claimedMilestones, friends: [] });
    return true;
  }

  // ==================== İÇERİK ÜRETİCİ ETKİNLİĞİ (CREATOR EVENT) ====================
  if (requestPath === '/api/creator-event/state' && request.method === 'GET') {
    if (!user) {
      sendJson(response, 401, { error: 'Oturum gereklidir.' });
      return true;
    }
    if (!user.creatorEvent) {
      user.creatorEvent = { submissions: [], claimedTiers: [false, false, false, false], totalViews: 0, isVerifiedCreator: false };
    }
    sendJson(response, 200, {
      ok: true,
      submissions: user.creatorEvent.submissions || [],
      claimedTiers: user.creatorEvent.claimedTiers || [false, false, false, false],
      totalViews: user.creatorEvent.totalViews || 0,
      isCreatorVerified: Boolean(user.creatorEvent.isVerifiedCreator || user.isCreatorVerified),
      userGold: user.gold || 0,
      userDiamonds: user.diamonds || 0
    });
    return true;
  }

  if (requestPath === '/api/creator-event/submit' && request.method === 'POST') {
    if (!user) {
      sendJson(response, 401, { error: 'Oturum gereklidir.' });
      return true;
    }
    if (!user.creatorEvent) {
      user.creatorEvent = { submissions: [], claimedTiers: [false, false, false, false], totalViews: 0, isVerifiedCreator: false };
    }
    if (!Array.isArray(user.creatorEvent.submissions)) user.creatorEvent.submissions = [];

    const platform = String(body.platform || '').trim().toLowerCase();
    const url = String(body.url || body.videoUrl || '').trim();
    const channel = String(body.channel || body.channelName || '').trim();
    const estimatedViews = Math.max(100, Number(body.estimatedViews) || 1000);
    const note = String(body.note || body.notes || '').trim().slice(0, 300);

    if (!['tiktok', 'youtube', 'instagram'].includes(platform)) {
      sendJson(response, 400, { error: 'Geçersiz platform. TikTok, YouTube veya Instagram seçilmelidir.' });
      return true;
    }
    if (!url || !url.startsWith('http')) {
      sendJson(response, 400, { error: 'Lütfen geçerli bir video bağlantı adresi (URL) girin.' });
      return true;
    }

    if (platform === 'tiktok' && !url.includes('tiktok.com')) {
      sendJson(response, 400, { error: 'Girdiğiniz link geçerli bir TikTok video linki olmalıdır.' });
      return true;
    }
    if (platform === 'youtube' && !url.includes('youtube.com') && !url.includes('youtu.be')) {
      sendJson(response, 400, { error: 'Girdiğiniz link geçerli bir YouTube video linki olmalıdır.' });
      return true;
    }
    if (platform === 'instagram' && !url.includes('instagram.com')) {
      sendJson(response, 400, { error: 'Girdiğiniz link geçerli bir Instagram video linki olmalıdır.' });
      return true;
    }

    const isDuplicate = user.creatorEvent.submissions.some(s => s.url.toLowerCase() === url.toLowerCase());
    if (isDuplicate) {
      sendJson(response, 409, { error: 'Bu video linkini daha önce zaten gönderdiniz.' });
      return true;
    }

    const newSub = {
      id: 'sub_' + Date.now() + '_' + Math.random().toString(36).substr(2, 5),
      platform,
      url,
      channel: channel || ('@' + user.username),
      estimatedViews,
      note,
      submittedAt: Date.now(),
      status: 'pending'
    };

    user.creatorEvent.submissions.unshift(newSub);
    saveAccountData(true);

    sendJson(response, 200, {
      ok: true,
      submission: newSub,
      submissions: user.creatorEvent.submissions
    });
    return true;
  }

  if (requestPath === '/api/creator-event/claim' && request.method === 'POST') {
    if (authRateLimited(request, 'creator_claim')) {
      sendJson(response, 429, { error: 'Çok fazla istek. Lütfen biraz bekleyin.' });
      return true;
    }
    if (!user) {
      sendJson(response, 401, { error: 'Oturum gereklidir.' });
      return true;
    }
    const lockKey = `creator:${user.username}`;
    if (claimLocks.has(lockKey)) {
      sendJson(response, 409, { error: 'İşlem devam ediyor, lütfen bekleyin.' });
      return true;
    }
    claimLocks.add(lockKey);
    try {
      const rawTier = body.tierIndex !== undefined ? body.tierIndex : (body.tierId !== undefined ? (Number(body.tierId) > 0 && Number(body.tierId) <= 4 ? Number(body.tierId) - 1 : body.tierId) : body.tier);
      const tier = parseInt(rawTier, 10);
      if (isNaN(tier) || tier < 0 || tier > 3) {
        sendJson(response, 400, { error: 'Geçersiz kademe.' });
        return true;
      }
      if (!user.creatorEvent) {
        user.creatorEvent = { submissions: [], claimedTiers: [false, false, false, false], totalViews: 0, isVerifiedCreator: false };
      }
      if (!Array.isArray(user.creatorEvent.claimedTiers)) user.creatorEvent.claimedTiers = [false, false, false, false];

      if (user.creatorEvent.claimedTiers[tier]) {
        sendJson(response, 409, { error: 'Bu kademenin ödülü zaten alındı.' });
        return true;
      }

      const approvedSubs = (user.creatorEvent.submissions || []).filter(s => s.status === 'approved');
      const reqViews = [1000, 10000, 50000, 200000];
      const totalApprovedViews = approvedSubs.reduce((sum, s) => sum + (Number(s.estimatedViews) || 1000), 0);

      const canClaim = totalApprovedViews >= reqViews[tier] || approvedSubs.length >= tier + 1;
      if (!canClaim) {
        sendJson(response, 400, { error: `Bu ödül için en az ${reqViews[tier].toLocaleString('tr-TR')} izlenmeye ulaşan onaylı bir videonuz olmalıdır.` });
        return true;
      }

      const tierRewards = [
        { gold: 5000, xp: 1000, title: '1. Kademe: Çaylak Üretici' },
        { gold: 25000, xp: 3000, diamonds: 350, title: '2. Kademe: Popüler Yıldız' },
        { gold: 75000, xp: 10000, diamonds: 1200, skinId: 'kiz_ates', title: '3. Kademe: Viral Fenomen' },
        { gold: 200000, xp: 25000, diamonds: 5000, verified: true, title: '4. Kademe: Orman Efsanesi Partner' }
      ];
      const reward = tierRewards[tier];

      user.coins = (user.coins || 0) + reward.gold;
      user.gold = user.coins;
      user.diamonds = (user.diamonds || 0) + (reward.diamonds || 0);
      user.xp = (user.xp || 0) + reward.xp;
      user.rankId = rankInfo(user.xp).rankId;

      if (reward.skinId) {
        user.ownedItems = ownedItemsForUser(user, [...(user.ownedItems || []), reward.skinId]);
      }
      if (reward.verified) {
        user.creatorEvent.isVerifiedCreator = true;
      }

      user.creatorEvent.claimedTiers[tier] = true;
      saveAccountData(true);

      sendJson(response, 200, {
        ok: true,
        tierIndex: tier,
        reward,
        claimedTiers: user.creatorEvent.claimedTiers,
        coins: user.coins,
        gold: user.gold,
        xp: user.xp,
        user: publicUser(user)
      });
      return true;
    } finally {
      claimLocks.delete(lockKey);
    }
  }

  if (requestPath === '/api/creator-event/simulate' && request.method === 'POST') {
    if (!user) {
      sendJson(response, 401, { error: 'Oturum gereklidir.' });
      return true;
    }
    if (!user.creatorEvent) {
      user.creatorEvent = { submissions: [], claimedTiers: [false, false, false, false], totalViews: 0, isVerifiedCreator: false };
    }
    if (!Array.isArray(user.creatorEvent.submissions)) user.creatorEvent.submissions = [];

    const pending = user.creatorEvent.submissions.find(s => s.status === 'pending');
    if (pending) {
      pending.status = 'approved';
      pending.approvedAt = Date.now();
      pending.estimatedViews = Math.max(Number(pending.estimatedViews) || 1000, 15000);
      user.creatorEvent.totalViews = (user.creatorEvent.submissions || []).reduce((sum, s) => sum + (s.status === 'approved' ? (s.estimatedViews || 0) : 0), 0);
      saveAccountData(true);
      sendJson(response, 200, { ok: true, submission: pending, submissions: user.creatorEvent.submissions, message: 'Bekleyen video başarıyla onaylandı!' });
      return true;
    }

    const platforms = ['tiktok', 'youtube', 'instagram'];
    const viewsList = [5000, 25000, 80000, 250000];
    const idx = Math.min(user.creatorEvent.submissions.length, 3);
    const chosenPlat = platforms[idx % platforms.length];
    const newSim = {
      id: 'sub_sim_' + Date.now(),
      platform: chosenPlat,
      url: chosenPlat === 'tiktok' ? `https://www.tiktok.com/@${user.username}/video/7281928371928` : (chosenPlat === 'youtube' ? `https://youtube.com/shorts/fb_highlight_${Date.now()}` : `https://instagram.com/reel/C819283719`),
      channel: '@' + user.username,
      estimatedViews: viewsList[idx] || 50000,
      note: 'ForestBrawl efsane vuruşlar & öğretici!',
      submittedAt: Date.now(),
      approvedAt: Date.now(),
      status: 'approved'
    };
    user.creatorEvent.submissions.unshift(newSim);
    user.creatorEvent.totalViews = user.creatorEvent.submissions.reduce((sum, s) => sum + (s.status === 'approved' ? (s.estimatedViews || 0) : 0), 0);
    saveAccountData(true);
    sendJson(response, 200, { ok: true, submission: newSim, submissions: user.creatorEvent.submissions, message: 'Test videosu eklendi ve onaylandı!' });
    return true;
  }

  if (requestPath === '/api/creator-event/reset' && request.method === 'POST') {
    if (!user) {
      sendJson(response, 401, { error: 'Oturum gereklidir.' });
      return true;
    }
    user.creatorEvent = { submissions: [], claimedTiers: [false, false, false, false], totalViews: 0, isVerifiedCreator: false };
    saveAccountData(true);
    sendJson(response, 200, { ok: true, claimedTiers: [false, false, false, false], submissions: [] });
    return true;
  }
  if (requestPath === '/api/shop/owned' && request.method === 'GET') {
    if (!user) sendJson(response, 401, { error: 'Oturum gerekli.' });
    else sendJson(response, 200, publicUser(user));
    return true;
  }
  if (requestPath === '/api/shop/sync' && request.method === 'POST') {
    if (!user) sendJson(response, 401, { error: 'Oturum gereklidir.' });
    else {
      if (body.equippedItems && typeof body.equippedItems === 'object') {
        user.equippedItems = equippedItemsForUser(user, { ...(user.equippedItems || {}), ...body.equippedItems });
      }
      saveAccountData(true);
      sendJson(response, 200, publicUser(user));
    }
    return true;
  }
  if (requestPath === '/api/shop/equip' && request.method === 'PUT') {
    if (!user) sendJson(response, 401, { error: 'Oturum gereklidir.' });
    else {
      let cat = String(body.category || '');
      const item = normalizeShopItemId(body.itemId);
      if (cat) {
        if (cat === 'pp') cat = 'deriler';
        if (item === 'thor' && !canUseThor(user)) {
          sendJson(response, 403, { error: 'Thor derisi yalnızca Basilisk hesabına aittir.' });
          return true;
        }
        if (['deriler', 'kiliclar', 'baltalar', 'profil_avatar'].includes(cat) && !canEquipShopItem(user, cat, item)) {
          sendJson(response, 403, { error: 'Bu kozmetik hesabında bulunmuyor.' });
          return true;
        }
        user.equippedItems = equippedItemsForUser(user, { ...(user.equippedItems || {}), [cat]: item });
        if (cat === 'deriler' || cat === 'profil_avatar') {
          user.equippedItems.deriler = item;
          user.equippedItems.profil_avatar = item;
        } else if (cat === 'efektler' || cat === 'profil_efekt') {
          user.equippedItems.profil_efekt = item;
          user.equippedItems.efektler = item;
        } else if (cat === 'cerceveler' || cat === 'profil_cerceve') {
          user.equippedItems.profil_cerceve = item;
          user.equippedItems.cerceveler = item;
        }

        const uKey = usernameKey(user.username);

        // 1. Canlı oyundaki tüm bağlı oyuncu örneklerinde skin'i güncelle
        for (const player of players.values()) {
          if (player._authUser && usernameKey(player._authUser.username) === uKey) {
            if (cat === 'deriler' || cat === 'profil_avatar') {
              player.skin = item;
            }
          }
        }

        // 2. Liderlik tablosundaki (Leaderboard) profil kozmetiklerini de hemen güncelle
        if (accountData.leaderboard && accountData.leaderboard[uKey]) {
          if (!accountData.leaderboard[uKey].profileCosmetics) {
            accountData.leaderboard[uKey].profileCosmetics = {};
          }
          accountData.leaderboard[uKey].profileCosmetics.avatarId = user.equippedItems?.profil_avatar || user.equippedItems?.deriler || 'wolf';
          accountData.leaderboard[uKey].profileCosmetics.skinId = user.equippedItems?.deriler || user.equippedItems?.profil_avatar || 'wolf';
          accountData.leaderboard[uKey].profileCosmetics.effectId = user.equippedItems?.profil_efekt || user.equippedItems?.efektler || 'effect_none';
          accountData.leaderboard[uKey].profileCosmetics.frameId = user.equippedItems?.profil_cerceve || user.equippedItems?.cerceveler || 'frame_woodland';
        }

        saveAccountData(true);
      }
      sendJson(response, 200, { success: true, equippedItems: user.equippedItems });
    }
    return true;
  }
  if (requestPath === '/api/diamonds/buy' && request.method === 'POST') {
    if (!user) {
      sendJson(response, 401, { error: 'Diamond satın almak için giriş yapmalısın.' });
      return true;
    }
    if (authRateLimited(request, 'diamond_buy')) {
      sendJson(response, 429, { error: 'Diamond satın alma limiti aşıldı.' });
      return true;
    }
    const amount = Math.floor(Number(body.amount));
    if (!Number.isSafeInteger(amount) || amount < 1) {
      sendJson(response, 400, { error: 'Geçerli bir diamond miktarı gir.' });
      return true;
    }
    const totalCost = amount * 5000;
    if (!Number.isSafeInteger(totalCost)) {
      sendJson(response, 400, { error: 'İstenen diamond miktarı çok büyük.' });
      return true;
    }
    const availableScore = Math.max(0, Number(user.score) || 0);
    if (availableScore < totalCost) {
      sendJson(response, 400, { error: `Yetersiz score. ${amount} diamond için ${totalCost.toLocaleString('tr-TR')} score gerekli.` });
      return true;
    }
    user.score = availableScore - totalCost;
    user.diamonds = Math.max(0, Number(user.diamonds) || 0) + amount;
    await saveAccountData(true);
    sendJson(response, 200, {
      success: true,
      amount,
      cost: totalCost,
      score: user.score,
      newScore: user.score,
      newDiamonds: user.diamonds,
      diamonds: user.diamonds,
      user: publicUser(user)
    });
    return true;
  }
  if (requestPath === '/api/shop/buy' && request.method === 'POST') {
    if (!user) sendJson(response, 401, { error: 'Oturum gereklidir.' });
    else {
      if (authRateLimited(request, 'shop_buy')) {
        sendJson(response, 429, { error: 'Alışveriş limiti aşıldı.' });
        return true;
      }
      const itemId = normalizeShopItemId(body.itemId);
      const chest = CHEST_CONFIG[String(body.chestId || itemId)];
      if (chest) {
        if ((user.diamonds || 0) < chest.cost) {
          sendJson(response, 400, { error: `Yetersiz diamond. ${chest.cost.toLocaleString('tr-TR')} diamond gerekli.` });
        } else {
          const ownedItems = new Set(Array.isArray(user.ownedItems) ? user.ownedItems.map(String) : []);
          const availableRewards = chest.rewards.filter(rewardId => !ownedItems.has(rewardId));
          if (!availableRewards.length) {
            sendJson(response, 409, { error: 'Bu sandıktaki tüm skinlere zaten sahipsin.' });
            return true;
          }
          const rewardId = chooseChestReward(availableRewards);
          user.diamonds = Math.max(0, Number(user.diamonds) || 0) - chest.cost;
          user.ownedItems = [...new Set([...(user.ownedItems || []), rewardId])];
          saveAccountData(true);
          sendJson(response, 200, { success: true, chestId: Object.keys(CHEST_CONFIG).find(id => CHEST_CONFIG[id] === chest), rewardId, newDiamonds: user.diamonds, diamonds: user.diamonds, ownedItems: user.ownedItems });
        }
        return true;
      }
      const cosmetic = findShopItem(itemId);
      const cost = cosmetic ? Math.max(1, Number(cosmetic.price) || 1) : null;
      if (itemId === 'thor' && !canUseThor(user)) {
        sendJson(response, 403, { error: 'Thor derisi yalnızca Basilisk hesabına aittir.' });
      } else if (!itemId || !cosmetic) {
        sendJson(response, 400, { error: 'Geçersiz eşya.' });
      } else if (cosmetic.type === 'axe' || cosmetic.type === 'sword') {
        sendJson(response, 403, { error: 'Kılıç ve balta mağaza sekmeleri kilitli.' });
      } else if ((user.ownedItems || []).includes(itemId)) {
        sendJson(response, 409, { error: 'Bu eşyaya zaten sahipsin.' });
      } else if ((user.diamonds || 0) < cost) {
        sendJson(response, 400, { error: `Yetersiz diamond. ${cost.toLocaleString('tr-TR')} diamond gerekli.` });
      } else {
        user.diamonds = Math.max(0, Number(user.diamonds) || 0) - cost;
        user.ownedItems = [...new Set([...(user.ownedItems || []), itemId])];
        saveAccountData(true);
        sendJson(response, 200, { success: true, newDiamonds: user.diamonds, diamonds: user.diamonds, ownedItems: user.ownedItems });
      }
    }
    return true;
  }
  sendJson(response, 404, { error: 'API endpoint bulunamadı.' });
  return true;
}

const mime = {
  '.html': 'text/html; charset=utf-8',
  '.css': 'text/css; charset=utf-8',
  '.js': 'application/javascript; charset=utf-8',
  '.json': 'application/json; charset=utf-8',
  '.svg': 'image/svg+xml',
  '.png': 'image/png',
  '.jpg': 'image/jpeg',
  '.jpeg': 'image/jpeg',
  '.webp': 'image/webp',
  '.avif': 'image/avif',
  '.ico': 'image/x-icon',
  '.txt': 'text/plain; charset=utf-8',
  '.woff': 'font/woff',
  '.woff2': 'font/woff2',
  '.ttf': 'font/ttf',
  '.mp3': 'audio/mpeg',
  '.ogg': 'audio/ogg',
  '.wav': 'audio/wav',
};

const server = http.createServer((request, response) => {
  let requestPath;
  try {
    requestPath = decodeURIComponent((request.url || '/').split('?')[0]);
  } catch {
    response.writeHead(400, { 'Content-Type': 'text/plain; charset=utf-8' });
    response.end('Bad request');
    return;
  }
  handleApi(request, response, requestPath).then(handled => {
    if (handled) return;
    serveStatic(request, response, requestPath);
  }).catch(error => {
    console.error('Request error:', error);
    if (!response.headersSent) sendJson(response, 500, { error: 'Sunucu hatası.' });
  });
});

function serveStatic(request, response, requestPath) {
  const normalized = String(requestPath || '/').trim();

  if (normalized === '/admin' || normalized === '/admin/' || normalized === '/game/admin' || normalized === '/game/admin/') {
    response.writeHead(302, { Location: '/admin.html' });
    response.end();
    return;
  }

  if (normalized === '/admin.html' || normalized === '/game/admin.html') {
    requestPath = '/admin/index.html';
  }
  else if (normalized === '/admin.css' || normalized === '/game/admin.css') {
    requestPath = '/admin/admin.css';
  }
  else if (normalized === '/admin.js' || normalized === '/game/admin.js') {
    requestPath = '/admin/admin.js';
  }
  else if (normalized === '/admin/index.html' || normalized === '/game/admin/index.html') {
    requestPath = '/admin/index.html';
  }
  else if (normalized === '/favicon.ico') {
    requestPath = '/favicon-32.png';
  }
  else if (normalized === '/ads.txt' || normalized === '/game/ads.txt' || normalized === '/.well-known/ads.txt') {
    const candidateAds = [
      path.join(root, 'ads.txt'),
      path.join(root, 'game', 'ads.txt'),
      path.join(__dirname, 'ads.txt'),
      path.join(__dirname, 'game', 'ads.txt')
    ];
    for (const ca of candidateAds) {
      if (fs.existsSync(ca)) {
        response.writeHead(200, {
          'Content-Type': 'text/plain; charset=utf-8',
          'Cache-Control': 'public, max-age=86400',
          'X-Content-Type-Options': 'nosniff'
        });
        fs.createReadStream(ca).pipe(response);
        return;
      }
    }
  }

  if (requestPath === '/.well-known/assetlinks.json' || requestPath === '/assetlinks.json') {
    const candidatePaths = [
      path.join(root, '.well-known', 'assetlinks.json'),
      path.join(__dirname, '..', 'assetlinks.json'),
      path.join(__dirname, 'assetlinks.json'),
      path.join(__dirname, 'game', 'assetlinks.json')
    ];
    let foundPath = null;
    for (const cp of candidatePaths) {
      try { if (fs.existsSync(cp)) { foundPath = cp; break; } } catch (_) {}
    }
    if (foundPath) {
      fs.readFile(foundPath, (error, data) => {
        if (error) {
          response.writeHead(500, { 'Content-Type': 'application/json; charset=utf-8' });
          response.end('{"error":"Read error"}');
          return;
        }
        response.writeHead(200, {
          'Content-Type': 'application/json; charset=utf-8',
          'Cache-Control': 'public, max-age=3600',
          'X-Content-Type-Options': 'nosniff',
          'Access-Control-Allow-Origin': '*'
        });
        response.end(data);
      });
      return;
    }
    response.writeHead(404, { 'Content-Type': 'application/json; charset=utf-8', 'Cache-Control': 'no-cache' });
    response.end('{"error":"assetlinks.json not found"}');
    return;
  }

  let relative = requestPath === '/' ? 'index.html' : requestPath.replace(/^\/+/, '');
  if (relative.startsWith('game/')) relative = relative.slice(5);
  else if (relative.startsWith('game\\')) relative = relative.slice(5);
  if (relative === '') relative = 'index.html';
  if (relative.endsWith('/')) relative += 'index.html';

  const blockedPath = /(^|[\\/])(?:\.|server\.js$|package(?:-lock)?\.json$|forest-data\.json(?:\.bak)?$|ecosystem\.config\.[cm]?js$|render\.yaml$|\.nvmrc$)/i;
  const isAssetLinks = relative === '.well-known/assetlinks.json';
  if (!isAssetLinks && blockedPath.test(relative)) {
    response.writeHead(404, { 'Content-Type': 'text/plain; charset=utf-8', 'X-Content-Type-Options': 'nosniff' });
    response.end('Not found');
    return;
  }

  const publicAssetDirs = new Set(['biomedecors', 'buildassets', 'mobassets', 'resourceasset', 'scytheassets', 'forestassetstrees', 'helmetsassets', 'koyassets', 'köyassets']);
  const topLevelDir = relative.split(/[\\/]/, 1)[0];
  let assetRoot = publicAssetDirs.has(topLevelDir) ? __dirname : root;
  let filePath = path.resolve(assetRoot, relative);
  if (!fs.existsSync(filePath)) {
    const altRoot = assetRoot === __dirname ? root : __dirname;
    const altPath = path.resolve(altRoot, relative);
    if (fs.existsSync(altPath)) {
      filePath = altPath;
      assetRoot = altRoot;
    } else {
      const safeRel = relative.replace(/İ/g, 'I').replace(/ı/g, 'i').replace(/İ/g, '%C4%B0');
      const safeCandidate1 = path.resolve(assetRoot, safeRel);
      const safeCandidate2 = path.resolve(altRoot, safeRel);
      if (fs.existsSync(safeCandidate1)) {
        filePath = safeCandidate1;
      } else if (fs.existsSync(safeCandidate2)) {
        filePath = safeCandidate2;
        assetRoot = altRoot;
      }
    }
  }
  const isGameFile = filePath.startsWith(`${root}${path.sep}`) || filePath === root;
  const isPublicAsset = publicAssetDirs.has(topLevelDir) && (filePath.startsWith(`${__dirname}${path.sep}${topLevelDir}`) || filePath.startsWith(`${root}${path.sep}${topLevelDir}`));
  if (!isGameFile && !isPublicAsset) {
    response.writeHead(403);
    response.end('Forbidden');
    return;
  }
  const gzipCache = serveStatic._gzipCache || (serveStatic._gzipCache = new Map());
  if (gzipCache.size > 60) {
    const oldestKey = gzipCache.keys().next().value;
    if (oldestKey) gzipCache.delete(oldestKey);
  }
  fs.readFile(filePath, (error, data) => {
    if (error) {
      response.writeHead(error.code === 'ENOENT' ? 404 : 500);
      response.end(error.code === 'ENOENT' ? 'Not found' : 'Server error');
      return;
    }
    const extension = path.extname(filePath).toLowerCase();
    const isHtmlOrCode = ['.html', '.js', '.css', '.json'].includes(extension);
    const isImage = ['.png', '.jpg', '.jpeg', '.webp', '.avif', '.gif', '.svg'].includes(extension);
    const headers = {
      'Content-Type': mime[extension] || 'application/octet-stream',
      'X-Content-Type-Options': 'nosniff',
      'Content-Security-Policy': "frame-ancestors 'self' https://forestbrawl.fun https://www.forestbrawl.fun https://titotu.io https://www.titotu.io https://titotu.ru https://www.titotu.ru",
      'Referrer-Policy': 'strict-origin-when-cross-origin',
      'Cross-Origin-Resource-Policy': 'cross-origin',
      'X-DNS-Prefetch-Control': 'on',
      'Permissions-Policy': 'camera=(), microphone=(), geolocation=()',
      'Cache-Control': isHtmlOrCode ? 'no-cache' : isImage ? 'public, max-age=604800, immutable' : 'public, max-age=86400',
    };

    const acceptEncoding = String(request.headers['accept-encoding'] || '');
    const isCompressible = ['.html', '.js', '.css', '.json', '.svg', '.txt'].includes(extension);
    if (isCompressible && acceptEncoding.includes('gzip')) {
      const cached = gzipCache.get(filePath);
      if (cached && !isHtmlOrCode) {
        headers['Content-Encoding'] = 'gzip';
        headers['Vary'] = 'Accept-Encoding';
        response.writeHead(200, headers);
        response.end(cached);
        return;
      }
      zlib.gzip(data, (err, compressed) => {
        if (!err && compressed) {
          if (!isHtmlOrCode) gzipCache.set(filePath, compressed);
          headers['Content-Encoding'] = 'gzip';
          headers['Vary'] = 'Accept-Encoding';
          response.writeHead(200, headers);
          response.end(compressed);
          return;
        }
        response.writeHead(200, headers);
        response.end(data);
      });
      return;
    }

    response.writeHead(200, headers);
    response.end(data);
  });
}

const io = new Server(server, {
  path: '/api/socket.io',
  pingInterval: 2500,
  pingTimeout: 8000,
  allowUpgrades: true,
  perMessageDeflate: false,
  maxHttpBufferSize: 256 * 1024,
  cors: {
    origin: (origin, callback) => {
      if (!origin) return callback(null, true);
      return callback(null, isAllowedOrigin(origin));
    },
    methods: ['GET', 'POST'],
    credentials: true,
  },
});

io.use((socket, next) => {
  const clientIp = requestClientKey(socket.request || { headers: {}, socket: socket.conn?.transport?.socket });
  if (isClientBanned(clientIp, null)) {
    return next(new Error('Banned'));
  }
  next();
});

const WORLD_BOSS_DEFS = Object.freeze([
  {
    id: 'worldboss-scorpios',
    name: 'SCORPIOS • Akrep Kralı',
    level: 50,
    x: 5200, y: 0,
    radius: 112, maxHp: 180000, speed: 105, aggroRange: 1500,
    damage: 60, attackCooldownMs: 1250, respawnMs: 180000,
    rewardGold: 750, rewardXp: 1800, rewardScore: 3500,
    skill: { id: 'void-burn', name: 'Void Yanığı', type: 'circle', radius: 210, damage: 120, cooldownMs: 8500, telegraphMs: 1300, color: '#b84aff' }
  },
  {
    id: 'worldboss-goliath',
    name: 'GOLIATH • Kaya Devi',
    level: 65,
    x: 0, y: -5200,
    radius: 132, maxHp: 280000, speed: 78, aggroRange: 1650,
    damage: 85, attackCooldownMs: 1450, respawnMs: 180000,
    rewardGold: 1200, rewardXp: 2800, rewardScore: 5500,
    skill: { id: 'rock-spike', name: 'Kaya Dikenleri', type: 'line', length: 440, radius: 88, damage: 175, cooldownMs: 9500, telegraphMs: 1450, color: '#d77b32' }
  }
]);

const worldBossStates = new Map(WORLD_BOSS_DEFS.map(def => [def.id, {
  id: def.id, x: def.x, y: def.y, homeX: def.x, homeY: def.y,
  vx: 0, vy: 0, angle: 0, hp: def.maxHp, maxHp: def.maxHp,
  alive: true, aggroed: false, state: 'idle', attackUntil: 0,
  hitFlashUntil: 0, lastAttackAt: 0, nextSkillAt: Date.now() + 5000,
  casting: null, respawnAt: 0, targetId: null, contributors: new Map()
}]));

function publicWorldBosses() {
  return WORLD_BOSS_DEFS.map(def => {
    const boss = worldBossStates.get(def.id);
    return {
      id: boss.id, name: def.name, level: def.level || 50, lvl: def.level || 50,
      x: Math.round(boss.x * 10) / 10, y: Math.round(boss.y * 10) / 10,
      vx: Math.round(boss.vx * 10) / 10, vy: Math.round(boss.vy * 10) / 10,
      angle: boss.angle, hp: boss.hp, maxHp: boss.maxHp,
      alive: boss.alive, aggroed: boss.aggroed, state: boss.state,
      attackUntil: boss.attackUntil, hitFlashUntil: boss.hitFlashUntil,
      respawnAt: boss.respawnAt
    };
  });
}

function broadcastWorldBossStates(volatile = false) {
  const states = publicWorldBosses();
  if (volatile) io.volatile.emit('world_boss_states', states);
  else io.emit('world_boss_states', states);
}

function worldBossSkillHitsPlayer(def, boss, cast, target) {
  const dx = target.x - cast.x;
  const dy = target.y - cast.y;
  const distance = Math.hypot(dx, dy);
  const playerRadius = Math.max(16, Math.min(64, Number(target.radius) || 24));
  if (cast.type === 'circle') return distance <= cast.radius + playerRadius;
  if (cast.type === 'line') {
    const forward = dx * Math.cos(cast.angle) + dy * Math.sin(cast.angle);
    const lateral = Math.abs(-dx * Math.sin(cast.angle) + dy * Math.cos(cast.angle));
    return forward >= 0 && forward <= cast.length && lateral <= cast.radius + playerRadius;
  }
  return false;
}

function recordWorldBossContribution(boss, player, damage) {
  if (!boss.contributors) boss.contributors = new Map();
  const current = boss.contributors.get(player.id) || { damage: 0 };
  current.damage += Math.max(0, Number(damage) || 0);
  boss.contributors.set(player.id, current);
}

function defeatWorldBoss(def, boss, attacker, now) {
  boss.alive = false;
  boss.aggroed = false;
  boss.state = 'dead';
  boss.vx = 0;
  boss.vy = 0;
  boss.casting = null;
  boss.targetId = null;
  boss.respawnAt = now + def.respawnMs;
  const gold = def.rewardGold;
  const xp = Math.max(1, Math.round(def.rewardXp * Math.max(0.1, Number(adminConfig.xpRate) || 1)));
  const score = def.rewardScore;
  const minimumDamage = Math.max(1, Math.ceil(def.maxHp * 0.02));
  const participants = [...(boss.contributors || new Map()).entries()]
    .map(([playerId, contribution]) => ({ player: players.get(playerId), damage: contribution.damage }))
    .filter(entry => entry.player && !entry.player.isBot && entry.damage >= minimumDamage);
  if (attacker && !attacker.isBot && !participants.some(entry => entry.player.id === attacker.id)) {
    participants.push({ player: attacker, damage: Math.max(1, boss.contributors?.get(attacker.id)?.damage || 1) });
  }
  if (!participants.length) {
    broadcastWorldBossStates();
    io.emit('world_boss_defeated', {
      id: def.id, name: def.name, killer: attacker?.name || 'Oyuncular',
      respawnAt: boss.respawnAt
    });
    return;
  }
  const totalDamage = participants.reduce((total, entry) => total + entry.damage, 0);
  let paidGold = 0, paidXp = 0, paidScore = 0;
  participants.forEach((entry, index) => {
    const isLastHitter = entry.player.id === attacker?.id;
    const share = totalDamage > 0 ? entry.damage / totalDamage : 1 / participants.length;
    const rewardGold = index === participants.length - 1 ? gold - paidGold : Math.floor(gold * share);
    const rewardXp = index === participants.length - 1 ? xp - paidXp : Math.floor(xp * share);
    const rewardScore = index === participants.length - 1 ? score - paidScore : Math.floor(score * share);
    paidGold += rewardGold;
    paidXp += rewardXp;
    paidScore += rewardScore;
    const lastHitBonus = isLastHitter ? Math.floor(gold * 0.1) : 0;
    const player = entry.player;
    player.gold = Math.min(MAX_ACCOUNT_COINS, (player.gold || 0) + rewardGold + lastHitBonus);
    player.xp = Math.min(MAX_ACCOUNT_XP, (player.xp || 0) + rewardXp);
    player.score = Math.min(MAX_ACCOUNT_SCORE, (player.score || 0) + rewardScore + lastHitBonus);
    player.sc = player.score;
    player.kills = (player.kills || 0) + 1;
    if (player._authUser) {
      player._authUser.xp = player.xp;
      player._authUser.rankId = rankInfo(player.xp).rankId;
    }
    recordServerQuestProgress(player, { bosses: 1, gold: rewardGold + lastHitBonus });
    persistPlayerScore(player);
    io.to(player.id).emit('self_state', { g: player.gold, xp: player.xp, sc: player.score, k: player.kills });
    io.to(player.id).emit('world_boss_reward', {
      id: def.id, name: def.name, gold: rewardGold + lastHitBonus, xp: rewardXp,
      score: rewardScore + lastHitBonus, contribution: entry.damage, lastHit: isLastHitter
    });
    awardLoot(player, def.level, true);
  });

  broadcastWorldBossStates();
  io.emit('world_boss_defeated', {
    id: def.id, name: def.name, killer: attacker?.name || 'Oyuncular',
    respawnAt: boss.respawnAt
  });
}

let lastWorldBossBroadcastAt = 0;
function resolveStaticCircleCollision(entity, entityRadius, obstacleX, obstacleY, obstacleRadius, previousPosition = null) {
  const minDistance = entityRadius + obstacleRadius;
  let dx = entity.x - obstacleX;
  let dy = entity.y - obstacleY;
  const distanceSquared = dx * dx + dy * dy;
  let distance = Math.sqrt(distanceSquared);
  if (distanceSquared >= minDistance * minDistance) {
    const startX = Number(previousPosition?.x);
    const startY = Number(previousPosition?.y);
    if (!Number.isFinite(startX) || !Number.isFinite(startY)) return false;
    const moveX = entity.x - startX;
    const moveY = entity.y - startY;
    const moveSquared = moveX * moveX + moveY * moveY;
    if (moveSquared <= 1e-9) return false;
    const offsetX = startX - obstacleX;
    const offsetY = startY - obstacleY;
    const b = 2 * (offsetX * moveX + offsetY * moveY);
    const c = offsetX * offsetX + offsetY * offsetY - minDistance * minDistance;
    const discriminant = b * b - 4 * moveSquared * c;
    if (c <= 0 || discriminant < 0) return false;
    const entry = (-b - Math.sqrt(discriminant)) / (2 * moveSquared);
    if (entry < 0 || entry > 1) return false;
    const contactX = startX + moveX * entry;
    const contactY = startY + moveY * entry;
    dx = contactX - obstacleX;
    dy = contactY - obstacleY;
    distance = Math.hypot(dx, dy);
    entity.x = contactX;
    entity.y = contactY;
  }

  const angle = Number.isFinite(Number(entity.angle)) ? Number(entity.angle) : 0;
  const nx = distance > 1e-6 ? dx / distance : -Math.cos(angle);
  const ny = distance > 1e-6 ? dy / distance : -Math.sin(angle);
  const separation = Math.max(0, minDistance - distance) + 0.5;
  entity.x += nx * separation;
  entity.y += ny * separation;

  const inwardVelocity = (Number(entity.vx) || 0) * nx + (Number(entity.vy) || 0) * ny;
  if (inwardVelocity < 0) {
    entity.vx = (Number(entity.vx) || 0) - inwardVelocity * nx;
    entity.vy = (Number(entity.vy) || 0) - inwardVelocity * ny;
  }
  return true;
}

setInterval(() => {
  const now = Date.now();
  let changed = false;

  for (const def of WORLD_BOSS_DEFS) {
    const boss = worldBossStates.get(def.id);
    if (!boss.alive) {
      if (boss.respawnAt > 0 && now >= boss.respawnAt) {
        boss.x = def.x; boss.y = def.y; boss.homeX = def.x; boss.homeY = def.y;
        boss.vx = 0; boss.vy = 0; boss.hp = def.maxHp; boss.contributors = new Map();
        boss.alive = true; boss.aggroed = false; boss.state = 'idle';
        boss.attackUntil = 0; boss.hitFlashUntil = 0; boss.lastAttackAt = 0;
        boss.nextSkillAt = now + 5000; boss.casting = null;
        boss.respawnAt = 0; boss.targetId = null;
        io.emit('world_boss_respawn', { id: def.id, x: def.x, y: def.y, hp: def.maxHp, maxHp: def.maxHp });
        changed = true;
      }
      continue;
    }

    if (boss.casting && now >= boss.casting.endsAt) {
      const cast = boss.casting;
      boss.casting = null;
      boss.state = 'attack';
      boss.attackUntil = now + 500;
      io.emit('world_boss_skill_impact', {
        id: def.id, effect: def.skill.id, x: cast.x, y: cast.y,
        angle: cast.angle, radius: cast.radius, length: cast.length
      });
      for (const target of players.values()) {
        if (!isPlayerCombatEligible(target) || !worldBossSkillHitsPlayer(def, boss, cast, target)) continue;
        const result = applyMobDamage({ id: def.id, typeName: def.name, level: def.level }, target, def.skill.damage);
        if (!result) continue;
        io.emit('world_boss_attack', {
          id: def.id, targetId: target.id, x: cast.x, y: cast.y,
          angle: cast.angle, skill: def.skill.id, dmg: result.dmg
        });
        if ((target.hp ?? 0) <= 0) {
          onPlayerDeath(target.id);
          io.emit('player_dead', { id: target.id });
        }
      }
      changed = true;
    }

    let target = null;
    let targetDistance = Infinity;
    for (const candidate of players.values()) {
      if (!isPlayerCombatEligible(candidate)) continue;
      const distance = Math.hypot((candidate.x || 0) - boss.x, (candidate.y || 0) - boss.y);
      if (distance < targetDistance && distance <= def.aggroRange) {
        target = candidate;
        targetDistance = distance;
      }
    }

    const previousX = boss.x;
    const previousY = boss.y;
    if (target) {
      boss.targetId = target.id;
      boss.aggroed = true;
      boss.angle = Math.atan2(target.y - boss.y, target.x - boss.x);
      if (boss.casting) {
        boss.state = 'attack';
      } else if (targetDistance > def.radius + 48) {
        const step = Math.min(targetDistance - def.radius - 48, def.speed * 0.05);
        boss.x += Math.cos(boss.angle) * step;
        boss.y += Math.sin(boss.angle) * step;
        boss.state = 'walk';
      } else {
        boss.state = now < boss.attackUntil ? 'attack' : 'idle';
        if (now - boss.lastAttackAt >= def.attackCooldownMs) {
          boss.lastAttackAt = now;
          boss.attackUntil = now + 520;
          boss.state = 'attack';
          const result = applyMobDamage({ id: def.id, typeName: def.name, level: def.level }, target, def.damage);
          if (result) {
            io.emit('world_boss_attack', {
              id: def.id, targetId: target.id, x: boss.x, y: boss.y,
              angle: boss.angle, dmg: result.dmg
            });
            if ((target.hp ?? 0) <= 0) {
              onPlayerDeath(target.id);
              io.emit('player_dead', { id: target.id });
            }
          }
        }
      }

      if (!boss.casting && now >= boss.nextSkillAt && targetDistance <= def.aggroRange * 0.75) {
        const skill = def.skill;
        boss.casting = {
          type: skill.type, x: skill.type === 'circle' ? target.x : boss.x,
          y: skill.type === 'circle' ? target.y : boss.y,
          angle: boss.angle, radius: skill.radius || 0, length: skill.length || 0,
          endsAt: now + skill.telegraphMs
        };
        boss.nextSkillAt = now + skill.cooldownMs;
        boss.state = 'attack';
        io.emit('world_boss_telegraph', {
          id: def.id, x: boss.casting.x, y: boss.casting.y,
          startTime: now, dur: skill.telegraphMs, color: skill.color,
          skillType: skill.type, skillName: skill.name, bossType: def.id,
          radius: skill.radius, length: skill.length, angle: boss.angle
        });
      }
    } else {
      boss.aggroed = false;
      boss.targetId = null;
      boss.casting = null;
      const dx = boss.homeX - boss.x;
      const dy = boss.homeY - boss.y;
      const distance = Math.hypot(dx, dy);
      if (distance > 2) {
        const step = Math.min(distance, def.speed * 0.035);
        boss.angle = Math.atan2(dy, dx);
        boss.x += dx / distance * step;
        boss.y += dy / distance * step;
        boss.state = 'walk';
      } else {
        boss.state = 'idle';
      }
    }
    boss.vx = (boss.x - previousX) / 0.05;
    boss.vy = (boss.y - previousY) / 0.05;
    for (let pass = 0; pass < 2; pass++) {
      for (const building of nearbyBuildings(boss.x, boss.y, def.radius + 120)) {
        if (!building || (building.hp ?? 100) <= 0 || building.type === 5) continue;
        resolveStaticCircleCollision(boss, def.radius, building.x, building.y, buildingCollisionRadius(building), { x: previousX, y: previousY });
      }
    }
    boss.x = Math.max(-6800, Math.min(6800, boss.x));
    boss.y = Math.max(-6800, Math.min(6800, boss.y));
    boss.vx = (boss.x - previousX) / 0.05;
    boss.vy = (boss.y - previousY) / 0.05;
    if (Math.abs(boss.x - previousX) > 0.01 || Math.abs(boss.y - previousY) > 0.01) changed = true;
  }

  if (changed || now - lastWorldBossBroadcastAt >= 100) {
    broadcastWorldBossStates(true);
    lastWorldBossBroadcastAt = now;
  }
}, 50).unref();

io.engine.on('connection_error', (err) => {
  const details = err?.message || 'unknown socket.io engine error';
  console.warn('[Socket.IO] engine connection error:', details);
});

function compactState(state, full = false) {
  const score = Number(state.score ?? state.sc ?? 0) || 0;
  const pLvl = calculatePlayerLevel(state);
  const helmetItemStats = state.helmetSkin ? getHelmetItemStats(state.helmetSkin) : null;
  const hpTheme = helmetItemStats?.hpTheme || '';
  const res = {
    x: Math.round((state.x || 0) * 10) / 10, y: Math.round((state.y || 0) * 10) / 10,
    a: state.angle !== undefined ? Math.round(state.angle * 100) / 100 : 0, hp: state.hp ?? 100, mhp: state.maxHp ?? 100, w: state.weapon || 1,
    atk: Boolean(state.isAttacking), atp: Number(state.attackTimer) || 0, atd: Number(state.attackDuration) || 0, k: state.kills || 0, xp: state.xp || 0, g: state.gold || 0,
    sc: score, at: state.axeTier || 0, st: state.swordTier || 0, rk: state.visualRankId ?? Math.min(11, Number(state.rankId) || 0),
    lvl: pLvl, level: pLvl, mlvl: Number(state.meleeLevel || 1), dlvl: Number(state.defenceLevel || 1),
    vx: state.vx ? Math.round(state.vx * 10) / 10 : 0, vy: state.vy ? Math.round(state.vy * 10) / 10 : 0,
    bx: typeof state.buildX === 'number' ? Math.round(state.buildX) : null, by: typeof state.buildY === 'number' ? Math.round(state.buildY) : null,
    sq: state.stateSeq || 0, tm: state.stateAt || Date.now(), tp: state.teleportSeq || 0,
    trappedBy: state.trappedBy || null, trappedX: state.trappedX ?? null, trappedY: state.trappedY ?? null,
    bt: Boolean(state.isBot),
    axeSkin: state.axeSkin || state.acc?.b || null,
    swordSkin: state.swordSkin || state.acc?.w || null,
    scytheId: state.scytheId || (state.swordSkin && String(state.swordSkin).startsWith('scythe_') ? state.swordSkin : null),
    helmetSkin: state.helmetSkin || state.acc?.h || null,
    hpTheme: hpTheme
  };
  if (full) {
    res.n = state.name || 'Oyuncu';
    res.sk = state.skin || 'default';
    res.skinAsset = cosmeticAssetForSkin(state.skin);
    res.color = state.color || '#8B5E3A';
    res.team = state.team || '';
    res.clanId = state.clanId || '';
    res.clanTag = state.clanTag || '';
    res.acc = state.acc || {};
    res.profileCosmetics = state.profileCosmetics || null;
  }
  return res;
}

function compactFullState(state) {
  return compactState(state, true);
}

function compactStateCompressed(state) {
  if (!state) return null;
  const isAtk = Boolean(state.isAttacking || (state.attackUntil && state.attackUntil > Date.now()));
  const pLvl = calculatePlayerLevel(state);
  return {
    x: Math.round((Number(state.x) || 0) * 10) / 10,
    y: Math.round((Number(state.y) || 0) * 10) / 10,
    a: Number.isFinite(Number(state.angle)) ? Math.round(Number(state.angle) * 100) / 100 : 0,
    hp: Number(state.hp ?? 100),
    mhp: Number(state.maxHp ?? 100),
    w: Number(state.weapon || 1),
    bx: typeof state.buildX === 'number' ? Math.round(state.buildX) : null,
    by: typeof state.buildY === 'number' ? Math.round(state.buildY) : null,
    sq: Number(state.stateSeq || 0),
    tp: Number(state.teleportSeq || 0),
    vx: Math.round((Number(state.vx) || 0) * 10) / 10,
    vy: Math.round((Number(state.vy) || 0) * 10) / 10,
    atk: isAtk ? 1 : 0,
    bt: state.isBot ? 1 : 0,
    t: state.trappedBy ? 1 : 0,
    l: pLvl,
    lvl: pLvl,
    r: String(state.roomId || '')
  };
}

function stateSignature(state) {
  if (!state) return '';
  const payload = compactStateCompressed(state);
  if (!payload) return '';
  return compressedStateSignature(payload);
}

function compressedStateSignature(payload) {
  if (!payload) return '';
  return [
    payload.x, payload.y, payload.a, payload.hp, payload.mhp, payload.w, payload.sq,
    payload.bx, payload.by, payload.tp, payload.vx, payload.vy, payload.atk, payload.bt, payload.t, payload.r
  ].join('|');
}

function syncOwnerResourceCollector(owner, building, now = Date.now()) {
  if (!owner || !building || building.ownerId !== owner.id) return;
  if (Number(building.type) !== 10 || (building.hp ?? 100) <= 0) return;
  const lastCollect = Number(building._lastCollectAt || 0);
  if (now - lastCollect < 3000) return;
  building._lastCollectAt = now;
  const tierBoost = Math.max(0, Number(building.tier) || 0);
  const woodGain = 6 + tierBoost * 2;
  const stoneGain = 5 + tierBoost * 2;
  const goldGain = 2 + tierBoost;
  owner.wood = (owner.wood || 0) + woodGain;
  owner.stone = (owner.stone || 0) + stoneGain;
  owner.gold = (owner.gold || 0) + goldGain;
  owner.score = (owner.score || 0) + 18;
  if (owner._authUser) {
    owner._authUser.coins = (owner._authUser.coins || 0) + goldGain;
    owner._authUser.gold = owner._authUser.coins;
  }
  const socket = io.sockets.sockets.get(owner.id);
  if (socket && socket.connected) {
    socket.emit('self_state', {
      g: owner.gold,
      sc: owner.score,
      xp: owner.xp,
      wood: owner.wood,
      stone: owner.stone,
      apples: owner.apples,
      seq: owner.stateSeq || 0,
      x: owner.x,
      y: owner.y,
      hp: owner.hp,
      hpSeq: owner.hpSeq || 0,
      hpAt: owner.hpAt || Date.now()
    });
  }
}

function roomCellKey(x, y) {
  return `${Math.floor((Number(x) || 0) / 1800)},${Math.floor((Number(y) || 0) / 1800)}`;
}

function getRoomForPosition(x, y) {
  return `room:${roomCellKey(x, y)}`;
}

function ensureRoom(roomId) {
  if (!rooms.has(roomId)) rooms.set(roomId, new Set());
  return rooms.get(roomId);
}

function updatePlayerRoom(player) {
  if (!player) return null;
  const roomId = getRoomForPosition(player.x || 0, player.y || 0);
  if (player.roomId && rooms.get(player.roomId)?.has(player.id)) rooms.get(player.roomId).delete(player.id);
  player.roomId = roomId;
  ensureRoom(roomId).add(player.id);
  return roomId;
}

function nearbyRoomIds(x, y, radius = PLAYER_AOI_RADIUS) {
  const minCellX = Math.floor(((Number(x) || 0) - radius) / 1800);
  const maxCellX = Math.floor(((Number(x) || 0) + radius) / 1800);
  const minCellY = Math.floor(((Number(y) || 0) - radius) / 1800);
  const maxCellY = Math.floor(((Number(y) || 0) + radius) / 1800);
  const ids = new Set();
  for (let cx = minCellX; cx <= maxCellX; cx++) {
    for (let cy = minCellY; cy <= maxCellY; cy++) {
      ids.add(`room:${cx},${cy}`);
    }
  }
  return ids;
}

function getRoomMembers(roomId) {
  return [...(rooms.get(roomId) || [])].map(id => players.get(id)).filter(Boolean);
}

function validateCombatState(attacker, target, { allowTrapHit = false, rangeLimit = 160, damage = 0, requireAlive = true, validWeapon = null } = {}) {
  if (!attacker || !target) return false;
  if (requireAlive && ((attacker.hp ?? 0) <= 0 || (target.hp ?? 0) <= 0)) return false;
  const targetIsBot = Boolean(target.isBot);
  if (!targetIsBot && ((attacker.clanId && attacker.clanId === target.clanId) || (attacker.team && target.team && attacker.team === target.team))) return false;
  if (!pvpAllowed()) return false;
  if (!allowTrapHit && target.trappedBy) return false;
  if (validWeapon && Number(attacker.weapon ?? 1) !== Number(validWeapon)) return false;
  if (attacker.roomId && target.roomId && attacker.roomId !== target.roomId && !nearbyRoomIds(attacker.x || 0, attacker.y || 0, rangeLimit || 160).has(target.roomId)) return false;
  const dist = Math.hypot((Number(target.x) || 0) - (Number(attacker.x) || 0), (Number(target.y) || 0) - (Number(attacker.y) || 0));
  if (dist > rangeLimit) return false;
  if (!Number.isFinite(Number(damage)) || Number(damage) <= 0) return false;
  return true;
}

function validateTrapCapture(attacker, target, building) {
  if (!attacker || !target || !building) return false;
  if ((attacker.hp ?? 0) <= 0 || (target.hp ?? 0) <= 0) return false;
  if (building.type !== 6 || (building.hp ?? 0) <= 0 || building.ownerId === target.id) return false;
  if ((building.ownerId && building.ownerId !== attacker.id) && attacker.id !== target.id) return false;
  const dx = (Number(target.x) || 0) - (Number(building.x) || 0);
  const dy = (Number(target.y) || 0) - (Number(building.y) || 0);
  const radius = trapCaptureRadius(building, target.radius || 34);
  return dx * dx + dy * dy <= radius * radius;
}

function compactMobTick(mob) {
  return {
    id: mob.id,
    seq: mob.stateSeq || 0,
    ts: mob.stateAt || Date.now(),
    x: Math.round(mob.x),
    y: Math.round(mob.y),
    vx: Math.round((mob.vx || 0) * 10) / 10,
    vy: Math.round((mob.vy || 0) * 10) / 10,
    angle: mob.angle !== undefined ? Math.round(mob.angle * 100) / 100 : 0,
    hp: mob.hp,
    maxHp: mob.maxHp,
    lvl: mob.level || 1,
    level: mob.level || 1,
    shape: mob.shape || 'wolf',
    radius: mob.radius,
    state: mob.state || 'idle',
    hitFlash: mob.hitFlash || 0,
    enraged: Boolean(mob.isEnraged),
    isBoss: Boolean(mob.isBoss),
    isPeaceful: Boolean(mob.isPeaceful),
    typeName: mob.typeName || 'Canavar',
  };
}

function publicClan(clan) {
  return { id: clan.id, name: clan.name, tag: clan.tag, ownerId: clan.ownerId, ownerName: clan.ownerName,
    members: (clan.members || []).map(member => ({ id: member.id, name: member.name })) };
}

function getPublicClanList() {
  return Array.from(clans.values()).map(clan => ({
    id: clan.id,
    name: clan.name,
    tag: clan.tag,
    ownerId: clan.ownerId,
    ownerName: clan.ownerName || 'Bilinmiyor',
    memberCount: (clan.members || []).length,
    maxMembers: 20
  }));
}

function broadcastClanList() {
  io.emit('clan_list', getPublicClanList());
}

function emitClanUpdate(clan) {
  io.to(`clan:${clan.id}`).emit('clan_update', publicClan(clan));
}

function leaveClan(socket, notify = true) {
  const player = players.get(socket.id);
  const clanId = player?.clanId || socket.data.clanId;
  const clan = clanId ? clans.get(clanId) : null;
  if (!clan) return;
  clan.members = (clan.members || []).filter(member => member.id !== socket.id);
  socket.leave(`clan:${clan.id}`);
  if (clan.ownerId === socket.id) {
    clan.ownerId = clan.members[0]?.id || null;
    clan.ownerName = clan.members[0]?.name || null;
    if (!clan.ownerId) clans.delete(clan.id);
  }
  if (player) { player.clanId = ''; player.clanTag = ''; }
  socket.data.clanId = '';
  saveAccountData();
  if (clans.has(clan.id)) emitClanUpdate(clan);
  broadcastClanList();
  if (notify) socket.emit('clan_left');
}

function broadcastOnlineCount() {
  io.emit('online_count', io.engine.clientsCount);
}

function relayToOthers(socket, event, payload) {
  socket.broadcast.emit(event, payload);
}

const WORLD = 11200;
const BIOME_EDGE = 0.38;
const BIOME_BORDER = WORLD * BIOME_EDGE;
const LAND_RADIUS = WORLD * 0.94;
const PLAY_RADIUS = WORLD * 0.90;
const VILLAGE_SAFE_HALF = 820;
const VILLAGE_BUFFER_HALF = 1450;
const VILLAGE_SAFE_RADIUS = 820;
const VILLAGE_BUFFER_RADIUS = 1450;
const VILLAGE_RESOURCE_CLEARANCE = 240;
const VILLAGE_MOB_CLEARANCE = 180;
function isInsideSafeVillage(x, y) {
  const nx = Math.abs(Number(x) || 0);
  const ny = Math.abs(Number(y) || 0);
  return nx <= VILLAGE_SAFE_HALF && ny <= VILLAGE_SAFE_HALF;
}
function isInsideVillageBuffer(x, y, padding = 0) {
  const margin = Math.max(0, Number(padding) || 0);
  const nx = Math.abs(Number(x) || 0);
  const ny = Math.abs(Number(y) || 0);
  return nx <= VILLAGE_BUFFER_HALF + margin && ny <= VILLAGE_BUFFER_HALF + margin;
}

const VILLAGE_COLLIDERS = [
  // 1. Kadim Su Kuyusu
  { x: 0, y: 15, rad: 78, name: 'well' },
  // 2. Tudor Köy Evi
  { x: -470, y: -380, rad: 115, name: 'house_w' },
  { x: -370, y: -380, rad: 115, name: 'house_e' },
  // 3. Demirci Atölyesi
  { x: 370, y: -380, rad: 115, name: 'forge_w' },
  { x: 470, y: -380, rad: 115, name: 'forge_e' },
  // 4. Gezgin Tüccar Arabası
  { x: 410, y: 405, rad: 115, name: 'cart' },
  // 5. Gizemli İksir Büyücüsü
  { x: -410, y: 405, rad: 68, name: 'sorcerer' },
  // 6. Köy Çiftçisi
  { x: -240, y: -180, rad: 50, name: 'farmer' },
  // 7. Demirci Fıçıları
  { x: 230, y: -180, rad: 44, name: 'forge_barrels' },
  // 8. Pazar Fıçıları
  { x: 230, y: 250, rad: 42, name: 'market_barrels' }
];

// Village NPC locations for interaction
const VILLAGE_NPCS = [
  { x: 420, y: -380, rad: 180, name: 'blacksmith', title: 'Usta Demirci' },
  { x: -410, y: 405, rad: 100, name: 'sorcerer', title: 'İksir Büyücüsü' },
  { x: -240, y: -180, rad: 80, name: 'farmer', title: 'Köy Çiftçisi' },
  { x: 410, y: 405, rad: 140, name: 'merchant', title: 'Tüccar' }
];

function resolveVillageFenceCollision(entity, radius) {
  const FENCE = 750;
  const GATE_HALF = 90;
  const rad = Number(radius) || 35;
  if (Math.abs(entity.y - (-FENCE)) < rad && Math.abs(entity.x) >= GATE_HALF - rad) {
    if (entity.y < -FENCE) entity.y = -FENCE - rad;
    else entity.y = -FENCE + rad;
  }
  if (Math.abs(entity.y - FENCE) < rad && Math.abs(entity.x) >= GATE_HALF - rad) {
    if (entity.y > FENCE) entity.y = FENCE + rad;
    else entity.y = FENCE - rad;
  }
  if (Math.abs(entity.x - (-FENCE)) < rad && Math.abs(entity.y) >= GATE_HALF - rad) {
    if (entity.x < -FENCE) entity.x = -FENCE - rad;
    else entity.x = -FENCE + rad;
  }
  if (Math.abs(entity.x - FENCE) < rad && Math.abs(entity.y) >= GATE_HALF - rad) {
    if (entity.x > FENCE) entity.x = FENCE + rad;
    else entity.x = FENCE - rad;
  }
}

function getBeginnerVillageSpawn() {
  for (let attempt = 0; attempt < 30; attempt++) {
    const ang = Math.random() * Math.PI * 2;
    const dist = 95 + Math.random() * 180;
    const px = Math.round(Math.cos(ang) * dist);
    const py = Math.round(Math.sin(ang) * dist);
    const collides = VILLAGE_COLLIDERS.some(o => {
      const dx = px - o.x, dy = py - o.y;
      const minD = o.rad + 40;
      return (dx * dx + dy * dy) < (minD * minD);
    });
    if (!collides) return { x: px, y: py };
  }
  return { x: 0, y: 150 };
}
const AGE_GOLD_TABLE = [
  0, 300, 900, 2000, 4000, 7000, 11000, 17000, 25000, 40000, 65000,
  95000, 135000, 185000, 245000, 315000, 400000, 500000, 620000, 760000, 920000, 1100000
];
function calculatePlayerLevel(input) {
  let g = 0, sc = 0, k = 0;
  if (typeof input === 'object' && input !== null) {
    g = Math.max(0, Number(input.gold) || 0);
    sc = Math.max(0, Number(input.score ?? input.sc ?? input.xp ?? 0) || 0);
    k = Math.max(0, Number(input.kills) || 0);
  } else {
    g = Math.max(0, Number(input) || 0);
  }
  let lvl = 1;
  for (let i = 1; i < AGE_GOLD_TABLE.length; i++) {
    if (g >= AGE_GOLD_TABLE[i]) lvl = i + 1; else break;
  }
  if (g >= AGE_GOLD_TABLE[AGE_GOLD_TABLE.length - 1]) {
    const extra = g - AGE_GOLD_TABLE[AGE_GOLD_TABLE.length - 1];
    lvl = AGE_GOLD_TABLE.length + Math.floor(extra / 200000);
  }
  const scoreLvl = Math.floor(Math.sqrt(sc / 70)) + 1;
  const killLvl = Math.floor(k / 3) + 1;
  return Math.max(1, Math.min(100, Math.max(lvl, scoreLvl, killLvl)));
}

function calculateLevelGapMultiplier(attackerLevel, defenderLevel) {
  const aLvl = Math.max(1, Number(attackerLevel) || 1);
  const dLvl = Math.max(1, Number(defenderLevel) || 1);
  const diff = dLvl - aLvl; // Pozitifse savunucu (hedef) daha yüksek seviyeli

  if (diff <= 0) {
    return Math.min(1.6, 1 + Math.abs(diff) * 0.012);
  }

  return Math.max(0.12, Math.pow(0.82, diff));
}

const MAX_MOBS = 120;
const MOB_RADIUS = 36;
const MOB_AGGRO_RANGE = 550;
const MOB_SPEED = 18;
const MOB_WANDER_SPEED = 8;
const MOB_CHASE_TIMEOUT = 7000;
const MOB_REAGGRO_DELAY = 12000;
const MOB_MIN_SPAWN_SEPARATION = 180;
const MOB_GRID_CELL_SIZE = 500;
const MOB_AOI_RADIUS = 4200;
const PLAYER_AOI_RADIUS = 3000;
const PLAYER_GRID_CELL_SIZE = 500;
const MAX_PLAYER_SPEED = 1200;
const MAX_MOVE_DELTA_PER_TICK = 140;
function setMobTarget(mob, targetId, now = Date.now()) {
  if (mob.targetId !== targetId || !mob.chaseStartedAt) {
    mob.chaseStartedAt = now;
    mob.chaseUntil = now + MOB_CHASE_TIMEOUT;
  }
  mob.targetId = targetId;
}

const BUILD_ROLES = {
  tank: {
    label: 'Tank',
    title: 'Iron Warden',
    theme: 'heavy protector',
    flavor: 'Duraklı ve kalın, göğsünü öne çıkarır, savunmayı önceleyen bir koruyucu.',
    color: '#9aa6ff',
    maxHp: 1.18, damage: 0.96, armor: 1.18, speed: 0.92,
    perks: ['Kalkan dayanımı', 'Ön hat tutma', 'Yüksek savunma']
  },
  vanguard: {
    label: 'Vanguard',
    title: 'Sunforge Vanguard',
    theme: 'frontliner titan',
    flavor: 'En öndeki savunma duvarı; göğüs geriye dönmez, sahayı kapatır.',
    color: '#a8c5ff',
    maxHp: 1.22, damage: 1.02, armor: 1.28, speed: 0.9,
    perks: ['Frontline wall', 'Stagger hold', 'Shield break']
  },
  assassin: {
    label: 'Assassin',
    title: 'Shadow Fang',
    theme: 'silent predator',
    flavor: 'Sessiz, hızlı ve ani hasar vurur; hedefi minimum mesafede imha eder.',
    color: '#d8a1ff',
    maxHp: 0.92, damage: 1.18, armor: 0.9, speed: 1.14,
    perks: ['Ani burst', 'Mobility', 'Critical tempo']
  },
  viper: {
    label: 'Viper',
    title: 'Night Viper',
    theme: 'venom rush',
    flavor: 'Kısa mesafede ölümcül hızla gelir; rakibin direncini çabuk tüketir.',
    color: '#cdaeff',
    maxHp: 0.9, damage: 1.26, armor: 0.88, speed: 1.18,
    perks: ['Poison tempo', 'Critical burst', 'Shadow cut']
  },
  ranged: {
    label: 'Ranged',
    title: 'Horizon Lens',
    theme: 'long sight',
    flavor: 'Uzaktan baskı kurar, hasarı ve menzili öne çıkarır.',
    color: '#7dd3fc',
    maxHp: 0.96, damage: 1.1, armor: 0.96, speed: 1.02,
    perks: ['Menzil üstünlüğü', 'İsabet', 'Kontrol']
  },
  oracle: {
    label: 'Oracle',
    title: 'Astral Oracle',
    theme: 'prophecy caster',
    flavor: 'Menzili ve kontrolü bozan, yıldız gibi kesin bir düzen kurar.',
    color: '#97f0ff',
    maxHp: 0.95, damage: 1.15, armor: 0.97, speed: 1.04,
    perks: ['Star guidance', 'Pacing control', 'Precision burst']
  },
  support: {
    label: 'Support',
    title: 'Aegis Relic',
    theme: 'guardian healer',
    flavor: 'Takımın ayakta kalmasını sağlar, savunma ve desteği öne çıkarır.',
    color: '#7ef0c3',
    maxHp: 1.06, damage: 0.94, armor: 1.04, speed: 1.0,
    perks: ['Heal pulse', 'Shield sustain', 'Utility']
  },
  trap: {
    label: 'Trap Master',
    title: 'Snare Warden',
    theme: 'field control',
    flavor: 'Tuzak kurup alanı kontrol eder; rakibin hareketini keser.',
    color: '#f9c66b',
    maxHp: 1.02, damage: 1.0, armor: 1.12, speed: 0.96,
    perks: ['Trap efficiency', 'Area denial', 'Tempo control']
  },
  warden: {
    label: 'Warden',
    title: 'Gale Warden',
    theme: 'field anchor',
    flavor: 'Alanı kontrol eder, tuzak ve zemin baskısını barındırır.',
    color: '#f6d87a',
    maxHp: 1.08, damage: 1.08, armor: 1.16, speed: 0.98,
    perks: ['Control field', 'Zone lockdown', 'Stall tempo']
  },
  berserker: {
    label: 'Berserker',
    title: 'Warfang Rage',
    theme: 'rage rush',
    flavor: 'Riskli ama yıkıcı bir saldırı profili; yakın dövüşte en tehlikelidir.',
    color: '#ff7d6b',
    maxHp: 0.9, damage: 1.24, armor: 0.82, speed: 1.08,
    perks: ['Burst damage', 'Aggro pressure', 'High risk tempo']
  }
};
const BUILD_HELMETS = {
  guardian: {
    label: 'Guardian',
    title: 'Stone Guardian',
    style: 'fortified',
    flavor: 'Kalın metal kask, dayanıklılık ve hiddet dengesini sağlar.',
    color: '#a5b4fc',
    maxHp: 1.12, damage: 0.94, armor: 1.2, speed: 0.96,
    rarity: 'Epic'
  },
  aegis: {
    label: 'Aegis',
    title: 'Sunfall Aegis',
    style: 'solar guard',
    flavor: 'Güneşi taşıyan koruyucu başlık; en sağlam bloklayıcı zırh profiline aittir.',
    color: '#ffe09a',
    maxHp: 1.18, damage: 0.98, armor: 1.3, speed: 0.94,
    rarity: 'Mythic'
  },
  phantom: {
    label: 'Phantom',
    title: 'Night Phantom',
    style: 'silent assassin',
    flavor: 'Hafif ama ölümcül; düşman önüne sessizce gelir.',
    color: '#d8b8ff',
    maxHp: 0.9, damage: 1.18, armor: 0.9, speed: 1.16,
    rarity: 'Legendary'
  },
  voidveil: {
    label: 'Voidveil',
    title: 'Moon Voidveil',
    style: 'shadow dusk',
    flavor: 'Geceye bürünmüş görünüm; sessizlik ve ölümcül ritim verir.',
    color: '#b9a7ff',
    maxHp: 0.88, damage: 1.22, armor: 0.88, speed: 1.2,
    rarity: 'Mythic'
  },
  ranger: {
    label: 'Ranger',
    title: 'Horizon Ranger',
    style: 'longview elite',
    flavor: 'Gözlem ve menzil odaklı, uzaktan savaşın kralı gibi durur.',
    color: '#7dd3fc',
    maxHp: 0.98, damage: 1.1, armor: 0.96, speed: 1.08,
    rarity: 'Epic'
  },
  sunflare: {
    label: 'Sunflare',
    title: 'Solar Crown',
    style: 'flare x-ray',
    flavor: 'Işık dalgaları taşıyan başlık; menzili ve hedefleme gücünü yükseltir.',
    color: '#ffcc7a',
    maxHp: 0.96, damage: 1.15, armor: 0.96, speed: 1.12,
    rarity: 'Mythic'
  },
  relic: {
    label: 'Relic',
    title: 'Aegis Relic',
    style: 'sacred ward',
    flavor: 'Kutsal ışıkla çevrili, koruyucu ve destek odaklı bir başlık.',
    color: '#7ef0c3',
    maxHp: 1.08, damage: 0.96, armor: 1.1, speed: 0.98,
    rarity: 'Epic'
  },
  frostcrown: {
    label: 'Frostcrown',
    title: 'Frostveil Crown',
    style: 'cryo discipline',
    flavor: 'Buzdan bir kılıçla kesilen soğuk hedefleme ve kontrollü savunma sağlar.',
    color: '#b2f0ff',
    maxHp: 1.06, damage: 1.1, armor: 1.12, speed: 1.0,
    rarity: 'Mythic'
  },
  trapper: {
    label: 'Trapper',
    title: 'Snare Trapper',
    style: 'mechanic warden',
    flavor: 'Mekanik tasarım, tuzak ve alan kontrolü için hazırlanmış.',
    color: '#fbbf24',
    maxHp: 1.02, damage: 1.06, armor: 1.08, speed: 0.94,
    rarity: 'Rare'
  },
  warfang: {
    label: 'Warfang',
    title: 'Warfang Crown',
    style: 'battle fury',
    flavor: 'Yırtıcı ve sert görünüm, en agresif savaşçılara uygun bir başlık.',
    color: '#ff8a65',
    maxHp: 0.88, damage: 1.26, armor: 0.84, speed: 1.1,
    rarity: 'Legendary'
  }
};
const LOADOUT_SETS = {
  sunforge: {
    label: 'Sunforge Set',
    theme: 'radiant frontliner',
    flavor: 'Güneşin ilk ışığı gibi baskı kurar; takımın önünde duran bir zırh setidir.',
    bonus: 'Savunma +12%, hasar +6%'
  },
  abyss: {
    label: 'Abyssal Set',
    theme: 'deep kill rhythm',
    flavor: 'Karanlığın içinde hareket eder; yakalanan hedefi çok hızlı düşürür.',
    bonus: 'Hız +10%, kritik +9%'
  },
  aurora: {
    label: 'Aurora Set',
    theme: 'luminous tempo',
    flavor: 'Parıltılı duruşu ve nazik görünümüyle hem kontrol hem baskı sağlar.',
    bonus: 'Kontrol +11%, tempo +7%'
  },
  tempest: {
    label: 'Tempest Set',
    theme: 'storm rush',
    flavor: 'Rüzgar gibi gelir, çarpma anında yıkıcı olur.',
    bonus: 'Hasar +14%, manevra +8%'
  },
  dawn: {
    label: 'Dawn Oath Set',
    theme: 'purity guardian',
    flavor: 'Ciddi bir koruyucu görselliği; takımın ayakta kalmasını sağlar.',
    bonus: 'Can +9%, kalkan +12%'
  }
};
const WEAPON_DEFINITIONS = {
  sword: { label: 'Sword', title: 'Velvet Edge', style: 'balanced duelist', damage: 1.08, range: 1.0, speed: 1.04, notes: 'Dengeli ve net hasar.' },
  axe: { label: 'Axe', title: 'Storm Cleaver', style: 'heavy breaker', damage: 1.22, range: 0.92, speed: 0.8, notes: 'Yüksek hasar, yüksek risk.' },
  spear: { label: 'Spear', title: 'Thorn Reach', style: 'control lance', damage: 1.1, range: 1.18, speed: 0.94, notes: 'Uzak kontrol ve giriş baskısı.' },
  bow: { label: 'Bow', title: 'Horizon String', style: 'range sniper', damage: 1.12, range: 1.26, speed: 0.9, notes: 'Menzil ve isabet üstünlüğü.' },
  crossbow: { label: 'Crossbow', title: 'Iron Verdict', style: 'heavy piercer', damage: 1.18, range: 1.2, speed: 0.72, notes: 'Yavaş ama yıkıcı.' },
  hammer: { label: 'Hammer', title: 'Vault Breaker', style: 'stun crusher', damage: 1.24, range: 0.9, speed: 0.7, notes: 'Yüksek stun ve ağır vurma.' },
  scythe: { label: 'Scythe', title: 'Reaper Arc', style: 'area sweeper', damage: 1.16, range: 1.05, speed: 0.82, notes: 'Alan kontrolü ve ters dönüş.' },
  staff: { label: 'Staff', title: 'Moon Weave', style: 'support caster', damage: 0.96, range: 1.1, speed: 1.0, notes: 'Destek, kontrol ve düzen.' },
  chakram: { label: 'Chakram', title: 'Aether Ring', style: 'arc thrower', damage: 1.08, range: 1.15, speed: 1.08, notes: 'Dönüşlü ve hızlı hasar.' },
  trapblade: { label: 'Trap Blade', title: 'Snare Fang', style: 'field trap', damage: 1.1, range: 1.04, speed: 0.9, notes: 'Tuzak ve alan baskısı.' },
  halberd: { label: 'Halberd', title: 'Gale Reach', style: 'reach finisher', damage: 1.14, range: 1.22, speed: 0.88, notes: 'Uzun menzil ve net giriş.' },
  dagger: { label: 'Dagger', title: 'Ghost Piercer', style: 'rush finisher', damage: 1.08, range: 0.84, speed: 1.2, notes: 'Hızlı burst ve çabuk öldürme.' },
  runeblade: { label: 'Rune Blade', title: 'Astral Sigil', style: 'arcane duelist', damage: 1.18, range: 1.02, speed: 1.04, notes: 'Büyülü hasar ve tekniği güçlü.' },
  wand: { label: 'Wand', title: 'Nova Scepter', style: 'spell anchor', damage: 1.0, range: 1.18, speed: 0.96, notes: 'Kontrol ve etkili destek.' },
  shotgun: { label: 'Shotgun', title: 'Bloom Breaker', style: 'close burst', damage: 1.22, range: 0.86, speed: 0.75, notes: 'Yakın mesafede devasa patlama.' },
  voidblade: { label: 'Voidblade', title: 'Null Eclipse', style: 'shadow edge', damage: 1.28, range: 1.08, speed: 1.12, notes: 'Karanlık enerjiyle kesen ölümcül bir kılıç.' },
  sunflare: { label: 'Sunflare', title: 'Helios Lash', style: 'solar cutter', damage: 1.3, range: 1.16, speed: 0.98, notes: 'Yüksek parlaklık ve baskı odaklı hasar.' },
  frostglaive: { label: 'Frost Glaive', title: 'Glacier Reach', style: 'ice control', damage: 1.18, range: 1.28, speed: 0.84, notes: 'Soğuk menzil ve kontrollü engeller.' },
  stormcannon: { label: 'Storm Cannon', title: 'Skybreaker', style: 'heavy artillery', damage: 1.34, range: 1.24, speed: 0.7, notes: 'Ağır, yüksek patlama hasarı.' },
  moonpiercer: { label: 'Moonpiercer', title: 'Lunar Fang', style: 'astral lance', damage: 1.2, range: 1.32, speed: 0.92, notes: 'Ay ışığı gibi net ve uzun menzilli vurum.' }
};
const HELMET_ITEM_STATS = Object.freeze({
  helmet_aegis: {
    maxHpBonus: 120,
    maxHp: 1.40,
    armor: 1.35,
    damage: 0.98,
    speed: 0.92,
    attackSpeed: 1.0,
    harvestMult: 1.0,
    windmillMult: 1.0,
    hpTheme: 'aegis'
  },
  helmet_phantom: {
    maxHpBonus: 0,
    maxHp: 0.90,
    armor: 0.88,
    damage: 1.20,
    speed: 1.18,
    attackSpeed: 1.10,
    harvestMult: 1.0,
    windmillMult: 1.0,
    hpTheme: 'phantom'
  },
  helmet_voidveil: {
    maxHpBonus: 0,
    maxHp: 0.85,
    armor: 0.85,
    damage: 1.25,
    speed: 1.22,
    attackSpeed: 1.15,
    harvestMult: 1.0,
    windmillMult: 1.0,
    hpTheme: 'voidveil'
  },
  helmet_ranger: {
    maxHpBonus: 20,
    maxHp: 1.0,
    armor: 0.95,
    damage: 1.12,
    speed: 1.10,
    attackSpeed: 1.05,
    harvestMult: 1.0,
    windmillMult: 1.0,
    hpTheme: 'ranger'
  },
  helmet_sunflare: {
    maxHpBonus: 0,
    maxHp: 0.95,
    armor: 0.94,
    damage: 1.18,
    speed: 1.14,
    attackSpeed: 1.08,
    harvestMult: 1.0,
    windmillMult: 1.0,
    hpTheme: 'sunflare'
  },
  helmet_druid: {
    maxHpBonus: 40,
    maxHp: 1.10,
    armor: 1.12,
    damage: 0.95,
    speed: 0.98,
    attackSpeed: 1.0,
    harvestMult: 1.50,
    windmillMult: 1.50,
    regenBonus: 3,
    hpTheme: 'druid'
  },
  helmet_frostcrown: {
    maxHpBonus: 30,
    maxHp: 1.08,
    armor: 1.15,
    damage: 1.12,
    speed: 1.0,
    attackSpeed: 1.05,
    harvestMult: 1.0,
    windmillMult: 1.0,
    hpTheme: 'frostcrown'
  },
  helmet_trapper: {
    maxHpBonus: 20,
    maxHp: 1.05,
    armor: 1.10,
    damage: 1.08,
    speed: 0.94,
    attackSpeed: 1.0,
    harvestMult: 1.0,
    windmillMult: 1.0,
    hpTheme: 'trapper'
  },
  helmet_warfang: {
    maxHpBonus: 0,
    maxHp: 0.88,
    armor: 0.82,
    damage: 1.28,
    speed: 1.12,
    attackSpeed: 1.12,
    harvestMult: 1.0,
    windmillMult: 1.0,
    hpTheme: 'warfang'
  },
  helmet_cehennem: {
    maxHpBonus: 0,
    maxHp: 0.95,
    armor: 0.90,
    damage: 1.32,
    speed: 1.05,
    attackSpeed: 1.12,
    burnEffect: true,
    harvestMult: 1.0,
    windmillMult: 1.0,
    hpTheme: 'cehennem'
  },
  helmet_ejderha: {
    maxHpBonus: 50,
    maxHp: 1.15,
    armor: 1.18,
    damage: 1.22,
    speed: 1.0,
    attackSpeed: 1.08,
    critChance: 0.25,
    critMultiplier: 1.75,
    harvestMult: 1.0,
    windmillMult: 1.0,
    hpTheme: 'ejderha'
  },
  helmet_necromancer: {
    maxHpBonus: 0,
    maxHp: 0.95,
    armor: 0.95,
    damage: 1.15,
    speed: 1.05,
    attackSpeed: 1.15,
    lifesteal: 0.15,
    killHeal: 25,
    harvestMult: 1.0,
    windmillMult: 1.0,
    hpTheme: 'necromancer'
  },
  helmet_cyber: {
    maxHpBonus: 0,
    maxHp: 0.95,
    armor: 0.95,
    damage: 1.10,
    speed: 1.18,
    attackSpeed: 1.25,
    harvestMult: 1.0,
    windmillMult: 1.0,
    hpTheme: 'cyber'
  }
});
const SCYTHE_ITEM_STATS = Object.freeze({
  scythe_tier_1: { damage: 1.03, attackSpeed: 1.02 },
  scythe_tier_2: { damage: 1.06, attackSpeed: 1.07, speed: 1.03 },
  scythe_tier_3: { damage: 1.12, attackSpeed: 0.97, speed: 1.01 },
  scythe_tier_4: { damage: 1.07, attackSpeed: 1.05, dash: 1.18 },
  scythe_tier_5: { damage: 1.04, attackSpeed: 1.08, speed: 1.12 },
  scythe_tier_6: { damage: 1.1, attackSpeed: 1.1, speed: 1.05 },
  scythe_tier_7: { damage: 1.16, attackSpeed: 1.08, dash: 1.08, speed: 1.02 },
  scythe_tier_8: { damage: 1.2, attackSpeed: 1.14, dash: 1.12, speed: 1.04 }
});
const SCYTHE_SHOP_PRICES = Object.freeze({
  scythe_tier_1: 120,
  scythe_tier_2: 240,
  scythe_tier_3: 420,
  scythe_tier_4: 680,
  scythe_tier_5: 1040,
  scythe_tier_6: 1520,
  scythe_tier_7: 2200,
  scythe_tier_8: 3200
});
const ITEM_HELMET_ALIAS_MAP = Object.freeze({
  helmet_aegis: 'aegis',
  helmet_phantom: 'phantom',
  helmet_voidveil: 'voidveil',
  helmet_ranger: 'ranger',
  helmet_sunflare: 'sunflare',
  helmet_druid: 'relic',
  helmet_frostcrown: 'frostcrown',
  helmet_trapper: 'trapper',
  helmet_warfang: 'warfang',
  helmet_cehennem: 'warfang',
  helmet_ejderha: 'aegis',
  helmet_necromancer: 'voidveil',
  helmet_cyber: 'phantom'
});
function normalizeItemKey(value) {
  return String(value || '').trim().toLowerCase().replace(/[^a-z0-9]+/g, '_').replace(/^_+|_+$/g, '');
}
function getHelmetItemStats(helmetValue) {
  const key = normalizeItemKey(helmetValue);
  return HELMET_ITEM_STATS[key] || null;
}
function getScytheItemStats(scytheValue) {
  const key = normalizeItemKey(scytheValue);
  return SCYTHE_ITEM_STATS[key] || null;
}
const mobGrid = new Map();
const playerGrid = new Map();

function mobCellKey(x, y) {
  return `${Math.floor(x / MOB_GRID_CELL_SIZE)},${Math.floor(y / MOB_GRID_CELL_SIZE)}`;
}

function rebuildMobGrid() {
  mobGrid.clear();
  for (const mob of mobs.values()) {
    const key = mobCellKey(mob.x, mob.y);
    const bucket = mobGrid.get(key);
    if (bucket) bucket.push(mob);
    else mobGrid.set(key, [mob]);
  }
}

function nearbyMobs(x, y, radius) {
  const minCellX = Math.floor((x - radius) / MOB_GRID_CELL_SIZE);
  const maxCellX = Math.floor((x + radius) / MOB_GRID_CELL_SIZE);
  const minCellY = Math.floor((y - radius) / MOB_GRID_CELL_SIZE);
  const maxCellY = Math.floor((y + radius) / MOB_GRID_CELL_SIZE);
  const result = [];
  const radiusSquared = radius * radius;
  for (let cellX = minCellX; cellX <= maxCellX; cellX++) {
    for (let cellY = minCellY; cellY <= maxCellY; cellY++) {
      const bucket = mobGrid.get(`${cellX},${cellY}`);
      if (!bucket) continue;
      for (const mob of bucket) {
        const dx = mob.x - x, dy = mob.y - y;
        if (dx * dx + dy * dy <= radiusSquared) result.push(mob);
      }
    }
  }
  return result;
}

function playerCellKey(x, y) {
  return `${Math.floor(x / PLAYER_GRID_CELL_SIZE)},${Math.floor(y / PLAYER_GRID_CELL_SIZE)}`;
}

function rebuildPlayerGrid() {
  playerGrid.clear();
  for (const player of players.values()) {
    if (!player || (player.hp ?? 0) <= 0) continue;
    const key = playerCellKey(player.x, player.y);
    const bucket = playerGrid.get(key);
    if (bucket) bucket.push(player);
    else playerGrid.set(key, [player]);
  }
}

function nearbyPlayers(x, y, radius, excludeId = null) {
  const radiusSquared = radius * radius;
  const minCellX = Math.floor((x - radius) / PLAYER_GRID_CELL_SIZE);
  const maxCellX = Math.floor((x + radius) / PLAYER_GRID_CELL_SIZE);
  const minCellY = Math.floor((y - radius) / PLAYER_GRID_CELL_SIZE);
  const maxCellY = Math.floor((y + radius) / PLAYER_GRID_CELL_SIZE);
  const result = [];
  const seen = new Set();
  for (let cellX = minCellX; cellX <= maxCellX; cellX++) {
    for (let cellY = minCellY; cellY <= maxCellY; cellY++) {
      const bucket = playerGrid.get(`${cellX},${cellY}`);
      if (!bucket) continue;
      for (const player of bucket) {
        if (!player || player.id === excludeId || (player.hp ?? 0) <= 0) continue;
        if (seen.has(player.id)) continue;
        const dx = (player.x || 0) - x;
        const dy = (player.y || 0) - y;
        if (dx * dx + dy * dy <= radiusSquared) {
          seen.add(player.id);
          result.push(player);
        }
      }
    }
  }
  return result;
}

function syncMobVisibility(changed = []) {
  rebuildMobGrid();
  for (const [id, player] of players) {
    const socket = io.sockets.sockets.get(id);
    if (!socket || !player.visibleMobIds) continue;
    const visibleMobs = nearbyMobs(player.x, player.y, MOB_AOI_RADIUS);
    const nextIds = new Set(visibleMobs.map(mob => mob.id));
    for (const mob of visibleMobs) {
      if (!player.visibleMobIds.has(mob.id)) socket.emit('mob_spawn', publicMob(mob));
    }
    for (const mobId of player.visibleMobIds) {
      if (!nextIds.has(mobId)) socket.emit('mob_despawn', { id: mobId, ts: Date.now() });
    }
    player.visibleMobIds = nextIds;
    const visibleChanged = changed.filter(mob => nextIds.has(mob.id));
    if (visibleChanged.length) socket.volatile.emit('mob_states', visibleChanged);
  }
}

function _makeMulberry32(seed) {
  return function() {
    seed |= 0; seed = (seed + 0x6D2B79F5) | 0;
    let t = Math.imul(seed ^ (seed >>> 15), 1 | seed);
    t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

const serverObstacles = [];
const obstacleGrid = new Map();
const OBSTACLE_CELL_SIZE = 180;
const MAX_RESOURCE_COLLISION_RADIUS = 224 * 0.96;
const SPECIAL_WORLD_MINERALS = Object.freeze([
  // 4 Diamond Nodes
  { id: 'sp-diamond-0', type: 'diamond', name: '💎 Elmas Cevheri', x: 2100,  y: -1200, radius: 112, hp: 3500, maxHp: 3500, yG: 120, yS: 35, yXp: 80, biome: 'forest' },
  { id: 'sp-diamond-1', type: 'diamond', name: '💎 Elmas Cevheri', x: -1600, y: -4200, radius: 112, hp: 3500, maxHp: 3500, yG: 120, yS: 35, yXp: 80, biome: 'winter' },
  { id: 'sp-diamond-2', type: 'diamond', name: '💎 Elmas Cevheri', x: 4800,  y: -800,  radius: 112, hp: 3500, maxHp: 3500, yG: 120, yS: 35, yXp: 80, biome: 'desert' },
  { id: 'sp-diamond-3', type: 'diamond', name: '💎 Elmas Cevheri', x: -2400, y: 3800,  radius: 112, hp: 3500, maxHp: 3500, yG: 120, yS: 35, yXp: 80, biome: 'lava' },

  // 2 Amethyst Nodes
  { id: 'sp-amethyst-0', type: 'amethyst', name: '🔮 Ametist Cevheri', x: 2800, y: -4600, radius: 128, hp: 5500, maxHp: 5500, yG: 250, yS: 60, yXp: 200, biome: 'winter' },
  { id: 'sp-amethyst-1', type: 'amethyst', name: '🔮 Ametist Cevheri', x: 3200, y: 4400,  radius: 128, hp: 5500, maxHp: 5500, yG: 250, yS: 60, yXp: 200, biome: 'lava' },

  // 1 Redite Node
  { id: 'sp-redite-0',   type: 'redite',   name: '👑 Kadim Redite Cevheri', x: -3600, y: 5600, radius: 148, hp: 9000, maxHp: 9000, yG: 600, yS: 150, yXp: 500, biome: 'lava' }
]);

const SERVER_RESOURCE_COLLISION_FRACTIONS = Object.freeze({
  wood: 0.65, stone: 0.82, gold: 0.8, apple: 0.65,
  bush: 0.6, mushroom: 0.55, crystal: 0.6, hive: 0.58,
  diamond: 0.82, amethyst: 0.84, redite: 0.86
});
function obstacleCellKey(x, y) {
  return `${Math.floor(x / OBSTACLE_CELL_SIZE)},${Math.floor(y / OBSTACLE_CELL_SIZE)}`;
}
function nearbyServerObstacles(x, y, radius) {
  const minCellX = Math.floor((x - radius) / OBSTACLE_CELL_SIZE);
  const maxCellX = Math.floor((x + radius) / OBSTACLE_CELL_SIZE);
  const minCellY = Math.floor((y - radius) / OBSTACLE_CELL_SIZE);
  const maxCellY = Math.floor((y + radius) / OBSTACLE_CELL_SIZE);
  const nearby = [];
  for (let cellX = minCellX; cellX <= maxCellX; cellX++) {
    for (let cellY = minCellY; cellY <= maxCellY; cellY++) {
      const bucket = obstacleGrid.get(`${cellX},${cellY}`);
      if (bucket) nearby.push(...bucket);
    }
  }
  return nearby;
}
function publicMob(mob) {
  return {
    id: mob.id, x: Math.round(mob.x), y: Math.round(mob.y), vx: Math.round(mob.vx * 10) / 10,
    vy: Math.round(mob.vy * 10) / 10, angle: mob.angle !== undefined ? Math.round(mob.angle * 100) / 100 : 0,
    seq: mob.stateSeq || 0,
    ts: mob.stateAt || Date.now(),
    hp: mob.hp, maxHp: mob.maxHp, radius: mob.radius,
    lvl: mob.level || 1, level: mob.level || 1,
    color: mob.color, outline: mob.outline, shape: mob.shape, eyes: mob.eyes,
    typeName: mob.typeName, dmg: mob.dmg, xpReward: mob.xpReward, goldReward: mob.goldReward,
    state: mob.state || 'idle',
    enraged: Boolean(mob.isEnraged),
    isBoss: Boolean(mob.isBoss),
    isPeaceful: Boolean(mob.isPeaceful),
  };
}

function applyMobSpikeDamage(mob, spike, now) {
  if (!mob || !spike || Number(spike.type) !== 3 || (spike.hp ?? 0) <= 0) return false;
  const owner = players.get(spike.ownerId || spike._ownerId);
  if (owner) return applySpikeDamageToMob(mob, spike, owner, now);
  if (now - (mob.lastSpikeHitAt || 0) < 420) return false;
  mob.lastSpikeHitAt = now;
  const tier = Math.max(0, Math.min(5, Number(spike.tier) || 0));
  const baseDamage = [45, 75, 110, 160, 220, 300][tier] || 45;
  const damage = mob.isBoss ? Math.min(baseDamage, Math.ceil(mob.maxHp / 18)) : baseDamage;
  mob.hp = Math.max(0, mob.hp - damage);
  mob.stateSeq = (mob.stateSeq || 0) + 1;
  broadcastMobEventNear(mob, 'mob_update', { id: mob.id, seq: mob.stateSeq, ts: now, hp: mob.hp, maxHp: mob.maxHp, hitFlash: 8 });
  if (mob.hp <= 0) {
    mobs.delete(mob.id);
    const ownerId = spike.ownerId || spike._ownerId;
    broadcastMobEventNear(mob, 'mob_dead', { id: mob.id, killerId: ownerId });
    const owner = players.get(ownerId);
    if (owner) {
      const rewardGold = Math.max(1, Math.floor((mob.goldReward || 10) * 0.65));
      owner.gold = (owner.gold || 0) + rewardGold;
      owner.score = (owner.score || 0) + rewardGold * 3;
      persistPlayerScore(owner);
      awardLoot(owner, mob.level || mob.lvl || 1, Boolean(mob.isBoss));
    }
  }
  return true;
}

const PREVIEW_RESOURCE_DEFS = {
  forest: [
    { type: 'wood', model: 'brawlStar',   w: 28, radius: 205, hp: 750 },
    { type: 'wood', model: 'pine',        w: 24, radius: 190, hp: 650 },
    { type: 'wood', model: 'classic',     w: 16, radius: 176, hp: 550 },
    { type: 'wood', model: 'hollowLog',   w: 10, radius: 160, hp: 500 },
    { type: 'wood', model: 'log',         w: 9,  radius: 150, hp: 450 },
    { type: 'wood', model: 'stump',       w: 8,  radius: 145, hp: 400 },
    { type: 'wood', model: 'lumberStack', w: 7,  radius: 150, hp: 520 },
    { type: 'wood', model: 'timberBench', w: 6,  radius: 150, hp: 480 },
    { type: 'stone', model: null, w: 20, radius: 120, hp: 650 },
    { type: 'stone', model: null, w: 10, radius: 150, hp: 950 },
    { type: 'gold',  model: null, w: 5,  radius: 115, hp: 500 },
    { type: 'gold',  model: null, w: 3,  radius: 140, hp: 700 },
    { type: 'apple', model: null, w: 10, radius: 133, hp: 380 },
    { type: 'bush',  model: null, w: 14, radius: 83,  hp: 240 },
    { type: 'mushroom', model: null, w: 8, radius: 65, hp: 180 },
    { type: 'crystal', model: null, w: 4, radius: 85, hp: 300 },
    { type: 'hive',    model: null, w: 3, radius: 75, hp: 260 }
  ],
  winter: [
    { type: 'wood', model: 'classic', w: 26, radius: 167, hp: 500 },
    { type: 'wood', model: 'classic', w: 13, radius: 207, hp: 680 },
    { type: 'stone', model: null, w: 24, radius: 123, hp: 750 },
    { type: 'stone', model: null, w: 12, radius: 153, hp: 1050 },
    { type: 'gold',  model: null, w: 6,  radius: 118, hp: 540 },
    { type: 'gold',  model: null, w: 3,  radius: 143, hp: 740 },
    { type: 'crystal', model: null, w: 5, radius: 85, hp: 300 },
    { type: 'bush',  model: null, w: 8,  radius: 78,  hp: 220 }
  ],
  desert: [
    { type: 'wood', model: 'classic', w: 16, radius: 161, hp: 460 },
    { type: 'wood', model: 'classic', w: 9,  radius: 199, hp: 640 },
    { type: 'stone', model: null, w: 28, radius: 125, hp: 700 },
    { type: 'stone', model: null, w: 14, radius: 155, hp: 1000 },
    { type: 'gold',  model: null, w: 8,  radius: 123, hp: 520 },
    { type: 'gold',  model: null, w: 4,  radius: 145, hp: 720 },
    { type: 'bush',  model: null, w: 10, radius: 75,  hp: 200 }
  ],
  lava: [
    { type: 'wood', model: 'classic', w: 28, radius: 184, hp: 600 },
    { type: 'wood', model: 'classic', w: 14, radius: 224, hp: 840 },
    { type: 'stone', model: null, w: 20, radius: 123, hp: 800 },
    { type: 'stone', model: null, w: 10, radius: 153, hp: 1120 },
    { type: 'gold',  model: null, w: 6,  radius: 118, hp: 540 },
    { type: 'gold',  model: null, w: 3,  radius: 143, hp: 780 },
    { type: 'bush',  model: null, w: 12, radius: 85,  hp: 250 }
  ]
};
function previewBiome(x, y) {
  const nx = x / WORLD, ny = y / WORLD;
  if (Math.abs(nx) < BIOME_EDGE && Math.abs(ny) < BIOME_EDGE) return 'forest';
  if (Math.abs(ny) >= Math.abs(nx)) return ny < 0 ? 'winter' : 'lava';
  return nx > 0 ? 'desert' : 'lava';
}
function previewResources() {
  const rng = _makeMulberry32(0x4F524553);
  const positions = [];
  const radius = PLAY_RADIUS * 0.98;
  const targetCount = 1400;
  const cellSize = 300;
  const grid = new Map();
  const cellKey = (cx, cy) => cx + ',' + cy;

  // Insert Special World Minerals (4 Diamond, 2 Amethyst, 1 Redite) first
  for (const sp of SPECIAL_WORLD_MINERALS) {
    if (isInsideVillageBuffer(sp.x, sp.y, VILLAGE_RESOURCE_CLEARANCE)) continue;
    positions.push({ ...sp, isSpecial: true });
    const cx = Math.floor(sp.x / cellSize);
    const cy = Math.floor(sp.y / cellSize);
    const k = cellKey(cx, cy);
    if (!grid.has(k)) grid.set(k, []);
    grid.get(k).push({ x: sp.x, y: sp.y });
  }

  let attempts = 0;
  while (positions.length < targetCount && attempts < 45000) {
    attempts++;
    const x = Math.round((rng() * 2 - 1) * radius);
    const y = Math.round((rng() * 2 - 1) * radius);
    const cx = Math.floor(x / cellSize);
    const cy = Math.floor(y / cellSize);

    if (isInsideVillageBuffer(x, y, VILLAGE_RESOURCE_CLEARANCE)) continue;

    // Guaranteed minimum distance: no touching or overlapping resources ("bitisik olmasin")
    let tooClose = false;
    for (let dx = -1; dx <= 1; dx++) {
      for (let dy = -1; dy <= 1; dy++) {
        const neighbors = grid.get(cellKey(cx + dx, cy + dy));
        if (neighbors) {
          for (let i = 0; i < neighbors.length; i++) {
            const n = neighbors[i];
            const distSq = (x - n.x) * (x - n.x) + (y - n.y) * (y - n.y);
            if (distSq < 270 * 270) { tooClose = true; break; }
          }
        }
        if (tooClose) break;
      }
      if (tooClose) break;
    }
    if (tooClose) continue;

    positions.push({ x, y });
    const k = cellKey(cx, cy);
    if (!grid.has(k)) grid.set(k, []);
    grid.get(k).push({ x, y });
  }
  return positions.map((position, idx) => {
    if (position.isSpecial) {
      return {
        id: `resource-${idx}`,
        idx,
        x: position.x,
        y: position.y,
        type: position.type,
        model: null,
        radius: position.radius,
        biome: position.biome,
        hp: position.hp,
        maxHp: position.maxHp,
        name: position.name,
        yG: position.yG,
        yS: position.yS,
        yXp: position.yXp
      };
    }
    const biome = previewBiome(position.x, position.y);
    const defs = PREVIEW_RESOURCE_DEFS[biome] || PREVIEW_RESOURCE_DEFS.forest;
    const total = defs.reduce((sum, entry) => sum + entry.w, 0);
    let roll = rng() * total;
    let picked = defs[0];
    for (const def of defs) {
      roll -= def.w;
      if (roll <= 0) { picked = def; break; }
    }
    return {
      id: `resource-${idx}`,
      idx,
      x: position.x,
      y: position.y,
      type: picked.type,
      model: picked.model || null,
      radius: picked.radius,
      biome,
      hp: picked.hp,
      maxHp: picked.hp
    };
  });
}
const previewWorldResources = previewResources();
const serverResources = previewWorldResources.map((resource, idx) => ({
  ...resource,
  idx,
  hp: resource.hp || (resource.type === 'wood' ? 700 : resource.type === 'stone' ? 850 : 500),
  maxHp: resource.maxHp || (resource.type === 'wood' ? 700 : resource.type === 'stone' ? 850 : 500),
  destroyed: false,
  lastHitBy: new Map(),
  lastHitSwingBy: new Map()
}));

for (const resource of serverResources) {
  const obstacle = {
    x: resource.x,
    y: resource.y,
    radius: resource.radius * 0.96,
    resource
  };
  serverObstacles.push(obstacle);
  const key = obstacleCellKey(obstacle.x, obstacle.y);
  const bucket = obstacleGrid.get(key);
  if (bucket) bucket.push(obstacle);
  else obstacleGrid.set(key, [obstacle]);
}

// ============================================================
// MOB HABITATS & REGIONAL SPECIES SYSTEM
// ============================================================
// Defines distinct species territories, distance bands, and pack behavior.
// Mobs strictly spawn in their natural habitats, form packs/herds with their species,
// and scale in level from low near town to high in deep wilderness.
const MOB_HABITATS = [
  // --- FOREST BIOME: ZONE 1 - STARTER PEACEFUL WILDLIFE (r: 1450 - 2450) [Lv 1 - 3] ---
  // Zero aggressive mobs! 100% peaceful wildlife for beginners outside town buffer.
  {
    id: 'hare_meadows',
    shape: 'wild_hare',
    biome: 'forest',
    minDist: 1450,
    maxDist: 2400,
    // Southwest and East meadows
    sectors: [
      { minAng: -Math.PI * 0.85, maxAng: -Math.PI * 0.15 },
      { minAng: Math.PI * 0.25, maxAng: Math.PI * 0.85 }
    ],
    packSize: 4,
    packSpread: 130,
    weight: 1.3
  },
  {
    id: 'deer_glades',
    shape: 'forest_deer',
    biome: 'forest',
    minDist: 1550,
    maxDist: 2500,
    // Northwest and Northeast quiet glades
    sectors: [
      { minAng: -Math.PI * 0.15, maxAng: Math.PI * 0.25 },
      { minAng: Math.PI * 0.85, maxAng: Math.PI * 1.15 }
    ],
    packSize: 3,
    packSpread: 170,
    weight: 1.1
  },

  // --- FOREST BIOME: ZONE 2 - OUTSKIRTS & THICKETS (r: 2500 - 3800) [Lv 3 - 6] ---
  {
    id: 'hornet_thickets',
    shape: 'forest_hornet',
    biome: 'forest',
    minDist: 2500,
    maxDist: 3700,
    // Flower groves & dense thorn bushes in Southeast
    sectors: [{ minAng: 0.1, maxAng: 1.8 }],
    packSize: 3,
    packSpread: 120,
    weight: 1.0
  },
  {
    id: 'wolf_ridges',
    shape: 'wolf',
    biome: 'forest',
    minDist: 2600,
    maxDist: 3900,
    // Rocky ridges and wolf dens in Northwest / West
    sectors: [
      { minAng: -Math.PI * 0.95, maxAng: -Math.PI * 0.25 },
      { minAng: 2.1, maxAng: 3.1 }
    ],
    packSize: 4,
    packSpread: 150,
    weight: 1.1
  },

  // --- FOREST BIOME: ZONE 3 - MID FOREST & CAVERNS (r: 3800 - 5200) [Lv 6 - 15] ---
  {
    id: 'boar_wallows',
    shape: 'wild_boar',
    biome: 'forest',
    minDist: 3800,
    maxDist: 4900,
    packSize: 3,
    packSpread: 160,
    weight: 1.0
  },
  {
    id: 'spider_hollows',
    shape: 'spider',
    biome: 'forest',
    minDist: 4000,
    maxDist: 5100,
    sectors: [{ minAng: -Math.PI, maxAng: 0 }],
    packSize: 2,
    packSpread: 130,
    weight: 1.0
  },
  {
    id: 'scorpion_crags',
    shape: 'scorpion',
    biome: 'forest',
    minDist: 4200,
    maxDist: 5200,
    sectors: [{ minAng: 0, maxAng: Math.PI }],
    packSize: 2,
    packSpread: 130,
    weight: 0.9
  },

  // --- FOREST BIOME: ZONE 4 - DEEP ANCIENT WOODS & LAIRS (r: 5100 - 7500) [Lv 12 - 28] ---
  {
    id: 'bear_dens',
    shape: 'bear',
    biome: 'forest',
    minDist: 5100,
    maxDist: 6200,
    packSize: 2,
    packSpread: 180,
    weight: 0.9
  },
  {
    id: 'grizzly_territory',
    shape: 'grizzly_bear',
    biome: 'forest',
    minDist: 5600,
    maxDist: 6700,
    packSize: 2,
    packSpread: 200,
    weight: 0.8
  },
  {
    id: 'wendigo_haunts',
    shape: 'elder_wendigo',
    biome: 'forest',
    minDist: 6200,
    maxDist: 7200,
    packSize: 1,
    packSpread: 0,
    weight: 0.7
  },
  {
    id: 'treant_sanctuary',
    shape: 'treant_boss',
    biome: 'forest',
    minDist: 6500,
    maxDist: 7500,
    packSize: 1,
    packSpread: 0,
    weight: 0.5
  },

  // --- OUTER BIOMES (r: 4500 - 10500) [Lv 22 - 65] ---
  // Winter Biome (North, y < -4300)
  { id: 'frost_fox_snow', shape: 'frost_fox', biome: 'winter', minDist: 4500, maxDist: 6800, packSize: 3, packSpread: 140, weight: 1.1 },
  { id: 'polar_bear_glacier', shape: 'polar_bear', biome: 'winter', minDist: 6000, maxDist: 8500, packSize: 2, packSpread: 180, weight: 0.9 },
  { id: 'mammoth_tundra', shape: 'mammoth', biome: 'winter', minDist: 7200, maxDist: 10200, packSize: 2, packSpread: 210, weight: 0.7 },

  // Desert Biome (East, x > 4300)
  { id: 'sand_viper_dunes', shape: 'sand_viper', biome: 'desert', minDist: 4500, maxDist: 6800, packSize: 3, packSpread: 140, weight: 1.1 },
  { id: 'dune_scorpion_wastes', shape: 'dune_scorpion', biome: 'desert', minDist: 6000, maxDist: 8500, packSize: 2, packSpread: 160, weight: 0.9 },
  { id: 'dune_lizard_canyons', shape: 'dune_lizard', biome: 'desert', minDist: 7200, maxDist: 10200, packSize: 2, packSpread: 200, weight: 0.7 },

  // Lava Biome (South & West, y > 4300 or x < -4300)
  { id: 'magma_hound_pack', shape: 'magma_hound', biome: 'lava', minDist: 4500, maxDist: 6800, packSize: 3, packSpread: 150, weight: 1.1 },
  { id: 'fire_drake_caldera', shape: 'fire_drake', biome: 'lava', minDist: 6000, maxDist: 8500, packSize: 2, packSpread: 190, weight: 0.8 },
  { id: 'obsidian_golem_abyss', shape: 'obsidian_golem', biome: 'lava', minDist: 7200, maxDist: 10200, packSize: 1, packSpread: 0, weight: 0.6 }
];

function clampBiomeX(targetBiome, x) {
  if (targetBiome === 'winter') return Math.max(-4100, Math.min(4100, x));
  if (targetBiome === 'desert') return Math.max(4400, Math.min(9800, x));
  if (targetBiome === 'lava') {
    return x < 0 ? Math.max(-9800, Math.min(-4400, x)) : Math.max(-4100, Math.min(4100, x));
  }
  return Math.max(-4150, Math.min(4150, x));
}

function clampBiomeY(targetBiome, y) {
  if (targetBiome === 'winter') return Math.max(-9800, Math.min(-4400, y));
  if (targetBiome === 'desert') return Math.max(-4100, Math.min(4100, y));
  if (targetBiome === 'lava') {
    return y > 0 ? Math.max(4400, Math.min(9800, y)) : Math.max(-4100, Math.min(4100, y));
  }
  return Math.max(-4150, Math.min(4150, y));
}

function pickWeightedHabitat(habitats) {
  if (!habitats || habitats.length === 0) return MOB_HABITATS[0];
  let totalWeight = 0;
  for (let i = 0; i < habitats.length; i++) totalWeight += (habitats[i].weight || 1.0);
  let roll = Math.random() * totalWeight;
  for (let i = 0; i < habitats.length; i++) {
    roll -= (habitats[i].weight || 1.0);
    if (roll <= 0) return habitats[i];
  }
  return habitats[0];
}

function selectHabitat(biome, nearX = null, nearY = null) {
  if (biome === 'forest') {
    if (nearX !== null && nearY !== null) {
      const pDist = Math.hypot(nearX, nearY);
      let eligible;
      if (pDist < 2500) {
        // Village outskirts: ONLY peaceful wildlife (Yaban Tavşanı Lv 1-2, Orman Geyiği Lv 2-3)
        eligible = MOB_HABITATS.filter(h => h.biome === 'forest' && h.maxDist <= 2500);
      } else if (pDist < 3900) {
        // Outskirts & Thickets (Hornet, Wolf)
        eligible = MOB_HABITATS.filter(h => h.biome === 'forest' && h.minDist >= 2400 && h.maxDist <= 4000);
      } else if (pDist < 5300) {
        // Mid Forest (Boar, Spider, Scorpion)
        eligible = MOB_HABITATS.filter(h => h.biome === 'forest' && h.minDist >= 3700 && h.maxDist <= 5300);
      } else {
        // Deep Forest (Bear, Grizzly, Wendigo, Treant)
        eligible = MOB_HABITATS.filter(h => h.biome === 'forest' && h.minDist >= 5000);
      }
      if (!eligible || eligible.length === 0) eligible = MOB_HABITATS.filter(h => h.biome === 'forest');
      return pickWeightedHabitat(eligible);
    }
    return pickWeightedHabitat(MOB_HABITATS.filter(h => h.biome === 'forest'));
  }

  // Outer biomes: distance tiers
  if (nearX !== null && nearY !== null) {
    const pDist = Math.hypot(nearX, nearY);
    let eligible;
    if (pDist < 6500) eligible = MOB_HABITATS.filter(h => h.biome === biome && h.maxDist <= 7000);
    else if (pDist < 8500) eligible = MOB_HABITATS.filter(h => h.biome === biome && h.minDist >= 5800 && h.maxDist <= 9000);
    else eligible = MOB_HABITATS.filter(h => h.biome === biome && h.minDist >= 7000);
    if (!eligible || eligible.length === 0) eligible = MOB_HABITATS.filter(h => h.biome === biome);
    return pickWeightedHabitat(eligible);
  }
  return pickWeightedHabitat(MOB_HABITATS.filter(h => h.biome === biome));
}

function isPositionSafeForMob(x, y, minMobDist = 120, minPlayerDist = 220) {
  if (isInsideVillageBuffer(x, y, VILLAGE_MOB_CLEARANCE)) return false;

  for (const m of mobs.values()) {
    const dx = m.x - x, dy = m.y - y;
    if (dx * dx + dy * dy < minMobDist * minMobDist) return false;
  }
  for (const p of players.values()) {
    const dx = p.x - x, dy = p.y - y;
    if (dx * dx + dy * dy < minPlayerDist * minPlayerDist) return false;
  }
  // Anti-Glitch: Never spawn inside player buildings or walls
  if (nearbyBuildings(x, y, 75).length > 0) return false;

  // Anti-Glitch: Never spawn inside resource rocks, trees or gold (70px margin is plenty)
  for (let ri = 0; ri < serverResources.length; ri++) {
    const res = serverResources[ri];
    if (!res) continue;
    const rdx = res.x - x, rdy = res.y - y;
    if (rdx * rdx + rdy * rdy < 70 * 70) return false;
  }
  return true;
}

function findSafeMobSpawn(targetBiome = 'forest', nearX = null, nearY = null) {
  const habitat = selectHabitat(targetBiome, nearX, nearY);
  const minMobDist = MOB_MIN_SPAWN_SEPARATION;
  const minPlayerDist = 180;

  // 1. Pack Clustering Mechanic:
  // 75% chance to spawn adjacent to an existing pack member of the SAME species/habitat
  if (Math.random() < 0.75) {
    const packMates = [];
    for (const m of mobs.values()) {
      if (m.shape === habitat.shape) {
        let neighborCount = 0;
        for (const o of mobs.values()) {
          if (o !== m && o.shape === m.shape && Math.hypot(o.x - m.x, o.y - m.y) < 280) {
            neighborCount++;
          }
        }
        if (neighborCount < (habitat.packSize || 3) - 1) {
          packMates.push(m);
        }
      }
    }

    if (packMates.length > 0) {
      const packMate = packMates[Math.floor(Math.random() * packMates.length)];
      for (let pAttempt = 0; pAttempt < 15; pAttempt++) {
        const pAng = Math.random() * Math.PI * 2;
        const pDist = 190 + Math.random() * Math.max(220, habitat.packSpread || 0);
        let px = Math.round(packMate.x + Math.cos(pAng) * pDist);
        let py = Math.round(packMate.y + Math.sin(pAng) * pDist);

        px = clampBiomeX(targetBiome, px);
        py = clampBiomeY(targetBiome, py);

        if (isPositionSafeForMob(px, py, minMobDist, minPlayerDist)) {
          return { x: px, y: py, habitat, packLeader: packMate };
        }
      }
    }
  }

  // 2. Habitat Territory Spawn:
  // Pick a position strictly within the habitat's distance band and sector angles
  for (let attempt = 0; attempt < 50; attempt++) {
    let ang;
    if (habitat.sectors && habitat.sectors.length > 0) {
      const sec = habitat.sectors[Math.floor(Math.random() * habitat.sectors.length)];
      ang = sec.minAng + Math.random() * (sec.maxAng - sec.minAng);
    } else {
      ang = Math.random() * Math.PI * 2;
    }

    let dist;
    if (nearX !== null && nearY !== null && attempt < 35 && targetBiome === previewBiome(nearX, nearY)) {
      const pAng = Math.random() * Math.PI * 2;
      const pDist = 380 + Math.random() * 800;
      let candX = Math.round(nearX + Math.cos(pAng) * pDist);
      let candY = Math.round(nearY + Math.sin(pAng) * pDist);
      candX = clampBiomeX(targetBiome, candX);
      candY = clampBiomeY(targetBiome, candY);
      if (isPositionSafeForMob(candX, candY, minMobDist, minPlayerDist)) {
        return { x: candX, y: candY, habitat, packLeader: null };
      }
    }

    dist = habitat.minDist + Math.random() * (habitat.maxDist - habitat.minDist);
    let x = Math.round(Math.cos(ang) * dist);
    let y = Math.round(Math.sin(ang) * dist);

    x = clampBiomeX(targetBiome, x);
    y = clampBiomeY(targetBiome, y);

    if (isPositionSafeForMob(x, y, minMobDist, minPlayerDist)) {
      return { x, y, habitat, packLeader: null };
    }
  }

  // Keep the same spacing guarantee even when the preferred local area is crowded.
  for (let attempt = 0; attempt < 100; attempt++) {
    const fallbackAngle = Math.random() * Math.PI * 2;
    const fallbackDistance = Math.max(1600, habitat.minDist || 1600) + Math.random() * 1400;
    let fallbackX = Math.round(Math.cos(fallbackAngle) * fallbackDistance);
    let fallbackY = Math.round(Math.sin(fallbackAngle) * fallbackDistance);
    fallbackX = clampBiomeX(targetBiome, fallbackX);
    fallbackY = clampBiomeY(targetBiome, fallbackY);
    if (isPositionSafeForMob(fallbackX, fallbackY, minMobDist, minPlayerDist)) {
      return { x: fallbackX, y: fallbackY, habitat, packLeader: null };
    }
  }
  const fallbackAngle = Math.random() * Math.PI * 2;
  const fallbackDistance = Math.max(2000, habitat.minDist || 2000);
  let fallbackX = clampBiomeX(targetBiome, Math.round(Math.cos(fallbackAngle) * fallbackDistance));
  let fallbackY = clampBiomeY(targetBiome, Math.round(Math.sin(fallbackAngle) * fallbackDistance));
  if (isInsideVillageBuffer(fallbackX, fallbackY, VILLAGE_MOB_CLEARANCE)) {
    fallbackX = clampBiomeX(targetBiome, VILLAGE_BUFFER_HALF + VILLAGE_MOB_CLEARANCE + 1);
    fallbackY = clampBiomeY(targetBiome, 0);
  }
  return {
    x: fallbackX,
    y: fallbackY,
    habitat,
    packLeader: null
  };
}

function createMob(prefBiome = null, nearX = null, nearY = null) {
  const biome = prefBiome || (nearX !== null && nearY !== null ? previewBiome(nearX, nearY) : 'forest');
  const { x, y, habitat } = findSafeMobSpawn(biome, nearX, nearY);
  const distFromCenter = Math.hypot(x, y);

  const type = MOB_TYPES.find(m => m.shape === habitat.shape) ||
               MOB_TYPES.find(m => m.biome === biome) ||
               MOB_TYPES[0];

  // Distance-scaled mob level progression:
  // Level increases smoothly from minLevel to maxLevel as mob distance increases
  const minLvl = type.minLevel || 1;
  const maxLvl = type.maxLevel || minLvl;
  const hMin = habitat?.minDist || 1450;
  const hMax = habitat?.maxDist || 7500;
  const progress = Math.max(0, Math.min(1, (distFromCenter - hMin) / Math.max(1, hMax - hMin)));
  const baseCalc = minLvl + progress * (maxLvl - minLvl);
  const mobLevel = Math.max(minLvl, Math.min(maxLvl, Math.round(baseCalc + (Math.random() * 0.8 - 0.4))));

  const baseLvl = type.baseLevel || minLvl;
  const lvlScaleHp = 1 + (mobLevel - 1) * 0.16;
  const lvlScaleDmg = 1 + (mobLevel - 1) * 0.12;

  const scaledHp = Math.round(type.hp * lvlScaleHp);
  const scaledDmg = Math.round(type.dmg * lvlScaleDmg);
  const scaledGold = Math.round(type.goldReward * (1 + (mobLevel - 1) * 0.08));
  const scaledXp = Math.round(type.xpReward * (1 + (mobLevel - 1) * 0.10));

  const angle = Math.random() * Math.PI * 2;
  const homeX = x;
  const homeY = y;
  const leashRadius = 850 + Math.random() * 300;

  const mob = {
    id: `mob-${nextMobId++}`, x, y, vx: 0, vy: 0, radius: type.radius || 44,
    homeX, homeY, leashRadius,
    level: mobLevel, lvl: mobLevel,
    hp: scaledHp, maxHp: scaledHp, color: type.color, outline: type.outline, shape: type.shape,
    eyes: type.eyes, typeName: type.typeName, dmg: scaledDmg, biome: type.biome || 'forest',
    speed: type.speed || MOB_SPEED, wanderSpeed: type.wanderSpeed || MOB_WANDER_SPEED,
    xpReward: scaledXp, goldReward: scaledGold,
    isPeaceful: Boolean(type.isPeaceful),
    isBoss: Boolean(type.isBoss),
    nextAttackAt: 0, wanderAngle: angle, wanderTargetAngle: angle,
    nextWanderTurnAt: Date.now() + 2500 + Math.random() * 2500,
    angle, targetId: null, chaseUntil: 0,
    state: 'walk', stateSeq: 0, stateAt: Date.now(),
    chaseStartedAt: 0, ignoreTargetId: null, ignoreTargetUntil: 0,
  };
  mobs.set(mob.id, mob);
  io.emit('mob_spawn', publicMob(mob));
  return mob;
}

function ensureMobs(prefX = null, prefY = null) {
  const spawnMultiplier = Math.max(0.1, Math.min(1.5, Number(adminConfig.mobSpawnMultiplier) || 1));
  const target = Math.max(1, Math.round(MAX_MOBS * spawnMultiplier));
  const biomes = ['forest', 'winter', 'desert', 'lava'];

  for (const mob of mobs.values()) {
    if (!isInsideVillageBuffer(mob.x, mob.y, VILLAGE_MOB_CLEARANCE)) continue;
    mobs.delete(mob.id);
    io.emit('mob_despawn', { id: mob.id });
  }

  const biomeCounts = { forest: 0, winter: 0, desert: 0, lava: 0 };
  for (const m of mobs.values()) {
    const b = m.biome || previewBiome(m.x, m.y);
    if (biomeCounts[b] !== undefined) biomeCounts[b]++;
  }

  const humanPlayers = [...players.values()].filter(p => !p.isBot && (p.hp ?? 0) > 0);

  // If a specific position is passed (e.g. join or teleport), spawn local mobs if low
  if (prefX !== null && prefY !== null) {
    const pBiome = previewBiome(prefX, prefY);
    const nearby = nearbyMobs(prefX, prefY, 1500);
    while (nearby.length < 8 && mobs.size < target) {
      const nm = createMob(pBiome, prefX, prefY);
      nearby.push(nm);
      biomeCounts[pBiome] = (biomeCounts[pBiome] || 0) + 1;
    }
  }

  // Ensure every active human player has mobs nearby in their biome (outside safe buffer)
  for (const p of humanPlayers) {
    // Keep village safe & peaceful; only populate when outside buffer
    if (Math.hypot(p.x, p.y) < VILLAGE_BUFFER_RADIUS) continue;

    const pBiome = previewBiome(p.x, p.y);
    const nearby = nearbyMobs(p.x, p.y, 1800);
    let attempts = 0;
    while (nearby.length < 8 && attempts < 12) {
      attempts++;
      if (mobs.size < target) {
        const nm = createMob(pBiome, p.x, p.y);
        nearby.push(nm);
        biomeCounts[pBiome] = (biomeCounts[pBiome] || 0) + 1;
      } else {
        // Recycle distant idle non-boss mob (> 2800 from all players)
        let recycled = null;
        for (const m of mobs.values()) {
          if (!m.targetId && !m.isBoss) {
            const hasNearbyPlayer = humanPlayers.some(pl => Math.hypot(pl.x - m.x, pl.y - m.y) < 2800);
            if (!hasNearbyPlayer) {
              recycled = m;
              break;
            }
          }
        }
        if (recycled) {
          mobs.delete(recycled.id);
          io.emit('mob_despawn', { id: recycled.id });
          const nm = createMob(pBiome, p.x, p.y);
          nearby.push(nm);
        } else {
          break; // All mobs are near active players
        }
      }
    }
  }

  // Maintain even quota across all 4 biomes
  const perBiomeTarget = Math.floor(target / biomes.length);
  for (const b of biomes) {
    while ((biomeCounts[b] || 0) < perBiomeTarget && mobs.size < target) {
      const pInBiome = humanPlayers.find(p => previewBiome(p.x, p.y) === b);
      if (pInBiome && Math.hypot(pInBiome.x, pInBiome.y) >= VILLAGE_BUFFER_RADIUS) {
        createMob(b, pInBiome.x, pInBiome.y);
      } else {
        createMob(b);
      }
      biomeCounts[b] = (biomeCounts[b] || 0) + 1;
    }
  }

  while (mobs.size < target) {
    const b = biomes[mobs.size % biomes.length];
    createMob(b);
  }

  while (mobs.size > target) {
    const oldest = mobs.keys().next().value;
    if (!oldest) break;
    mobs.delete(oldest);
    io.emit('mob_despawn', { id: oldest });
  }
}

function applyMobDamage(mob, target, damage, isWeb = false) {
  if (!mob || !target || (target.hp ?? 0) <= 0) return null;
  if (isInsideSafeVillage(target.x, target.y)) return null;
  const now = Date.now();
  if (isWeb) {
    const lastWebAt = Number(target._lastWebAt || 0);
    if (lastWebAt && now - lastWebAt < 3600) return null;
    target._lastWebAt = now;
  }
  const isBot = Boolean(target.isBot);
  const targetSocket = io.sockets.sockets.get(target.id);
  if (!isBot && (!targetSocket || !targetSocket.connected)) return null;

  // Seviye farkı ve Savunma statı hesaplaması
  const mobLvl = mob.level || 1;
  const targetLvl = calculatePlayerLevel(target);
  const lvlFactor = calculateLevelGapMultiplier(mobLvl, targetLvl);
  const defLvl = Math.max(1, Number(target.defenceLevel || 1));
  const defBonus = 1 - Math.min(0.40, (defLvl - 1) * 0.015);
  const armor = Math.max(0.3, Math.min(3.0, Number(target.armorMultiplier) || 1.0));
  const rawDmg = Number(damage) || 1;
  const maxEffectiveDamage = Math.max(1, Math.ceil((Number(target.maxHp) || 250) * 0.18));
  const maxRawDamage = Math.max(1, Math.floor(maxEffectiveDamage * armor));
  const appliedDamage = Math.min(
    limitHitDamage(target, Math.round(rawDmg * lvlFactor * defBonus)),
    maxRawDamage
  );
  const hpBefore = target.hp;
  applyPlayerDamage(target, appliedDamage);
  const actualDamage = Math.max(0, hpBefore - target.hp);

  // Oyuncuya Defence XP kazandır
  const defXpGain = Math.max(6, Math.round(actualDamage * 0.55));
  if (targetSocket) {
    awardCombatXp(target, 'defence', defXpGain, { from: mob.typeName || 'Canavar' });
  }
  const hpAt = target.hpAt;
  const hpSeq = target.hpSeq;
  const payload = {
    id: target.id, hp: target.hp, dmg: actualDamage, hpSeq, hpAt,
    sourceId: mob.id, sourceName: mob.typeName || 'Düşman', isWeb: Boolean(isWeb),
  };
  if (isBot) {
    broadcastPlayerStateNear(target);
    if (target.hp <= 0) {
      onPlayerDeath(target.id);
      io.emit('player_dead', { id: target.id });
    }
  } else {
    io.to(target.id).emit('player_take_damage', payload);
    io.to(target.id).emit('self_state', { hp: target.hp, hpSeq, hpAt });
  }
  return payload;
}

function limitHitDamage(target, damage) {
  const maxHp = Math.max(1, Number(target?.maxHp) || 250);
  return Math.min(Math.max(1, Math.round(Number(damage) || 1)), Math.max(1, Math.ceil(maxHp * 0.22)));
}

function awardCombatXp(player, type, amount, details = {}) {
  if (!player || (type !== 'melee' && type !== 'defence')) return;
  const levelKey = type === 'melee' ? 'meleeLevel' : 'defenceLevel';
  const xpKey = type === 'melee' ? 'meleeXp' : 'defenceXp';
  const level = Math.max(1, Math.min(100, Number(player[levelKey]) || 1));
  let xp = Math.max(0, Number(player[xpKey]) || 0) + Math.max(1, Math.round((Number(amount) || 0) * 0.15));
  let nextLevel = level;
  const maxXpForLevel = currentLevel => Math.floor((type === 'melee' ? 360 * Math.pow(1.4, currentLevel - 1) : 440 * Math.pow(1.42, currentLevel - 1)));
  while (xp >= maxXpForLevel(nextLevel) && nextLevel < 100) {
    xp -= maxXpForLevel(nextLevel);
    nextLevel++;
  }
  player[levelKey] = nextLevel;
  player[xpKey] = xp;
  if (player._authUser) {
    player._authUser[levelKey] = nextLevel;
    player._authUser[xpKey] = xp;
    saveAccountData();
  }
  const targetSocket = io.sockets.sockets.get(player.id);
  if (!targetSocket) return;
  targetSocket.emit('combat_xp_gain', { ...details, type, amount });
  targetSocket.emit('combat_stats_state', {
    meleeLevel: Math.max(1, Number(player.meleeLevel) || 1),
    meleeXp: Math.max(0, Number(player.meleeXp) || 0),
    defenceLevel: Math.max(1, Number(player.defenceLevel) || 1),
    defenceXp: Math.max(0, Number(player.defenceXp) || 0)
  });
}

function isPlayerCombatEligible(player, socketMap = io?.sockets?.sockets) {
  if (!player || typeof player !== 'object') return false;
  if ((player.hp ?? 0) <= 0 || player._dead === true) return false;
  if (isInsideSafeVillage(player.x, player.y)) return false;
  if (!player.id) return false;
  if (player.isBot) return true;
  const socket = socketMap ? socketMap.get(player.id) : null;
  return !!socket && socket.connected === true;
}

function isMobTargetEligible(mob, candidate, socketMap = io?.sockets?.sockets) {
  if (!mob || !candidate) return false;
  if (!isPlayerCombatEligible(candidate, socketMap)) return false;
  if (isInsideSafeVillage(candidate.x, candidate.y)) return false;
  // Peaceful mobs (Hare, Deer) never auto-aggro unless provoked by player attack
  if (mob.isPeaceful && mob.targetId !== candidate.id) return false;
  const d = Math.hypot((candidate.x || 0) - (mob.x || 0), (candidate.y || 0) - (mob.y || 0));
  if (d > (mob.targetId === candidate.id ? MOB_AGGRO_RANGE * 1.6 : MOB_AGGRO_RANGE)) return false;
  return true;
}

function applyPlayerDamage(target, damage) {
  if (!target) return target;
  if (isInsideSafeVillage(target.x, target.y)) return target;
  const rawDmg = Math.max(1, Math.round(Number(damage) || 1));
  const armor = Math.max(0.3, Math.min(3.0, Number(target.armorMultiplier) || 1.0));
  const effectiveDamage = Math.max(1, Math.round(rawDmg / armor));
  target.hp = Math.max(0, (target.hp ?? 250) - effectiveDamage);
  target.hpSeq = (target.hpSeq || 0) + 1;
  target.hpAt = Date.now();
  return target;
}

function broadcastPlayerStateNear(target) {
  if (!target) return;
  const nearby = nearbyPlayers(target.x, target.y, PLAYER_AOI_RADIUS);
  for (const observer of nearby) {
    if (!observer || observer.isBot) continue;
    const socket = io.sockets.sockets.get(observer.id);
    if (socket?.connected) socket.volatile.emit('players', { [target.id]: compactStateCompressed(target) });
  }
}

function broadcastPlayerEventNear(player, event, payload) {
  if (!player) return;
  const nearby = nearbyPlayers(player.x, player.y, PLAYER_AOI_RADIUS);
  for (const observer of nearby) {
    if (!observer || observer.isBot) continue;
    const socket = io.sockets.sockets.get(observer.id);
    if (socket?.connected) socket.emit(event, payload);
  }
}

function broadcastMobEventNear(mob, event, payload) {
  if (!mob) return;
  const sentTo = new Set();
  const nearby = nearbyPlayers(mob.x, mob.y, MOB_AOI_RADIUS);
  for (const observer of nearby) {
    if (!observer || observer.isBot) continue;
    const socket = io.sockets.sockets.get(observer.id);
    if (socket?.connected) {
      socket.emit(event, payload);
      sentTo.add(observer.id);
    }
  }
  for (const [id, socket] of io.sockets.sockets) {
    if (socket.data.isSpectator && socket.connected && !sentTo.has(id)) socket.emit(event, payload);
  }
}

function broadcastTrapStateNear(target, payload) {
  broadcastPlayerEventNear(target, 'trap_state', payload);
}

function broadcastBotEvent(bot, event, payload) {
  broadcastPlayerEventNear(bot, event, payload);
}

function publishPlayerDamage(target, damage, sourceName = 'Düşman') {
  if (!target) return;
  const socket = io.sockets.sockets.get(target.id);
  if (target.isBot) {
    broadcastPlayerStateNear(target);
    return;
  }
  if (!socket || !socket.connected) return;
  socket.emit('pvp_hit', { dmg: damage, fromName: sourceName });
  socket.emit('self_state', { hp: target.hp, hpSeq: target.hpSeq, hpAt: target.hpAt });
}

function applySpikeDamageToTarget(target, spike, now = Date.now(), fromPush = false) {
  if (!target || (target.hp ?? 0) <= 0 || target._dead) return false;
  if (isInsideSafeVillage(target.x, target.y)) return false;
  if (!spike || Number(spike.type) !== 3 || (spike.hp ?? 0) <= 0) return false;
  if (!pvpAllowed()) return false;
  // Spike owner cannot damage themselves
  if (spike.ownerId === target.id) return false;
  // Team / Clan immunity
  if (!target.isBot && ((spike.ownerClanId && spike.ownerClanId === target.clanId) || (spike.ownerTeam && spike.ownerTeam === target.team))) return false;
  if (target.isBot && spike.ownerClanId && target.clanId && spike.ownerClanId === target.clanId) return false;

  // Rate limiting / Cooldown per target per spike (420ms cooldown)
  if (!target.lastSpikeHits) target.lastSpikeHits = new Map();
  const spikeKey = String(spike.id || spike._netId || `${spike.ownerId || 'spike'}:${spike.x}:${spike.y}`);
  const lastHit = target.lastSpikeHits.get(spikeKey) || 0;
  if (now - lastHit < 420) return false;
  target.lastSpikeHits.set(spikeKey, now);
  target.lastSpikeHit = now;
  target.lastSpikeHitAt = now;

  const tier = Math.max(0, Math.min(5, Number(spike.tier) || 0));
  const damage = limitHitDamage(target, Math.min(180, Math.round(60 * [1, 1.15, 1.3, 1.5, 1.8, 2.2][tier])));
  applyPlayerDamage(target, damage);

  const owner = players.get(spike.ownerId);
  if (target.isBot && owner) alertBotAttacked(target, owner);

  const ownerName = owner?.name || 'Diken';
  io.to(target.id).emit('pvp_hit', { dmg: damage, fromName: ownerName });
  io.to(target.id).emit('self_state', { hp: target.hp, hpSeq: target.hpSeq, hpAt: target.hpAt });
  broadcastPlayerStateNear(target);

  if (owner && !owner.isBot) {
    const s = io.sockets.sockets.get(owner.id);
    if (s) {
      s.emit('spike_dmg_confirm', { targetId: target.id, dmg: damage, targetName: target.name || 'Oyuncu' });
    }
  }

  // Knockback away from spike if NOT trapped
  if (!target.trappedBy) {
    const sdx = (Number(target.x) || 0) - Number(spike.x);
    const sdy = (Number(target.y) || 0) - Number(spike.y);
    const slen = Math.hypot(sdx, sdy) || 1;
    io.to(target.id).emit('spike_push', { dx: sdx / slen, dy: sdy / slen, force: 180 });
  }

  if (target.hp <= 0) {
    if (owner) {
      stealDeathLoot(owner, target);
      owner.kills = (owner.kills || 0) + 1;
      owner.score = (owner.score || 0) + 150;
      if (!owner.isBot && !target.isBot) {
        recordServerQuestProgress(owner, {
          pvpKills: 1,
          ...(BOUNTY_EVENT_ENABLED && currentBountyId && target.id === currentBountyId ? { kingKills: 1 } : {})
        });
      }
      if (BOUNTY_EVENT_ENABLED && currentBountyId && target.id === currentBountyId) {
        const bountyBonus = 300;
        owner.gold = (owner.gold || 0) + bountyBonus;
        owner.score = (owner.score || 0) + bountyBonus;
        const s = io.sockets.sockets.get(owner.id);
        if (s) s.emit('bounty_kill_reward', { name: target.name || 'Oyuncu', bonus: bountyBonus });
        io.emit('bounty_killed_broadcast', { killer: ownerName, victim: target.name || 'Oyuncu', bonus: bountyBonus });
        currentBountyId = null;
        io.emit('bounty_update', { id: null });
      }
      const s = io.sockets.sockets.get(owner.id);
      if (s) s.emit('pvp_kill_confirm', { targetId: target.id, targetName: target.name || 'Oyuncu' });
      persistPlayerScore(owner);
    }
    onPlayerDeath(target.id);
    target.kills = target.kills || 0;
    io.to(target.id).emit('pvp_killed', { byName: ownerName });
    io.emit('player_dead', { id: target.id });
    io.emit('pvp_kill_feed', { killer: ownerName, victim: target.name || 'Oyuncu', streak: owner?.kills || 0 });
  }
  return true;
}

function applyBotSpikeDamage(bot, spike, now) {
  return applySpikeDamageToTarget(bot, spike, now);
}

function triggerSpikeContacts(spike, now = Date.now()) {
  if (!spike || Number(spike.type) !== 3 || (spike.hp ?? 0) <= 0) return;
  const spikeRadius = Number(spike.radius) || 34;
  for (const target of players.values()) {
    if (!target || (target.hp ?? 0) <= 0 || target.id === spike.ownerId) continue;
    const targetRadius = Number(target.radius) || 35;
    const distance = Math.hypot((Number(target.x) || 0) - Number(spike.x), (Number(target.y) || 0) - Number(spike.y));
    if (distance <= targetRadius + spikeRadius) applySpikeDamageToTarget(target, spike, now);
  }
  const owner = players.get(spike.ownerId);
  if (!owner) return;
  for (const mob of mobs.values()) {
    if (!mob || (mob.hp ?? 0) <= 0) continue;
    const mobRadius = Number(mob.radius) || 36;
    const distance = Math.hypot((Number(mob.x) || 0) - Number(spike.x), (Number(mob.y) || 0) - Number(spike.y));
    if (distance <= mobRadius + spikeRadius) applySpikeDamageToMob(mob, spike, owner, now);
  }
}

function applySpikeDamageToMob(mob, spike, attacker, now = Date.now()) {
  if (!mob || mob.hp <= 0 || !spike || Number(spike.type) !== 3 || (spike.hp ?? 0) <= 0) return false;
  if (now - (mob.lastSpikeHitAt || 0) < 420) return false;
  mob.lastSpikeHitAt = now;
  const tier = Math.max(0, Math.min(5, Number(spike.tier) || 0));
  const baseDamage = [45, 75, 110, 160, 220, 300][tier] || 45;
  const damage = mob.isBoss ? Math.min(baseDamage, Math.ceil(mob.maxHp / 18)) : baseDamage;
  mob.hp = Math.max(0, mob.hp - damage);
  if (attacker) setMobTarget(mob, attacker.id, now);
  mob.stateSeq = (mob.stateSeq || 0) + 1;
  broadcastMobEventNear(mob, 'mob_update', {
    id: mob.id, seq: mob.stateSeq, ts: now, hp: mob.hp, maxHp: mob.maxHp,
    hitFlash: 8, ...(attacker ? { targetId: attacker.id } : {})
  });

  if (mob.hp <= 0) {
    mobs.delete(mob.id);
    broadcastMobEventNear(mob, 'mob_dead', { id: mob.id, killerId: attacker?.id || spike.ownerId || null });
    if (attacker) awardBuildingMobKill(mob, attacker, 0.65);
    setTimeout(() => { if (players.size > 0) ensureMobs(); }, 4000 + Math.random() * 2000);
  }
  return true;
}

function awardBuildingMobKill(mob, attacker, goldMultiplier = 1) {
  if (!mob || !attacker) return;
  const rewardGold = Math.max(1, Math.floor((mob.goldReward || 10) * goldMultiplier));
  const rewardXp = Math.max(1, Math.round((mob.xpReward || 35) * Math.max(0.1, Number(adminConfig.xpRate) || 1)));
  const rewardScore = Math.round(rewardXp * 0.75 + rewardGold * 3);
  attacker.gold = (attacker.gold || 0) + rewardGold;
  attacker.xp = (attacker.xp || 0) + rewardXp;
  attacker.score = (attacker.score || 0) + rewardScore;
  attacker.kills = (attacker.kills || 0) + 1;
  applyLoadoutStats(attacker);
  attacker.hpSeq = (attacker.hpSeq || 0) + 1;
  attacker.hpAt = Date.now();
  const mobQuestKey = questMobKey(mob);
  recordServerQuestProgress(attacker, { kills: 1, ...(mobQuestKey ? { [mobQuestKey]: 1 } : {}), gold: rewardGold });
  persistPlayerScore(attacker);
  const attackerSocket = io.sockets.sockets.get(attacker.id);
  if (attackerSocket) {
    attackerSocket.emit('self_state', {
      hp: attacker.hp, maxHp: attacker.maxHp, baseMaxHp: attacker._loadoutBaseMaxHp,
      hpSeq: attacker.hpSeq, hpAt: attacker.hpAt,
      g: attacker.gold, xp: attacker.xp, sc: attacker.score, k: attacker.kills,
      matchKills: Math.max(0, attacker.kills - (attacker.matchStartKills || 0))
    });
    attackerSocket.emit('mob_kill_reward', { xp: rewardXp, gold: rewardGold, score: rewardScore, typeName: mob.typeName });
  }
  awardLoot(attacker, mob.level || mob.lvl || 1, Boolean(mob.isBoss));
}

function applyMobTrapDamage(mob, trap, now = Date.now()) {
  if (!mob || mob.hp <= 0 || !trap || Number(trap.type) !== 6 || (trap.hp ?? 0) <= 0) return false;
  const trapId = String(trap.id);
  const isFirstHit = mob.trapDamageBuildingId !== trapId;
  if (!isFirstHit && now - (mob.lastTrapDamageAt || 0) < 1500) return false;
  mob.trapDamageBuildingId = trapId;
  mob.lastTrapDamageAt = now;
  const tier = Math.max(0, Math.min(5, Number(trap.tier) || 0));
  const damage = (isFirstHit ? [35, 60, 90, 130, 180, 250] : [10, 18, 28, 40, 55, 75])[tier] || 10;
  mob.hp = Math.max(0, mob.hp - damage);
  mob.stateSeq = (mob.stateSeq || 0) + 1;
  broadcastMobEventNear(mob, 'mob_update', { id: mob.id, seq: mob.stateSeq, ts: now, hp: mob.hp, maxHp: mob.maxHp, hitFlash: 8 });
  if (mob.hp <= 0) {
    mobs.delete(mob.id);
    const owner = players.get(trap.ownerId || trap._ownerId);
    broadcastMobEventNear(mob, 'mob_dead', { id: mob.id, killerId: owner?.id || trap.ownerId || null });
    if (owner) awardBuildingMobKill(mob, owner);
    setTimeout(() => { if (players.size > 0) ensureMobs(); }, 4000 + Math.random() * 2000);
  }
  return true;
}

function applyMobBuildingDamage(mob, building, now = Date.now()) {
  if (!mob || !building || (building.hp ?? 0) <= 0) return false;
  const type = Number(building.type);
  const cooldown = type === 4 ? 1200 : type === 8 ? 1500 : type === 9 ? 2000 : 0;
  if (!cooldown || now - (mob.lastBuildHitAt || 0) <= cooldown) return false;
  mob.lastBuildHitAt = now;
  const damageMultiplier = type === 4 ? 0.8 : type === 8 ? 0.6 : 0.4;
  const damage = Math.max(1, Math.round((Number(mob.dmg) || 0) * damageMultiplier));
  building.hp = Math.max(0, (building.hp ?? building.maxHp ?? 100) - damage);
  io.emit('build_hp_update', { id: building.id, hp: building.hp });
  if (building.hp <= 0) {
    if (type === 6) releaseTrapVictims(building.id);
    buildings.delete(building.id);
    scheduleBuildingGridRebuild();
    io.emit('build_destroy', { id: building.id });
    io.emit('trap_freed', { buildingId: building.id });
  }
  return true;
}

function sanitizePlayerLoadout(role, helmet) {
  const normalizedRole = String(role || 'tank').toLowerCase();
  const normalizedHelmet = String(helmet || 'guardian').toLowerCase();
  const resolvedRole = BUILD_ROLES[normalizedRole] ? normalizedRole : 'tank';
  const aliasedHelmet = ITEM_HELMET_ALIAS_MAP[normalizedHelmet] || normalizedHelmet;
  const resolvedHelmet = BUILD_HELMETS[aliasedHelmet] ? aliasedHelmet : 'guardian';
  return {
    role: resolvedRole,
    helmet: resolvedHelmet,
    roleInfo: BUILD_ROLES[resolvedRole],
    helmetInfo: BUILD_HELMETS[resolvedHelmet]
  };
}

function buildLoadoutCatalog() {
  return {
    roles: Object.fromEntries(Object.entries(BUILD_ROLES).map(([key, value]) => [key, {
      ...value,
      id: key
    }])),
    helmets: Object.fromEntries(Object.entries(BUILD_HELMETS).map(([key, value]) => [key, {
      ...value,
      id: key
    }])),
    weapons: Object.fromEntries(Object.entries(WEAPON_DEFINITIONS).map(([key, value]) => [key, {
      ...value,
      id: key
    }])),
    sets: Object.fromEntries(Object.entries(LOADOUT_SETS).map(([key, value]) => [key, {
      ...value,
      id: key
    }]))
  };
}

function sanitizePremiumDesign(data = {}) {
  const weapon = String(data.designWeapon || data.weapon || 'sword').toLowerCase();
  const set = String(data.set || 'sunforge').toLowerCase();
  return {
    weapon: WEAPON_DEFINITIONS[weapon] ? weapon : 'sword',
    set: LOADOUT_SETS[set] ? set : 'sunforge'
  };
}

function getLootEquipmentStats(player) {
  const stats = { damage: 0, armor: 0, maxHp: 0, speed: 0, critChance: 0 };
  const bag = Array.isArray(player?.lootBag) ? player.lootBag : [];
  const equipment = sanitizeLootEquipment(player?.lootEquipment, bag);
  for (const item of Object.values(equipment)) {
    const definition = LootCatalog.ITEM_BY_ID[item.id];
    if (!definition) continue;
    for (const key of Object.keys(stats)) stats[key] += Number(definition.stats[key]) || 0;
  }
  stats.damage = Math.min(0.45, stats.damage);
  stats.armor = Math.min(0.4, stats.armor);
  stats.maxHp = Math.min(450, stats.maxHp);
  stats.speed = Math.min(0.15, stats.speed);
  stats.critChance = Math.min(0.1, stats.critChance);
  return stats;
}

function applyLoadoutStats(player) {
  if (!player) return;
  const loadout = sanitizePlayerLoadout(player.role, player.helmet);
  const premiumDesign = sanitizePremiumDesign({
    weapon: player.designWeapon || (typeof player.weapon === 'string' ? player.weapon : 'sword'),
    set: player.loadoutSet
  });
  const weaponStats = WEAPON_DEFINITIONS[premiumDesign.weapon] || WEAPON_DEFINITIONS.sword;
  const setBonus = LOADOUT_SETS[premiumDesign.set] || LOADOUT_SETS.sunforge;
  const roleStats = BUILD_ROLES[loadout.role] || BUILD_ROLES.tank;
  const helmetItemStats = player.helmetSkin ? getHelmetItemStats(player.helmetSkin) : null;
  const scytheItemStats = getScytheItemStats(player.scytheId || player.swordSkin);
  const lootStats = getLootEquipmentStats(player);
  const previousMaxHp = Number(player.maxHp) || 250;
  const hpMultiplier = (roleStats.maxHp || 1);
  const damageMultiplier = (roleStats.damage || 1) * (helmetItemStats?.damage || 1) * (scytheItemStats?.damage || 1) * (1 + lootStats.damage);
  const armorMultiplier = (roleStats.armor || 1) * (helmetItemStats?.armor || 1) * (1 + lootStats.armor);
  const speedMultiplier = (roleStats.speed || 1) * (helmetItemStats?.speed || 1) * (scytheItemStats?.speed || 1) * (1 + lootStats.speed);
  const premiumDamageBuffer = Number(weaponStats.damage || 1) * 1.05;
  const attackSpeedMultiplier = (Number(weaponStats.speed) || 1) * (helmetItemStats?.attackSpeed || 1) * (scytheItemStats?.attackSpeed || 1);
  const baseMaxHp = Number(player.baseMaxHp) || 250;
  player.baseMaxHp = baseMaxHp;
  player._loadoutBaseMaxHp = Math.max(130, Math.round(baseMaxHp * hpMultiplier));
  const bonusHp = helmetItemStats ? (helmetItemStats.maxHpBonus || 0) : 0;
  const combatHpBonus = (calculatePlayerLevel(player) - 1) * 2
    + (Math.max(1, Number(player.defenceLevel) || 1) - 1);
  player.maxHp = Math.max(130, player._loadoutBaseMaxHp + bonusHp + combatHpBonus + lootStats.maxHp);
  const previousHpValue = Number(player.hp);
  const previousHp = Number.isFinite(previousHpValue) ? Math.max(0, previousHpValue) : previousMaxHp;
  player.hp = previousHp <= 0
    ? 0
    : Math.min(player.maxHp, previousHp + Math.max(0, player.maxHp - previousMaxHp));
  player.damageMultiplier = damageMultiplier * premiumDamageBuffer;
  player.armorMultiplier = armorMultiplier;
  player.speedMultiplier = speedMultiplier * (Number(weaponStats.speed) || 1);
  player.attackSpeedMultiplier = attackSpeedMultiplier;
  player.harvestMultiplier = helmetItemStats?.harvestMult || 1.0;
  player.windmillMultiplier = helmetItemStats?.windmillMult || 1.0;
  player.lifesteal = helmetItemStats?.lifesteal || 0;
  player.critChance = Math.min(0.5, (helmetItemStats?.critChance || 0) + lootStats.critChance);
  player.critMultiplier = helmetItemStats?.critMultiplier || 1.0;
  player.burnEffect = Boolean(helmetItemStats?.burnEffect);
  player.dashBoost = Number(scytheItemStats?.dash || 1);
  player.itemStats = {
    helmet: helmetItemStats || null,
    scythe: scytheItemStats || null,
    loot: lootStats
  };
  player.role = loadout.role;
  player.helmet = loadout.helmet;
  player.designWeapon = premiumDesign.weapon;
  player.loadoutSet = premiumDesign.set;
  player.setInfo = setBonus;
  player.weaponInfo = weaponStats;
}

function persistPlayerEquipment(player) {
  const user = player?._authUser;
  if (!user) return;
  user.ownedAxes = normalizeOwnedTiers(player.ownedAxes);
  user.ownedSwords = normalizeOwnedTiers(player.ownedSwords);
  user.ownedHelmets = normalizeOwnedItemIds(player.ownedHelmets, /^helmet_[a-z0-9_]{1,48}$/);
  user.ownedScythes = normalizeOwnedItemIds(player.ownedScythes, /^scythe_tier_[1-8]$/);
  user.axeTier = user.ownedAxes.includes(Number(player.axeTier)) ? Number(player.axeTier) : 0;
  user.swordTier = user.ownedSwords.includes(Number(player.swordTier)) ? Number(player.swordTier) : 0;
  user.scytheId = user.ownedScythes.includes(player.scytheId) ? player.scytheId : null;
  user.helmetSkin = user.ownedHelmets.includes(player.helmetSkin) ? player.helmetSkin : null;
  user.meleeLevel = Math.max(1, Math.min(100, Number(player.meleeLevel) || 1));
  user.meleeXp = Math.max(0, Number(player.meleeXp) || 0);
  user.defenceLevel = Math.max(1, Math.min(100, Number(player.defenceLevel) || 1));
  user.defenceXp = Math.max(0, Number(player.defenceXp) || 0);
  saveAccountData();
}

function lootInventoryPayload(player) {
  const bag = sanitizeLootBag(player?.lootBag);
  const equipped = sanitizeLootEquipment(player?.lootEquipment, bag);
  return { bag, equipped, capacity: 32 };
}

function persistLootInventory(player) {
  if (!player) return;
  const inventory = lootInventoryPayload(player);
  player.lootBag = inventory.bag;
  player.lootEquipment = inventory.equipped;
  if (player._authUser) {
    player._authUser.lootBag = inventory.bag;
    player._authUser.lootEquipment = inventory.equipped;
    saveAccountData();
  }
}

function emitLootInventory(player, socket = io.sockets.sockets.get(player?.id)) {
  if (!player || !socket) return;
  persistLootInventory(player);
  socket.emit('loot_inventory_state', lootInventoryPayload(player));
}

function awardLoot(player, level, isBoss) {
  if (!player) return;
  const item = LootCatalog.rollLoot(level, isBoss);
  if (!item) return;
  const socket = io.sockets.sockets.get(player.id);
  if (!socket) return;
  player.lootBag = sanitizeLootBag(player.lootBag);
  if (player.lootBag.length >= 32) {
    socket.emit('loot_item_notice', { ok: false, message: 'Cantan dolu; ganimet alamadin.' });
    return;
  }
  const instance = { uid: crypto.randomUUID(), id: item.id };
  player.lootBag.push(instance);
  persistLootInventory(player);
  socket.emit('loot_inventory_state', lootInventoryPayload(player));
  socket.emit('loot_item_notice', { ok: true, item: instance, source: isBoss ? 'boss' : 'mob' });
}

function stealDeathLoot(killer, target) {
  if (!killer || !target || killer.id === target.id) return;
  const stealRate = 0.2;
  const goldStolen = Math.max(0, Math.floor((Number(target.gold) || 0) * stealRate));
  const scoreStolen = Math.max(0, Math.floor((Number(target.score) || 0) * stealRate));
  const woodStolen = Math.max(0, Math.floor((Number(target.wood) || 0) * stealRate));
  const stoneStolen = Math.max(0, Math.floor((Number(target.stone) || 0) * stealRate));
  if (goldStolen > 0) {
    killer.gold = (killer.gold || 0) + goldStolen;
    target.gold = Math.max(0, (target.gold || 0) - goldStolen);
  }
  if (scoreStolen > 0) {
    killer.score = (killer.score || 0) + scoreStolen;
    target.score = Math.max(0, (target.score || 0) - scoreStolen);
  }
  if (woodStolen > 0) {
    killer.wood = (killer.wood || 0) + woodStolen;
    target.wood = Math.max(0, (target.wood || 0) - woodStolen);
  }
  if (stoneStolen > 0) {
    killer.stone = (killer.stone || 0) + stoneStolen;
    target.stone = Math.max(0, (target.stone || 0) - stoneStolen);
  }
  persistPlayerScore(killer);
  persistPlayerScore(target);
}

function updateBounty() {
  if (!BOUNTY_EVENT_ENABLED) {
    if (currentBountyId !== null) {
      currentBountyId = null;
      io.emit('bounty_update', { id: null });
    }
    return;
  }
  if (currentBountyId) {
    const current = players.get(currentBountyId);
    if (!current || (current.hp ?? 0) <= 0 || current._dead || !io.sockets.sockets.get(currentBountyId)?.connected) {
      currentBountyId = null;
      io.emit('bounty_update', { id: null });
    }
  }
  if (!currentBountyId && players.size > 0) {
    let topCandidate = null;
    for (const p of players.values()) {
      if (!p || p.isBot || isBotLeaderboardName(p.name) || (p.hp ?? 0) <= 0 || p._dead) continue;
      if (!io.sockets.sockets.get(p.id)?.connected) continue;
      if (!topCandidate || (p.score || 0) > (topCandidate.score || 0)) {
        topCandidate = p;
      }
    }
    if (topCandidate && (topCandidate.score || 0) >= 100) {
      currentBountyId = topCandidate.id;
      io.emit('bounty_update', { id: currentBountyId, name: topCandidate.name, score: topCandidate.score });
    }
  }
}

function releaseTrapVictims(trapId) {
  for (const player of players.values()) {
    if (player.trappedBy === trapId) releaseTrapVictim(player.id, trapId);
  }
}

function alertBotAttacked(bot, attacker) {
  if (!bot || !bot.isBot || !attacker || (bot.hp ?? 0) <= 0 || bot._dead) return;
  bot._lastAttackedBy = attacker.id;
  bot.target = { id: attacker.id, x: attacker.x, y: attacker.y, entity: attacker, type: 'player' };
  bot.targetChangeAt = Date.now() + 5000;
  bot.weapon = 2; // Immediately switch to sword
  if (bot.clanId && typeof botList !== 'undefined') {
    for (const [otherId, ally] of botList) {
      if (otherId === bot.id || !ally || (ally.hp ?? 0) <= 0 || ally._dead || ally.clanId !== bot.clanId) continue;
      const d = Math.hypot(ally.x - bot.x, ally.y - bot.y);
      if (d < 700 && (!ally.target || ally.target.type !== 'player')) {
        ally.target = { id: attacker.id, x: attacker.x, y: attacker.y, entity: attacker, type: 'player' };
        ally.targetChangeAt = Date.now() + 4000;
        ally.weapon = 2;
      }
    }
  }
}

function onPlayerDeath(playerId) {
  if (!playerId) return;
  releaseTrapVictim(playerId);
  deletePlayerBuildings(playerId);
  const target = players.get(playerId);
  if (target) {
    if (!target.isBot && !target._matchFinalized) {
      const matchKills = Math.max(0, (Number(target.kills) || 0) - (Number(target.matchStartKills) || 0));
      const matchScore = Math.max(0, (Number(target.score) || 0) - (Number(target.matchStartScore) || 0));
      const matchGold = Math.max(0, (Number(target.gold) || 0) - (Number(target.matchStartGold) || 0));
      const matchTime = Math.max(0, Math.min(86400, Math.floor((Date.now() - (Number(target.matchStartedAt) || Date.now())) / 1000)));
      recordServerQuestProgress(target, { kills: matchKills, time: Math.floor(matchTime / 60) });
      recordDeathScore(target.name, matchScore, matchGold, matchKills, matchTime, target._authUser, Boolean(target._authUser));
      target._matchFinalized = true;
    }
    target.wood = 0;
    target.stone = 0;
    target.gold = 0;
    target.diamond = 0;
    target.amethyst = 0;
    target.redite = 0;
    target.apples = 5;
    target.score = 0;
    target.sc = 0;
    persistPlayerEquipment(target);
    target._dead = true;
    if (target.isBot) {
      target.trappedBy = null;
      target.trappedUntil = 0;
      target.trappedX = null;
      target.trappedY = null;
      target.target = null;
      target.targetChangeAt = 0;
      target.vx = 0;
      target.vy = 0;
      target.baseBuildingIds = [];
      target.defSpikes = [];
    }
    if (target.isBot && typeof scheduleBotRespawn === 'function') {
      scheduleBotRespawn(target);
    }
    if (target._guestId) {
      reconnectSessions.delete(target._guestId);
    }
  }
}

function resolveTrapCapturePoint(target, trap) {
  if (!target || !trap) return { x: Number(target?.x) || 0, y: Number(target?.y) || 0 };
  const trapX = Number(trap.x) || 0;
  const trapY = Number(trap.y) || 0;
  const trapRadius = Number(trap.radius) || 78;
  const targetX = Number(target.x) || 0;
  const targetY = Number(target.y) || 0;
  const dx = targetX - trapX;
  const dy = targetY - trapY;
  const dist = Math.hypot(dx, dy) || 1;
  const orbitRadius = Math.max(18, Math.min(trapRadius - 12, trapRadius - 22));
  const hash = Array.from(String(target.id || `${targetX}:${targetY}`)).reduce((acc, ch) => acc + ch.charCodeAt(0), 0);
  const angleBias = ((hash % 997) / 997) * Math.PI * 2;
  if (dist < 1) {
    return {
      x: trapX + Math.cos(angleBias) * orbitRadius,
      y: trapY + Math.sin(angleBias) * orbitRadius,
    };
  }
  const nx = dx / dist;
  const ny = dy / dist;
  return {
    x: trapX + nx * orbitRadius,
    y: trapY + ny * orbitRadius,
  };
}

function applyTrapVictimState(target, trapId, trapX = target?.x, trapY = target?.y) {
  if (!target || !trapId) return false;
  const trap = buildings.get(trapId);
  if (!trap || trap.type !== 6 || (trap.hp ?? 0) <= 0) {
    return releaseTrapVictim(target.id, trapId);
  }
  const capturePoint = resolveTrapCapturePoint({ ...target, x: Number.isFinite(Number(trapX)) ? Number(trapX) : (Number(target.x) || 0), y: Number.isFinite(Number(trapY)) ? Number(trapY) : (Number(target.y) || 0) }, trap);
  target.trappedBy = trapId;
  target.trappedX = normalizeWorldCoord(capturePoint.x, target.x || 0);
  target.trappedY = normalizeWorldCoord(capturePoint.y, target.y || 0);
  target.x = target.trappedX;
  target.y = target.trappedY;
  target.vx = 0;
  target.vy = 0;
  broadcastTrapStateNear(target, {
    id: target.id, trappedBy: trapId, trappedX: target.trappedX, trappedY: target.trappedY,
    x: target.x, y: target.y, at: Date.now()
  });
  return true;
}

function releaseTrapVictim(playerId, trapId = null) {
  const target = players.get(playerId);
  if (!target || !target.trappedBy) return false;
  const activeTrapId = trapId ?? target.trappedBy;
  if (!activeTrapId || (trapId && target.trappedBy !== trapId)) return false;
  const trap = buildings.get(activeTrapId);
  const ownerId = trap?.ownerId || null;
  target.trappedBy = null;
  target.trappedX = null;
  target.trappedY = null;
  target.vx = 0;
  target.vy = 0;
  broadcastTrapStateNear(target, {
    id: target.id, trappedBy: null, trappedX: null, trappedY: null,
    x: target.x, y: target.y, at: Date.now()
  });
  io.to(playerId).emit('trap_freed', { buildingId: activeTrapId });
  if (ownerId) {
    io.to(ownerId).emit('trap_victim_freed', { victimId: playerId, buildingId: activeTrapId });
  }
  return true;
}

function capturePlayerInTrap(target) {
  if (!target || target.hp <= 0 || target.trappedBy) return false;
  for (const building of buildings.values()) {
    if (building.type !== 6 || (building.hp ?? 0) <= 0 || building.ownerId === target.id) continue;
    const dx = (Number(target.x) || 0) - (Number(building.x) || 0);
    const dy = (Number(target.y) || 0) - (Number(building.y) || 0);
    const triggerRadius = trapCaptureRadius(building, target.radius || 34);
    if (dx * dx + dy * dy > triggerRadius * triggerRadius) continue;
    if (!applyTrapVictimState(target, building.id, target.x, target.y)) continue;
    io.to(target.id).emit('trap_caught', { buildingId: building.id, x: target.x, y: target.y });
    broadcastPlayerEventNear(target, 'trap_triggered', { buildingId: building.id, victimId: target.id, x: target.x, y: target.y });
    return true;
  }
  return false;
}

function capturePlayerInSpecificTrap(target, building) {
  if (!target || target.hp <= 0 || target.trappedBy || !building) return false;
  if (building.type !== 6 || (building.hp ?? 0) <= 0 || building.ownerId === target.id) return false;
  const dx = (Number(target.x) || 0) - (Number(building.x) || 0);
  const dy = (Number(target.y) || 0) - (Number(building.y) || 0);
  const triggerRadius = trapCaptureRadius(building, target.radius || 34);
  if (dx * dx + dy * dy > triggerRadius * triggerRadius) return false;
  if (!applyTrapVictimState(target, building.id, target.x, target.y)) return false;
  io.to(target.id).emit('trap_caught', { buildingId: building.id, x: target.x, y: target.y });
  broadcastPlayerEventNear(target, 'trap_triggered', { buildingId: building.id, victimId: target.id, x: target.x, y: target.y });
  return true;
}

function pushTrappedVictim(owner, target, dx, dy, requestedStep = 1) {
  if (!owner || !target || !target.trappedBy || target.hp <= 0) return false;
  const trap = buildings.get(target.trappedBy);
  if (!trap || trap.ownerId !== owner.id || (trap.hp ?? 0) <= 0) return false;
  const length = Math.hypot(dx, dy) || 1;
  const cooldownKey = `${owner.id}:${target.id}`;
  const now = Date.now();
  if (now - (trapPushCooldowns.get(cooldownKey) || 0) < 14) return false;
  trapPushCooldowns.set(cooldownKey, now);

  const ownerRad = Number(owner.radius) || 35;
  const targetRad = Number(target.radius) || 35;
  const minDist = ownerRad + targetRad;
  const trapRad = Number(trap.radius) || 78;
  const leashRadius = trapRad + 26; // 104 px

  const currentDist = Math.hypot((Number(target.x) || 0) - (Number(owner.x) || 0), (Number(target.y) || 0) - (Number(owner.y) || 0)) || 1;
  const nx = dx / length;
  const ny = dy / length;

  // Determine push step: if overlapping, push at least the overlap amount
  const overlap = Math.max(0, minDist - currentDist);
  const step = Math.min(8.0, Math.max(overlap > 0 ? overlap : 0.8, Number(requestedStep) || 1));
  const pushX = nx * step;
  const pushY = ny * step;

  let proposedX = (Number(target.trappedX ?? target.x) || 0) + pushX;
  let proposedY = (Number(target.trappedY ?? target.y) || 0) + pushY;

  // 1. Clamp to Trap Leash boundary
  const trapDx = proposedX - (Number(trap.x) || 0);
  const trapDy = proposedY - (Number(trap.y) || 0);
  const trapDistance = Math.hypot(trapDx, trapDy);
  if (trapDistance > leashRadius) {
    proposedX = (Number(trap.x) || 0) + (trapDx / (trapDistance || 1)) * leashRadius;
    proposedY = (Number(trap.y) || 0) + (trapDy / (trapDistance || 1)) * leashRadius;
  }

  // 2. Solid obstacle & spike collision for the pushed victim
  for (const b of nearbyBuildings(proposedX, proposedY, targetRad + 60)) {
    if (b.id === trap.id || b.type === 5 || (b.hp ?? 0) <= 0) continue;
    const bRad = Number(b.radius) || (b.type === 8 ? 24 : (b.type === 6 ? 78 : (b.type === 10 ? 30 : 36)));
    const bdx = proposedX - b.x;
    const bdy = proposedY - b.y;
    const bDist = Math.hypot(bdx, bdy) || 0.01;
    const minBDist = targetRad + bRad;
    if (bDist < minBDist) {
      // If obstacle is a Spike, deal spike damage authoritatively!
      if (b.type === 3) {
        applySpikeDamageToTarget(target, b, now, true);
      }
      // Repel proposed position out of the obstacle
      const bnx = bdx / bDist;
      const bny = bdy / bDist;
      proposedX = b.x + bnx * minBDist;
      proposedY = b.y + bny * minBDist;
    }
  }

  target.trappedX = proposedX;
  target.trappedY = proposedY;
  target.x = proposedX;
  target.y = proposedY;
  target.vx = 0;
  target.vy = 0;

  // 3. ZERO-CLIPPING CONSTRAINT ON OWNER:
  // The owner's body can NEVER penetrate into the victim's body.
  // If the victim cannot move further (hit leash or hit obstacle), owner must be stopped outside the victim!
  const finalDx = target.x - (Number(owner.x) || 0);
  const finalDy = target.y - (Number(owner.y) || 0);
  const finalDist = Math.hypot(finalDx, finalDy) || 0.01;
  if (finalDist < minDist) {
    const pen = minDist - finalDist;
    const fnx = finalDx / finalDist;
    const fny = finalDy / finalDist;
    owner.x -= fnx * pen;
    owner.y -= fny * pen;
    if (owner.vx !== undefined && owner.vy !== undefined) {
      NetworkPhysics.projectVelocitySlide(owner, -fnx, -fny, 0.05);
    }
  }

  broadcastTrapStateNear(target, {
    id: target.id, trappedBy: target.trappedBy, trappedX: target.trappedX, trappedY: target.trappedY,
    x: target.x, y: target.y, at: now
  });
  io.to(target.id).emit('trap_victim_push', { dx: pushX, dy: pushY, x: target.x, y: target.y });
  broadcastPlayerStateNear(target);
  broadcastPlayerStateNear(owner);
  return true;
}

function dedupeTrapState(target, trapId) {
  if (!target || !trapId) return false;
  const trap = buildings.get(trapId);
  if (!trap || trap.type !== 6 || (trap.hp ?? 0) <= 0) {
    return releaseTrapVictim(target.id, trapId);
  }
  const trapDx = (Number(target.x) || 0) - (Number(trap.x) || 0);
  const trapDy = (Number(target.y) || 0) - (Number(trap.y) || 0);
  const leashRadius = (Number(trap.radius) || 78) + 26;
  if (trapDx * trapDx + trapDy * trapDy > leashRadius * leashRadius) {
    target.x = Number(trap.x) + (trapDx / (Math.hypot(trapDx, trapDy) || 1)) * leashRadius;
    target.y = Number(trap.y) + (trapDy / (Math.hypot(trapDx, trapDy) || 1)) * leashRadius;
    target.trappedX = target.x;
    target.trappedY = target.y;
    broadcastTrapStateNear(target, {
      id: target.id, trappedBy: trapId, trappedX: target.trappedX, trappedY: target.trappedY,
      x: target.x, y: target.y, at: Date.now()
    });
  }
  return true;
}

function enforceCanonicalTrapLock(target) {
  if (!target || !target.trappedBy) return false;
  const trap = buildings.get(target.trappedBy);
  if (!trap || trap.type !== 6 || (trap.hp ?? 0) <= 0) {
    return releaseTrapVictim(target.id, target.trappedBy);
  }
  const trapX = Number(trap.x) || 0;
  const trapY = Number(trap.y) || 0;
  const currentX = Number(target.x) || 0;
  const currentY = Number(target.y) || 0;
  const trapDx = currentX - trapX;
  const trapDy = currentY - trapY;
  const leashRadius = (Number(trap.radius) || 78) + 26;
  const distance = Math.hypot(trapDx, trapDy) || 1;
  if (distance > leashRadius) {
    const clampedX = trapX + (trapDx / distance) * leashRadius;
    const clampedY = trapY + (trapDy / distance) * leashRadius;
    target.x = clampedX;
    target.y = clampedY;
    target.trappedX = clampedX;
    target.trappedY = clampedY;
    target.vx = 0;
    target.vy = 0;
    broadcastTrapStateNear(target, {
      id: target.id,
      trappedBy: target.trappedBy,
      trappedX: target.trappedX,
      trappedY: target.trappedY,
      x: target.x,
      y: target.y,
      at: Date.now()
    });
    return true;
  }
  if (target.trappedX == null || target.trappedY == null) {
    target.trappedX = currentX;
    target.trappedY = currentY;
  }
  return true;
}

function resolveTrapOwnerCollisions(owner) {
  if (!owner || owner.hp <= 0) return;
  const ownerRadius = Number(owner.radius) || 35;
  for (const target of players.values()) {
    if (target.id === owner.id || !target.trappedBy || target.hp <= 0) continue;
    const trap = buildings.get(target.trappedBy);
    if (!trap || trap.ownerId !== owner.id) continue;
    const dx = (Number(target.x) || 0) - (Number(owner.x) || 0);
    const dy = (Number(target.y) || 0) - (Number(owner.y) || 0);
    const distance = Math.hypot(dx, dy) || 0.01;
    const targetRadius = Number(target.radius) || 35;
    const minDist = ownerRadius + targetRadius;
    if (distance < minDist + 10) {
      const pushStep = Math.max(1.2, (minDist - distance) + 1.0);
      pushTrappedVictim(owner, target, dx, dy, pushStep);
    }
  }
}

function broadcastMobIds() {
  rebuildMobGrid();
  for (const [id, player] of players) {
    const socket = io.sockets.sockets.get(id);
    if (!socket) continue;
    const visibleMobs = nearbyMobs(player.x, player.y, MOB_AOI_RADIUS);
    player.visibleMobIds = new Set(visibleMobs.map(mob => mob.id));
    socket.emit('mob_ids', [...player.visibleMobIds]);
    socket.emit('mob_states', visibleMobs.map(publicMob));
  }
}

// The server owns mob positions so every connected player renders the same world.
let lastMobTickAt = Date.now();
setInterval(() => {
  const hasSpectators = [...io.sockets.sockets.values()].some(client => client.data.isSpectator);
  if (players.size === 0 && !hasSpectators) return;
  ensureMobs();
  const changed = [];
  const now = Date.now();
  const tickScale = Math.max(0.2, Math.min(2.5, (now - lastMobTickAt) / 50));
  lastMobTickAt = now;
  for (const mob of mobs.values()) {
    mob.stateSeq = (mob.stateSeq || 0) + 1;
    mob.stateAt = now;
    if (mob.trappedBy) {
      const b = buildings.get(mob.trappedBy);
      if (b && (b.hp ?? 100) > 0 && now < (mob.trappedUntil || 0)) {
        mob.vx = 0;
        mob.vy = 0;
        mob.x = mob.trappedX ?? mob.x;
        mob.y = mob.trappedY ?? mob.y;
        applyMobTrapDamage(mob, b, now);
        if (mob.hp <= 0) continue;
        for (const spike of nearbyBuildings(mob.x, mob.y, mob.radius + 90)) {
          const dx = mob.x - spike.x;
          const dy = mob.y - spike.y;
          const hitRadius = (mob.radius || 36) + (spike.radius || 34);
          if (dx * dx + dy * dy <= hitRadius * hitRadius) applyMobSpikeDamage(mob, spike, now);
        }
        changed.push(publicMob(mob));
        continue; // Mob is trapped in place — CANNOT chase or attack distant players!
      } else {
        const expiredTrapId = mob.trappedBy;
        mob.trappedBy = null;
        mob.trappedUntil = 0;
        if (expiredTrapId) {
          mob.trapIgnoreBuildingId = expiredTrapId;
          mob.trapIgnoreUntil = now + MOB_TRAP_REENTRY_COOLDOWN_MS;
        }
        mob.trapDamageBuildingId = null;
        mob.lastTrapDamageAt = 0;
        io.emit('mob_freed', {
          mobId: mob.id,
          buildingId: expiredTrapId || null,
          ignoreUntil: mob.trapIgnoreUntil || 0
        });
      }
    }

    let target = mob.targetId ? players.get(mob.targetId) : null;
    if (target && !isMobTargetEligible(mob, target)) target = null;
    if (!target || (target.hp ?? 0) <= 0 || isInsideSafeVillage(target.x, target.y)) {
      mob.targetId = null;
      mob.chaseStartedAt = 0;
      mob.chaseUntil = 0;
      target = null;
    }
    if (target && mob.chaseStartedAt && now - mob.chaseStartedAt >= MOB_CHASE_TIMEOUT) {
      mob.ignoreTargetId = target.id;
      mob.ignoreTargetUntil = now + MOB_REAGGRO_DELAY;
      mob.targetId = null;
      mob.chaseStartedAt = 0;
      mob.chaseUntil = 0;
      mob.hp = Math.min(mob.maxHp, mob.hp + Math.round(mob.maxHp * 0.15));
      target = null;
    }
    if (now >= (mob.ignoreTargetUntil || 0)) mob.ignoreTargetId = null;
    if (!target) {
      if (mob.targetId && players.has(mob.targetId)) {
        const prior = players.get(mob.targetId);
        if (prior && (prior.hp ?? 0) > 0 && !prior._dead && isMobTargetEligible(mob, prior)) {
          target = prior;
        } else {
          mob.targetId = null;
          mob.chaseStartedAt = 0;
          mob.chaseUntil = 0;
        }
      } else if (!mob.isPeaceful) {
        // Hostile wild beasts scan for nearby players outside the safe buffer zone
        const nearby = nearbyPlayers(mob.x, mob.y, MOB_AGGRO_RANGE);
        for (let pi = 0; pi < nearby.length; pi++) {
          const candidate = nearby[pi];
          if (candidate.id !== mob.ignoreTargetId && isMobTargetEligible(mob, candidate)) {
            target = candidate;
            setMobTarget(mob, candidate.id, now);
            break;
          }
        }
      }
    }

    // Leash tether check: if mob has chased too far from its home anchor, disengage and return
    const homeX = mob.homeX ?? mob.x;
    const homeY = mob.homeY ?? mob.y;
    const leash = mob.leashRadius || 550;
    const distFromHome = Math.hypot(mob.x - homeX, mob.y - homeY);
    if (target && distFromHome > leash * 1.3) {
      mob.ignoreTargetId = target.id;
      mob.ignoreTargetUntil = now + MOB_REAGGRO_DELAY;
      mob.targetId = null;
      mob.chaseStartedAt = 0;
      mob.chaseUntil = 0;
      target = null;
      mob.hp = Math.min(mob.maxHp, mob.hp + Math.round(mob.maxHp * 0.15));
    }
    const isEnraged = (mob.hp ?? mob.maxHp) < mob.maxHp * 0.4;
    if (isEnraged && !mob.isEnraged) {
      mob.isEnraged = true;
      broadcastMobEventNear(mob, 'mob_enraged', { id: mob.id, typeName: mob.typeName, x: Math.round(mob.x), y: Math.round(mob.y) });
    } else if (!isEnraged && mob.isEnraged) {
      mob.isEnraged = false;
    }

    const targetDistance = target ? ((target.x - mob.x) ** 2 + (target.y - mob.y) ** 2) : Infinity;
    if (target && now < mob.chaseUntil) {
      const distance = Math.sqrt(targetDistance);
      const spd = ((mob.speed || MOB_SPEED) * 0.5) * (mob.isEnraged ? 1.28 : 1.0);
      const stopDistance = (mob.radius || MOB_RADIUS) + 30;
      const targetAngle = distance > 1 ? Math.atan2(target.y - mob.y, target.x - mob.x) : mob.angle;
      mob.angle = targetAngle;
      const approachDistance = Math.max(0, distance - stopDistance);
      const chaseSpeed = Math.min(spd, approachDistance / tickScale);
      mob.vx = Math.cos(targetAngle) * chaseSpeed;
      mob.vy = Math.sin(targetAngle) * chaseSpeed;

      let abilityFired = false;
      const shape = mob.shape || '';

      // Biome Signature Abilities
      if ((shape === 'spider' || shape === 'orumcek') && distance < 300 && distance > 70 && now >= (mob.nextAbilityAt || 0) && now - (mob.lastWebAt || 0) >= (mob.isEnraged ? 2500 : 3500)) {
        mob.lastWebAt = now;
        mob.nextAbilityAt = now + (mob.isEnraged ? 2500 : 3500);
        mob.nextAttackAt = now + (mob.isEnraged ? 900 : 1300);
        mob.chaseUntil = now + MOB_CHASE_TIMEOUT;
        mob.state = 'attack';
        const webDmg = 18;
        const webDamage = applyMobDamage(mob, target, webDmg, true);
        broadcastMobEventNear(mob, 'mob_attack', {
          id: mob.id, targetId: target.id, dmg: webDamage?.dmg ?? 0, hp: webDamage?.hp, hpSeq: webDamage?.hpSeq,
          typeName: mob.typeName, shape: mob.shape, isWeb: true,
          x: mob.x, y: mob.y, angle: mob.angle, targetX: target.x, targetY: target.y, seq: mob.stateSeq, ts: mob.stateAt
        });
        abilityFired = true;
      } else if (shape === 'polar_bear' && distance < 150 && now >= (mob.nextAbilityAt || 0)) {
        mob.nextAbilityAt = now + 4500;
        mob.nextAttackAt = now + (mob.isEnraged ? 800 : 1100);
        mob.chaseUntil = now + MOB_CHASE_TIMEOUT;
        mob.state = 'attack';
        const slamDmg = 65;
        const damageRes = applyMobDamage(mob, target, slamDmg);
        broadcastMobEventNear(mob, 'mob_ability', {
          id: mob.id, ability: 'glacial_slam', targetId: target.id, dmg: damageRes?.dmg ?? 0, hp: damageRes?.hp,
          x: mob.x, y: mob.y, targetX: target.x, targetY: target.y, radius: 150, shape
        });
        abilityFired = true;
      } else if (shape === 'frost_fox' && distance > 90 && distance < 280 && now >= (mob.nextAbilityAt || 0)) {
        mob.nextAbilityAt = now + 3500;
        mob.nextAttackAt = now + (mob.isEnraged ? 750 : 1100);
        mob.chaseUntil = now + MOB_CHASE_TIMEOUT;
        mob.state = 'attack';
        const dashDist = Math.min(80, Math.max(20, distance - 40));
        mob.x += Math.cos(targetAngle) * (dashDist * 0.35);
        mob.y += Math.sin(targetAngle) * (dashDist * 0.35);
        mob.vx = Math.cos(targetAngle) * spd * 1.8;
        mob.vy = Math.sin(targetAngle) * spd * 1.8;
        const dashDmg = 45;
        const damageRes = applyMobDamage(mob, target, dashDmg);
        broadcastMobEventNear(mob, 'mob_ability', {
          id: mob.id, ability: 'frost_dash', targetId: target.id, dmg: damageRes?.dmg ?? 0, hp: damageRes?.hp,
          x: mob.x, y: mob.y, targetX: target.x, targetY: target.y, shape
        });
        abilityFired = true;
      } else if (shape === 'mammoth' && distance < 260 && now >= (mob.nextAbilityAt || 0)) {
        mob.nextAbilityAt = now + 5500;
        mob.nextAttackAt = now + (mob.isEnraged ? 900 : 1200);
        mob.chaseUntil = now + MOB_CHASE_TIMEOUT;
        mob.state = 'attack';
        const chargeDist = Math.min(70, Math.max(20, distance - 30));
        mob.x += Math.cos(targetAngle) * (chargeDist * 0.35);
        mob.y += Math.sin(targetAngle) * (chargeDist * 0.35);
        mob.vx = Math.cos(targetAngle) * spd * 1.6;
        mob.vy = Math.sin(targetAngle) * spd * 1.6;
        const trampleDmg = 80;
        const damageRes = applyMobDamage(mob, target, trampleDmg);
        broadcastMobEventNear(mob, 'mob_ability', {
          id: mob.id, ability: 'trample', targetId: target.id, dmg: damageRes?.dmg ?? 0, hp: damageRes?.hp,
          x: mob.x, y: mob.y, targetX: target.x, targetY: target.y, shape
        });
        abilityFired = true;
      } else if (shape === 'sand_viper' && distance > 80 && distance < 340 && now >= (mob.nextAbilityAt || 0)) {
        mob.nextAbilityAt = now + 3000;
        mob.nextAttackAt = now + (mob.isEnraged ? 750 : 1100);
        mob.chaseUntil = now + MOB_CHASE_TIMEOUT;
        mob.state = 'attack';
        const spitDmg = 38;
        const damageRes = applyMobDamage(mob, target, spitDmg, true);
        broadcastMobEventNear(mob, 'mob_ability', {
          id: mob.id, ability: 'venom_spit', targetId: target.id, dmg: damageRes?.dmg ?? 0, hp: damageRes?.hp,
          x: mob.x, y: mob.y, targetX: target.x, targetY: target.y, shape
        });
        abilityFired = true;
      } else if (shape === 'dune_scorpion' && distance < 110 && now >= (mob.nextAbilityAt || 0)) {
        mob.nextAbilityAt = now + 5000;
        mob.nextAttackAt = now + (mob.isEnraged ? 800 : 1100);
        mob.chaseUntil = now + MOB_CHASE_TIMEOUT;
        mob.state = 'attack';
        const clampDmg = 55;
        const damageRes = applyMobDamage(mob, target, clampDmg);
        broadcastMobEventNear(mob, 'mob_ability', {
          id: mob.id, ability: 'pincer_clamp', targetId: target.id, dmg: damageRes?.dmg ?? 0, hp: damageRes?.hp,
          x: mob.x, y: mob.y, targetX: target.x, targetY: target.y, shape
        });
        abilityFired = true;
      } else if (shape === 'dune_lizard' && distance < 130 && now >= (mob.nextAbilityAt || 0)) {
        mob.nextAbilityAt = now + 4000;
        mob.nextAttackAt = now + (mob.isEnraged ? 750 : 1100);
        mob.chaseUntil = now + MOB_CHASE_TIMEOUT;
        mob.state = 'attack';
        const whipDmg = 50;
        const damageRes = applyMobDamage(mob, target, whipDmg);
        broadcastMobEventNear(mob, 'mob_ability', {
          id: mob.id, ability: 'tail_whip', targetId: target.id, dmg: damageRes?.dmg ?? 0, hp: damageRes?.hp,
          x: mob.x, y: mob.y, targetX: target.x, targetY: target.y, shape
        });
        abilityFired = true;
      } else if (shape === 'magma_hound' && distance > 80 && distance < 260 && now >= (mob.nextAbilityAt || 0)) {
        mob.nextAbilityAt = now + 3200;
        mob.nextAttackAt = now + (mob.isEnraged ? 750 : 1100);
        mob.chaseUntil = now + MOB_CHASE_TIMEOUT;
        mob.state = 'attack';
        const pounceDist = Math.min(80, Math.max(20, distance - 30));
        mob.x += Math.cos(targetAngle) * (pounceDist * 0.35);
        mob.y += Math.sin(targetAngle) * (pounceDist * 0.35);
        mob.vx = Math.cos(targetAngle) * spd * 1.8;
        mob.vy = Math.sin(targetAngle) * spd * 1.8;
        const pounceDmg = 60;
        const damageRes = applyMobDamage(mob, target, pounceDmg);
        broadcastMobEventNear(mob, 'mob_ability', {
          id: mob.id, ability: 'blaze_pounce', targetId: target.id, dmg: damageRes?.dmg ?? 0, hp: damageRes?.hp,
          x: mob.x, y: mob.y, targetX: target.x, targetY: target.y, shape
        });
        abilityFired = true;
      } else if (shape === 'fire_drake' && distance < 280 && now >= (mob.nextAbilityAt || 0)) {
        mob.nextAbilityAt = now + 4200;
        mob.nextAttackAt = now + (mob.isEnraged ? 800 : 1100);
        mob.chaseUntil = now + MOB_CHASE_TIMEOUT;
        mob.state = 'attack';
        const breathDmg = 70;
        const damageRes = applyMobDamage(mob, target, breathDmg);
        broadcastMobEventNear(mob, 'mob_ability', {
          id: mob.id, ability: 'inferno_breath', targetId: target.id, dmg: damageRes?.dmg ?? 0, hp: damageRes?.hp,
          x: mob.x, y: mob.y, targetX: target.x, targetY: target.y, angle: mob.angle, shape
        });
        abilityFired = true;
      } else if (shape === 'obsidian_golem' && distance < 190 && now >= (mob.nextAbilityAt || 0)) {
        mob.nextAbilityAt = now + 6000;
        mob.nextAttackAt = now + (mob.isEnraged ? 900 : 1200);
        mob.chaseUntil = now + MOB_CHASE_TIMEOUT;
        mob.state = 'attack';
        const quakeDmg = 85;
        const damageRes = applyMobDamage(mob, target, quakeDmg);
        broadcastMobEventNear(mob, 'mob_ability', {
          id: mob.id, ability: 'seismic_quake', targetId: target.id, dmg: damageRes?.dmg ?? 0, hp: damageRes?.hp,
          x: mob.x, y: mob.y, targetX: target.x, targetY: target.y, radius: 190, shape
        });
        abilityFired = true;
      }

      // Standard melee attack if no ability fired and in contact range
      if (!abilityFired && distance < (mob.radius + 60) && now >= (mob.nextAttackAt || 0) && now - (target.stateAt || 0) < 2500) {
        const meleeDamage = applyMobDamage(mob, target, mob.dmg);
        mob.nextAttackAt = now + (mob.isEnraged ? 800 : 1200);
        mob.chaseUntil = now + MOB_CHASE_TIMEOUT;
        mob.state = 'attack';
        broadcastMobEventNear(mob, 'mob_attack', {
          id: mob.id, targetId: target.id, dmg: meleeDamage?.dmg ?? 0, hp: meleeDamage?.hp, hpSeq: meleeDamage?.hpSeq,
          typeName: mob.typeName, shape: mob.shape,
          x: mob.x, y: mob.y, angle: mob.angle, targetX: target.x, targetY: target.y, seq: mob.stateSeq, ts: mob.stateAt
        });
      } else if (mob.state === 'attack' && now >= (mob.nextAttackAt || 0) - 600) {
        mob.state = 'walk';
      }

      if (target && (target.hp ?? 0) <= 0) {
        onPlayerDeath(target.id);
        io.to(target.id).emit('pvp_killed', { byName: mob.typeName });
        io.emit('player_dead', { id: target.id });
      }
    } else {
      mob.targetId = null;
      mob.state = 'walk';
      const homeX = mob.homeX ?? mob.x;
      const homeY = mob.homeY ?? mob.y;
      const leash = mob.leashRadius || 550;
      const distFromHome = Math.hypot(mob.x - homeX, mob.y - homeY);
      if (distFromHome > leash * 0.8) {
        mob.wanderTargetAngle = Math.atan2(homeY - mob.y, homeX - mob.x);
      } else if (now >= (mob.nextWanderTurnAt || 0)) {
        mob.wanderTargetAngle = mob.wanderAngle + (Math.random() - 0.5) * 1.2;
        mob.nextWanderTurnAt = now + 2500 + Math.random() * 2500;
      }
      const wanderTurn = Math.atan2(
        Math.sin(mob.wanderTargetAngle - mob.wanderAngle),
        Math.cos(mob.wanderTargetAngle - mob.wanderAngle)
      );
      const maxWanderTurn = 0.045 * tickScale;
      mob.wanderAngle += Math.max(-maxWanderTurn, Math.min(maxWanderTurn, wanderTurn));
      const wspd = (mob.wanderSpeed || MOB_WANDER_SPEED) * 0.5;

      // Biome-aware wandering boundaries
      const mb = mob.biome || 'forest';
      let minX = -4400, maxX = 4400, minY = -4400, maxY = 4400;
      if (mb === 'winter') {
        minX = -4400; maxX = 4400; minY = -6700; maxY = -4720;
      } else if (mb === 'desert') {
        minX = 4720; maxX = 6700; minY = -4400; maxY = 4400;
      } else if (mb === 'lava') {
        if (mob.y > 4400) { minX = -4400; maxX = 4400; minY = 4720; maxY = 6700; }
        else { minX = -6700; maxX = -4720; minY = -4400; maxY = 4400; }
      }

      if (mob.x > maxX) { mob.wanderAngle = Math.PI * (0.8 + Math.random() * 0.4); mob.x = maxX - 10; }
      else if (mob.x < minX) { mob.wanderAngle = Math.random() * 0.4 * Math.PI - 0.2 * Math.PI; mob.x = minX + 10; }
      if (mob.y > maxY) { mob.wanderAngle = -Math.PI * (0.3 + Math.random() * 0.4); mob.y = maxY - 10; }
      else if (mob.y < minY) { mob.wanderAngle = Math.PI * (0.3 + Math.random() * 0.4); mob.y = minY + 10; }

      mob.angle = mob.wanderAngle;
      mob.vx = Math.cos(mob.wanderAngle) * wspd;
      mob.vy = Math.sin(mob.wanderAngle) * wspd;
    }

    const previousX = mob.x;
    const previousY = mob.y;
    mob.x += mob.vx * tickScale;
    mob.y += mob.vy * tickScale;

    const separationRange = (mob.radius || MOB_RADIUS) + MOB_RADIUS + 36;
    for (const other of nearbyMobs(mob.x, mob.y, separationRange)) {
      if (other === mob) continue;
      const dx = mob.x - other.x;
      const dy = mob.y - other.y;
      const distance = Math.hypot(dx, dy);
      const minDistance = (mob.radius || MOB_RADIUS) + (other.radius || MOB_RADIUS) + 36;
      if (distance >= minDistance) continue;

      const angle = distance > 0
        ? Math.atan2(dy, dx)
        : ((parseInt(String(mob.id).replace(/\D/g, ''), 10) || 0) % 360) * Math.PI / 180;
      const normalX = Math.cos(angle);
      const normalY = Math.sin(angle);
      const push = Math.min(12, (minDistance - distance) * 0.55);
      mob.x += normalX * push;
      mob.y += normalY * push;

      const inwardSpeed = mob.vx * normalX + mob.vy * normalY;
      if (inwardSpeed < 0) {
        mob.vx -= inwardSpeed * normalX;
        mob.vy -= inwardSpeed * normalY;
      }
    }

    // Beginner Safe Village & Farmland Buffer push-out:
    // Hostile beasts cannot enter the peaceful perimeter (r < 1420), losing aggro and returning.
    // Peaceful wildlife (hares/deer) stay outside the inner village gates (r < 1180).
    const distToCenter = Math.hypot(mob.x, mob.y);
    const bufferLimit = mob.isPeaceful ? 1180 : 1420;
    if (distToCenter < bufferLimit) {
      const pushAng = distToCenter > 1 ? Math.atan2(mob.y, mob.x) : Math.random() * Math.PI * 2;
      mob.x = Math.cos(pushAng) * bufferLimit;
      mob.y = Math.sin(pushAng) * bufferLimit;
      mob.vx = Math.cos(pushAng) * 6;
      mob.vy = Math.sin(pushAng) * 6;
      mob.wanderAngle = pushAng;
      mob.targetId = null;
      mob.chaseStartedAt = 0;
      mob.chaseUntil = 0;
    }

    // Solid collision push-out against resources (trees, rocks, gold)
    const nearbyObstacles = nearbyServerObstacles(mob.x, mob.y, mob.radius + MAX_RESOURCE_COLLISION_RADIUS);
    for (let oi = 0; oi < nearbyObstacles.length; oi++) {
      const obs = nearbyObstacles[oi];
      const ox = mob.x - obs.x, oy = mob.y - obs.y;
      const oDist2 = ox * ox + oy * oy;
      const minODist = mob.radius + obs.radius;
      if (oDist2 < minODist * minODist && oDist2 > 0) {
        const oDist = Math.sqrt(oDist2) || 1;
        const push = minODist - oDist;
        mob.x += (ox / oDist) * push;
        mob.y += (oy / oDist) * push;
        const dot = mob.vx * (ox / oDist) + mob.vy * (oy / oDist);
        if (dot < 0) {
          mob.vx -= dot * (ox / oDist);
          mob.vy -= dot * (oy / oDist);
        }
      }
    }

    // Sweep the whole movement segment so fast mobs cannot tunnel through thin buildings or traps.
    const movementDistance = Math.hypot(mob.x - previousX, mob.y - previousY);
    const sweepCenterX = (previousX + mob.x) * 0.5;
    const sweepCenterY = (previousY + mob.y) * 0.5;
    for (const b of nearbyBuildings(sweepCenterX, sweepCenterY, mob.radius + 120 + movementDistance * 0.5)) {
      const collision = resolveMobBuildingCollision(mob, b, { x: previousX, y: previousY }, now);
      if (collision.trapped) {
        mob.nextAttackAt = now + 3500;
        io.emit('mob_trapped', {
          mobId: mob.id,
          buildingId: b.id,
          x: mob.trappedX,
          y: mob.trappedY,
          frozenAngle: mob.angle,
          ts: now
        });
        break;
      }
      if (collision.collided && b.type === 3 && (b.hp ?? 100) > 0) {
        applyMobSpikeDamage(mob, b, now);
        break;
      }
      if (collision.collided && [4, 8, 9].includes(Number(b.type))) {
        applyMobBuildingDamage(mob, b, now);
      }
    }

    mob.x = Math.max(-PLAY_RADIUS, Math.min(PLAY_RADIUS, mob.x));
    mob.y = Math.max(-PLAY_RADIUS, Math.min(PLAY_RADIUS, mob.y));

    changed.push(compactMobTick(mob));
  }
  syncMobVisibility(changed);
}, 50);

// ═════════════════════════════════════════════════════════════════════════
// DYNAMIC INTELLIGENT BOT AI SYSTEM (CLANS, BASE BUILDING, SQUAD DEFENSE)
// ═════════════════════════════════════════════════════════════════════════
const BOT_NAMES = [
  'ShadowBlade', 'Viper_99', 'FrostBite', 'StormRider', 'Ghost_TR', 'WolfFang',
  'Apex_Predator', 'IronClad', 'Ninja_X', 'SilentDeath', 'DragonBorn', 'Phoenix',
  'Blaze_Runner', 'DarkKnight', 'CyberSamurai', 'AlphaWolf', 'Titan_01', 'Valkyrie',
  'Eren_TR', 'GamerPro', 'SniperWolf', 'BloodSeeker', 'Raven', 'MysticBlade',
  'Kral_Kurt', 'Thor_Slayer', 'Zeus_99', 'NoobMaster', 'Warrior_TR', 'Starve_King'
];

function purgeBotLeaderboardRecords() {
  const botKeys = new Set(BOT_NAMES.map(name => usernameKey(name)));
  let changed = false;
  for (const key of Object.keys(accountData.leaderboard || {})) {
    if (botKeys.has(key)) {
      delete accountData.leaderboard[key];
      changed = true;
    }
  }
  if (Array.isArray(accountData.recentDeaths)) {
    const filtered = accountData.recentDeaths.filter(entry => !botKeys.has(usernameKey(entry?.name)));
    if (filtered.length !== accountData.recentDeaths.length) {
      accountData.recentDeaths = filtered;
      changed = true;
    }
  }
  if (changed) saveAccountData(true);
}

purgeBotLeaderboardRecords();

const BOT_SKINS = ['default', 'skin_desert', 'skin_frostwolf', 'skin_storm', 'skin_sapphire', 'skin_ruby', 'skin_emerald'];

const BOT_CLANS = [
  { id: 'clan_apex', name: 'Apex Predators', tag: 'APEX' },
  { id: 'clan_wolf', name: 'Shadow Wolves', tag: 'WOLF' },
  { id: 'clan_titan', name: 'Iron Titans', tag: 'TITAN' },
  { id: 'clan_elite', name: 'Elite Squad', tag: 'ELITE' }
];

function ensureBotClans() {
  for (const c of BOT_CLANS) {
    if (!clans.has(c.id)) {
      clans.set(c.id, { id: c.id, name: c.name, tag: c.tag, ownerId: `owner_${c.id}`, ownerName: `${c.tag}_Leader`, members: [] });
    }
  }
}

let botIdCounter = 1;
const botList = new Map();

function getBotSpawnPosition(radius = 35) {
  const padding = Math.max(0, Number(radius) || 35) + 64;
  for (let attempt = 0; attempt < 100; attempt++) {
    const x = Math.round((Math.random() * 2 - 1) * 3000);
    const y = Math.round((Math.random() * 2 - 1) * 3000);
    if (!isInsideVillageBuffer(x, y, padding)) return { x, y };
  }
  return {
    x: VILLAGE_BUFFER_HALF + padding + 1,
    y: Math.round((Math.random() * 2 - 1) * 3000)
  };
}

function keepBotOutsideVillage(bot) {
  const padding = (Number(bot.radius) || 35) + 64;
  const minCoord = VILLAGE_BUFFER_HALF + padding;
  if (!isInsideVillageBuffer(bot.x, bot.y, padding)) return false;

  const xDistance = minCoord - Math.abs(bot.x);
  const yDistance = minCoord - Math.abs(bot.y);
  if (xDistance <= yDistance) {
    const side = bot.x === 0 ? (bot.id.charCodeAt(bot.id.length - 1) % 2 ? 1 : -1) : Math.sign(bot.x);
    bot.x = side * minCoord;
    bot.vx = side * Math.max(0, Math.abs(bot.vx || 0));
  } else {
    const side = bot.y === 0 ? (bot.id.charCodeAt(bot.id.length - 1) % 2 ? 1 : -1) : Math.sign(bot.y);
    bot.y = side * minCoord;
    bot.vy = side * Math.max(0, Math.abs(bot.vy || 0));
  }
  bot.target = null;
  bot.targetChangeAt = Date.now() + 800;
  if (bot.trappedX !== null && isInsideVillageBuffer(bot.trappedX, bot.trappedY, padding)) {
    bot.trappedBy = null;
    bot.trappedUntil = 0;
    bot.trappedX = null;
    bot.trappedY = null;
  }
  return true;
}

function createBot(name) {
  ensureBotClans();
  const botId = `bot_${botIdCounter++}`;
  const angle = Math.random() * Math.PI * 2;
  const botName = name || BOT_NAMES[Math.floor(Math.random() * BOT_NAMES.length)];
  const botSkin = BOT_SKINS[Math.floor(Math.random() * BOT_SKINS.length)];
  const wep = Math.random() < 0.65 ? 2 : 1;
  const tier = Math.floor(Math.random() * 3) + 1;

  const joinClan = Math.random() < 0.85;
  const chosenClan = joinClan ? BOT_CLANS[Math.floor(Math.random() * BOT_CLANS.length)] : null;
  const clanId = chosenClan ? chosenClan.id : '';
  const clanTag = chosenClan ? chosenClan.tag : '';
  const team = clanTag;

  if (chosenClan) {
    const clanObj = clans.get(chosenClan.id);
    if (clanObj && !clanObj.members.some(m => m.id === botId)) {
      clanObj.members.push({ id: botId, name: botName });
    }
  }

  const { x, y } = getBotSpawnPosition();

  const bot = {
    id: botId,
    name: botName,
    isBot: true,
    x, y,
    vx: 0, vy: 0,
    angle,
    hp: 250, maxHp: 250,
    wood: Math.floor(Math.random() * 80) + 50,
    stone: Math.floor(Math.random() * 60) + 30,
    gold: Math.floor(Math.random() * 120) + 20,
    apples: Math.floor(Math.random() * 15) + 6,
    score: Math.floor(Math.random() * 1500) + 200,
    sc: 0,
    xp: Math.floor(Math.random() * 800) + 100,
    weapon: wep,
    axeTier: tier,
    swordTier: tier,
    skin: botSkin,
    color: '#8B5E3A',
    team,
    clanId,
    clanTag,
    kills: 0,
    stateSeq: 0,
    stateAt: Date.now(),
    lastSwingAt: 0,
    lastAppleAt: 0,
    lastBuildAt: 0,
    lastBaseActionAt: 0,
    baseX: null,
    baseY: null,
    baseStep: 0,
    baseBuildingIds: [],
    target: null,
    targetChangeAt: 0,
    speed: 280,
    radius: 35,
    trappedBy: null,
    trappedUntil: 0,
    trappedX: null,
    trappedY: null,
    isAttacking: false,
    attackUntil: 0
  };
  bot.sc = bot.score;

  updatePlayerRoom(bot);
  players.set(botId, bot);
  botList.set(botId, bot);

  io.emit('player_join', { id: botId, state: compactFullState(bot), aoi: true });
  return bot;
}

function removeBot(botId) {
  const bot = botList.get(botId);
  if (!bot) return;
  if (bot.clanId && clans.has(bot.clanId)) {
    const clanObj = clans.get(bot.clanId);
    if (clanObj) clanObj.members = clanObj.members.filter(m => m.id !== botId);
  }
  botList.delete(botId);
  players.delete(botId);
  if (bot.roomId && rooms.get(bot.roomId)?.has(botId)) {
    rooms.get(bot.roomId).delete(botId);
  }
  deletePlayerBuildings(botId);
  io.emit('player_despawn', { id: botId });
}

function scheduleBotRespawn(bot) {
  setTimeout(() => {
    if (!botList.has(bot.id)) return;
    const spawn = getBotSpawnPosition(bot.radius);
    bot.x = spawn.x;
    bot.y = spawn.y;
    bot.vx = 0;
    bot.vy = 0;
    bot.hp = 250;
    bot.maxHp = 250;
    bot._dead = false;
    bot.trappedBy = null;
    bot.trappedUntil = 0;
    bot.trappedX = null;
    bot.trappedY = null;
    bot.target = null;
    bot.targetChangeAt = 0;
    bot.baseX = null;
    bot.baseY = null;
    bot.baseStep = 0;
    bot.baseBuildingIds = [];
    bot.defSpikes = [];
    bot.lastSwingAt = 0;
    bot.lastAppleAt = 0;
    bot.lastBuildAt = 0;
    bot.lastBaseActionAt = 0;
    bot.isAttacking = false;
    bot.teleportSeq = (bot.teleportSeq || 0) + 1;
    bot.apples = 10;
    bot.wood = 50;
    bot.stone = 30;
    bot.stateSeq = (bot.stateSeq || 0) + 1;
    bot.stateAt = Date.now();
    updatePlayerRoom(bot);
    io.emit('player_join', { id: bot.id, state: compactFullState(bot), aoi: true });
  }, 4000 + Math.random() * 3000);
}

// Remove bots left by older population state; bot spawning is disabled.
setInterval(() => {
  for (const botId of botList.keys()) removeBot(botId);

  const now = Date.now();
  const dt = 0.1;

  for (const bot of botList.values()) {
    if ((bot.hp ?? 0) <= 0 || bot._dead) continue;
    keepBotOutsideVillage(bot);

    // 0. Trap Check: If trapped by an enemy trap, freeze with max 3.5s hold (no infinite freeze)
    if (bot.trappedBy) {
      const b = buildings.get(bot.trappedBy);
      if (b && (b.hp ?? 100) > 0 && now < (bot.trappedUntil || 0)) {
        bot.vx = 0;
        bot.vy = 0;
        bot.x = bot.trappedX ?? bot.x;
        bot.y = bot.trappedY ?? bot.y;
        for (const spike of nearbyBuildings(bot.x, bot.y, (bot.radius || 35) + 90)) {
          const dx = bot.x - spike.x;
          const dy = bot.y - spike.y;
          const hitRadius = (bot.radius || 35) + (spike.radius || 34);
          if (Number(spike.type) === 3 && dx * dx + dy * dy <= hitRadius * hitRadius) {
            applyBotSpikeDamage(bot, spike, now);
          }
        }
        bot.stateSeq = (bot.stateSeq || 0) + 1;
        bot.stateAt = now;
        updatePlayerRoom(bot);
        continue;
      } else {
        bot.trappedBy = null;
        bot.trappedUntil = 0;
        bot.trappedX = null;
        bot.trappedY = null;
      }
    }

    // 1. Survival Check: Heal with apples if low on HP
    if (bot.hp < 210 && bot.apples > 0 && now - (bot.lastAppleAt || 0) >= 700) {
      bot.apples--;
      bot.hp = Math.min(bot.maxHp, bot.hp + 32);
      bot.hpSeq = (bot.hpSeq || 0) + 1;
      bot.hpAt = now;
      bot.lastAppleAt = now;

      // Defensive tactical spike drop when wounded in close combat (spawn with safe clearance)
      if (bot.target && bot.target.type === 'player' && bot.wood >= 20 && now - (bot.lastBuildAt || 0) >= BUILD_ACTION_COOLDOWN) {
        bot.lastBuildAt = now;
        bot.wood -= 20;
        bot.weapon = 3;
        bot.isAttacking = true;
        bot.attackUntil = now + 250;
        bot.lastSwingAt = now;
        const bDist = (bot.radius || 35) + 34 + 18; // 87 units clearance, never inside bot body
        const bX = Math.round(bot.x + Math.cos(bot.angle) * bDist);
        const bY = Math.round(bot.y + Math.sin(bot.angle) * bDist);
        const bId = `${bot.id}-def-${Date.now().toString(36)}`;
        const defSpike = {
          id: bId, type: 3, x: bX, y: bY, angle: bot.angle,
          radius: 34, hp: 180, maxHp: 180, tier: 0,
          ownerId: bot.id, ownerClanId: bot.clanId || ''
        };
        buildings.set(bId, defSpike);
        if (!bot.defSpikes) bot.defSpikes = [];
        if (bot.defSpikes.length >= 3) {
          const oldSpikeId = bot.defSpikes.shift();
          if (buildings.has(oldSpikeId)) {
            buildings.delete(oldSpikeId);
            io.emit('build_destroy', { id: oldSpikeId });
          }
        }
        bot.defSpikes.push(bId);
        scheduleBuildingGridRebuild();
        broadcastBotEvent(bot, 'player_attack', { id: bot.id, weapon: 3, angle: bot.angle, at: now, durationMs: 240 });
        io.emit('build', { id: bId, building: { ...defSpike } });
      }
    }

    // 2. Target Selection / Aggro update
    if (bot.target && bot.target.type === 'player') {
      const curDist = Math.hypot(bot.target.x - bot.x, bot.target.y - bot.y);
      const targetInVillage = bot.target.entity &&
        isInsideVillageBuffer(bot.target.entity.x, bot.target.entity.y, (bot.radius || 35) + 64);
      if (curDist > 650 || targetInVillage || !bot.target.entity || (bot.target.entity.hp ?? 0) <= 0 || bot.target.entity._dead) {
        bot.target = null;
        bot.targetChangeAt = now + 800;
      }
    }

    if (!bot.target || now > (bot.targetChangeAt || 0)) {
      let bestTarget = null;
      let bestDist = 550; // Responsive engagement radius

      // 2a. Revenge: Prioritize player who recently attacked this bot
      if (bot._lastAttackedBy) {
        const attacker = players.get(bot._lastAttackedBy);
        if (attacker && (attacker.hp ?? 0) > 0 && !attacker._dead &&
            !isInsideVillageBuffer(attacker.x, attacker.y, (bot.radius || 35) + 64)) {
          const dAttacker = Math.hypot(attacker.x - bot.x, attacker.y - bot.y);
          if (dAttacker < 750) {
            bestTarget = { id: attacker.id, x: attacker.x, y: attacker.y, entity: attacker, type: 'player' };
            bestDist = dAttacker;
          }
        }
      }

      // 2b. Squad Defense: Protect nearby clanmate being attacked
      if (!bestTarget && bot.clanId) {
        for (const [otherId, ally] of players) {
          if (otherId === bot.id || !ally || (ally.hp ?? 0) <= 0 || ally._dead) continue;
          if (ally.clanId === bot.clanId || ally.team === bot.team) {
            const dAlly = Math.hypot(ally.x - bot.x, ally.y - bot.y);
            if (dAlly < 500 && ally._lastAttackedBy) {
              const attacker = players.get(ally._lastAttackedBy);
              if (attacker && (attacker.hp ?? 0) > 0 && !attacker._dead &&
                  !isInsideVillageBuffer(attacker.x, attacker.y, (bot.radius || 35) + 64) &&
                  attacker.clanId !== bot.clanId) {
                bestTarget = { id: attacker.id, x: attacker.x, y: attacker.y, entity: attacker, type: 'player' };
                bestDist = Math.hypot(attacker.x - bot.x, attacker.y - bot.y);
                break;
              }
            }
          }
        }
      }

      // 2c. Nearest Hostile Player or Rival Bot within vision range
      if (!bestTarget) {
        for (const [otherId, other] of players) {
          if (otherId === bot.id || !other || (other.hp ?? 0) <= 0 || other._dead) continue;
          if (isInsideVillageBuffer(other.x, other.y, (bot.radius || 35) + 64)) continue;
          if ((other.clanId && other.clanId === bot.clanId) || (other.team && other.team === bot.team)) continue;
          const d = Math.hypot(other.x - bot.x, other.y - bot.y);
          if (d < bestDist) {
            bestDist = d;
            bestTarget = { id: otherId, x: other.x, y: other.y, entity: other, type: 'player' };
          }
        }
      }

      // 2d. Resource gathering when low on resources or idle
      if (!bestTarget && (bot.wood < 100 || bot.stone < 50 || Math.random() < 0.35)) {
        for (let i = 0; i < serverResources.length; i++) {
          const res = serverResources[i];
          if (!res || res.destroyed) continue;
          const d = Math.hypot(res.x - bot.x, res.y - bot.y);
          if (d < 500 && d < bestDist) {
            bestDist = d;
            bestTarget = { id: res.idx, x: res.x, y: res.y, type: 'resource' };
          }
        }
      }

      // 2e. Active Roam (explore world, never stand still)
      if (!bestTarget) {
        const roamDist = 300 + Math.random() * 400;
        const roamAngle = (bot.wanderAngle || bot.angle || 0) + (Math.random() - 0.5) * 1.6;
        bot.wanderAngle = roamAngle;
        bestTarget = {
          x: Math.max(-3400, Math.min(3400, bot.x + Math.cos(roamAngle) * roamDist)),
          y: Math.max(-3400, Math.min(3400, bot.y + Math.sin(roamAngle) * roamDist)),
          type: 'roam'
        };
      }

      bot.target = bestTarget;
      bot.targetChangeAt = now + 1800 + Math.random() * 1200;
    }

    if (bot.target && bot.target.entity) {
      if (bot.target.entity.hp <= 0 || bot.target.entity._dead) {
        bot.target = null;
        continue;
      }
      bot.target.x = bot.target.entity.x;
      bot.target.y = bot.target.entity.y;
    }

    // 3. Base Building & Fortification (Windmills + Spikes)
    if (bot.wood >= 40 && bot.stone >= 20 && (!bot.target || bot.target.type === 'roam') && now - (bot.lastBaseActionAt || 0) > 4000) {
      if (!bot.baseX) {
        bot.baseX = Math.round(bot.x);
        bot.baseY = Math.round(bot.y);
        bot.baseStep = 0;
      }

      const bRad = 85;
      let placeType = null;
      let pX = bot.baseX;
      let pY = bot.baseY;

      if (bot.baseStep === 0 && bot.wood >= 40 && bot.stone >= 20) {
        placeType = 4; // Center Windmill
      } else if (bot.baseStep >= 1 && bot.baseStep <= 4 && bot.wood >= 20 && bot.stone >= 5) {
        placeType = 3; // Protective Spikes
        const angles = [0, Math.PI * 0.5, Math.PI, Math.PI * 1.5];
        const a = angles[bot.baseStep - 1];
        pX = Math.round(bot.baseX + Math.cos(a) * bRad);
        pY = Math.round(bot.baseY + Math.sin(a) * bRad);
      } else if (bot.baseStep === 5 && bot.wood >= 25) {
        placeType = 10; // Resource Machine
        pX = Math.round(bot.baseX + 48);
        pY = Math.round(bot.baseY + 48);
      }

      if (placeType !== null) {
        const [wCost, sCost] = BUILD_COSTS[placeType] || [20, 5, 0];
        const mHp = BUILD_MAX_HP[placeType] || 120;
        const bRad = BUILD_RADII[placeType] || (placeType === 4 ? 44 : (placeType === 3 ? 34 : 30));
        if (bot.wood >= wCost && bot.stone >= sCost) {
          bot.wood -= wCost;
          bot.stone -= sCost;
          bot.lastBaseActionAt = now;
          bot.lastBuildAt = now;
          bot.weapon = placeType;
          bot.isAttacking = true;
          bot.attackUntil = now + 300;
          bot.lastSwingAt = now;
          bot.baseStep++;
          if (bot.baseStep > 5) bot.baseStep = 6;

          // Cap base buildings per bot to prevent clutter
          if (!bot.baseBuildingIds) bot.baseBuildingIds = [];
          if (bot.baseBuildingIds.length >= 4) {
            const oldId = bot.baseBuildingIds.shift();
            if (buildings.has(oldId)) {
              buildings.delete(oldId);
              broadcastBotEvent(bot, 'build_destroy', { id: oldId });
            }
          }

          const bId = `${bot.id}-base-${bot.baseStep}-${Date.now().toString(36)}`;
          const newBld = {
            id: bId,
            type: placeType,
            x: pX,
            y: pY,
            angle: 0,
            radius: bRad,
            hp: mHp,
            maxHp: mHp,
            tier: 0,
            ownerId: bot.id,
            ownerClanId: bot.clanId || ''
          };
          buildings.set(bId, newBld);
          bot.baseBuildingIds.push(bId);
          scheduleBuildingGridRebuild();
          broadcastBotEvent(bot, 'player_attack', { id: bot.id, weapon: placeType, angle: bot.angle, at: now, durationMs: 240 });
          io.emit('build', { id: bId, building: { ...newBld } });
        }
      }
    }

    // 4. Movement, Weapon Switching & Tactical Combat
    if (bot.target) {
      const dx = bot.target.x - bot.x;
      const dy = bot.target.y - bot.y;
      const dist = Math.hypot(dx, dy);

      const targetAngle = Math.atan2(dy, dx);
      let angleDiff = targetAngle - bot.angle;
      while (angleDiff < -Math.PI) angleDiff += Math.PI * 2;
      while (angleDiff > Math.PI) angleDiff -= Math.PI * 2;
      const turnRate = (bot.target.type === 'player') ? 0.65 : 0.40;
      bot.angle += angleDiff * turnRate;

      // Smart Weapon Selection: Axe (1) for resources, Sword (2) for PvP (wait for build slam anim to finish)
      if (now > (bot.attackUntil || 0)) {
        if (bot.target.type === 'resource') {
          bot.weapon = 1;
        } else if (bot.target.type === 'player') {
          bot.weapon = 2;
        }
      }

      // Exact human player walking speed (280 units/sec)
      const baseSpeed = 280;
      let moveAngle = bot.angle;
      let moveSpeed = baseSpeed;

      if (bot.target.type === 'player') {
        if (dist > 650) {
          bot.target = null;
          bot.vx = 0;
          bot.vy = 0;
        } else if (dist > 95) {
          moveSpeed = baseSpeed;
          moveAngle = bot.angle;
          bot.vx = Math.cos(moveAngle) * moveSpeed;
          bot.vy = Math.sin(moveAngle) * moveSpeed;
        } else if (dist <= 95 && dist >= 55) {
          // Tactical Circle-Strafing around opponent
          const strafeSign = ((bot.id.charCodeAt(bot.id.length - 1) + Math.floor(now / 1200)) % 2 === 0) ? 1 : -1;
          moveAngle = targetAngle + (Math.PI * 0.42 * strafeSign);
          moveSpeed = baseSpeed * 0.9;
          bot.vx = Math.cos(moveAngle) * moveSpeed;
          bot.vy = Math.sin(moveAngle) * moveSpeed;
        } else {
          // Backpedal slightly for weapon spacing
          moveAngle = targetAngle + Math.PI;
          moveSpeed = baseSpeed * 0.65;
          bot.vx = Math.cos(moveAngle) * moveSpeed;
          bot.vy = Math.sin(moveAngle) * moveSpeed;
        }
      } else if (dist > 75) {
        bot.vx = Math.cos(bot.angle) * moveSpeed;
        bot.vy = Math.sin(bot.angle) * moveSpeed;
      } else {
        bot.vx = 0;
        bot.vy = 0;
        // If roam destination reached, immediately seek new target on next tick
        if (bot.target && bot.target.type === 'roam') {
          bot.target = null;
          bot.targetChangeAt = 0;
        }
      }

      // Step position
      bot.x += bot.vx * dt;
      bot.y += bot.vy * dt;

      // SOLID COLLISION RESOLUTION (Bots CANNOT pass through buildings, spikes, traps, walls, trees, rocks)
      const botRad = Number(bot.radius) || 35;
      for (let pass = 0; pass < 2; pass++) {
        // A. Solid Buildings & Traps
        for (const b of nearbyBuildings(bot.x, bot.y, botRad + 120)) {
          if (b.type === 5) continue; // Boost pad allows walkover
          if ((b.hp ?? 100) <= 0) continue;

          // Enemy Trap capture check
          if (b.type === 6 && b.ownerId !== bot.id && (!bot.clanId || b.ownerClanId !== bot.clanId)) {
            const tdx = bot.x - b.x, tdy = bot.y - b.y;
            const trapTriggerR = trapCaptureRadius(b, bot.radius || 35);
            if (tdx * tdx + tdy * tdy <= trapTriggerR * trapTriggerR) {
              bot.trappedBy = b.id;
              bot.trappedUntil = now + 3500; // max 3.5 seconds trap hold
              bot.trappedX = bot.x;
              bot.trappedY = bot.y;
              bot.vx = 0; bot.vy = 0;
              broadcastPlayerEventNear(bot, 'trap_triggered', { buildingId: b.id, victimId: bot.id, bId: b.id, x: bot.x, y: bot.y });
              continue;
            }
          }

          // Traps are passable until their capture radius is entered.
          if (b.type === 6) continue;

          // Solid repulsion against walls/spikes/windmills
          const bRad = Number(b.radius) || (b.type === 8 ? 24 : (b.type === 6 ? 78 : (b.type === 10 ? 30 : 36)));
          const col = NetworkPhysics.resolveCircleCircle(bot, botRad, 1.0, b, bRad, 0.0);
          if (col && col.collided && pass === 0) {
            NetworkPhysics.projectVelocitySlide(bot, col.nx, col.ny, 0.05);
            if (b.type === 3) applyBotSpikeDamage(bot, b, now);
          }
        }

        // B. Natural Obstacles (Trees, Rocks, Gold Nodes)
        const nearObs = nearbyServerObstacles(bot.x, bot.y, botRad + MAX_RESOURCE_COLLISION_RADIUS);
        for (let oi = 0; oi < nearObs.length; oi++) {
          const obs = nearObs[oi];
          const ox = bot.x - obs.x, oy = bot.y - obs.y;
          const oDist2 = ox * ox + oy * oy;
          const minODist = botRad + obs.radius;
          if (oDist2 < minODist * minODist && oDist2 > 0) {
            const oDist = Math.sqrt(oDist2) || 1;
            const push = minODist - oDist;
            bot.x += (ox / oDist) * push;
            bot.y += (oy / oDist) * push;
            const dot = bot.vx * (ox / oDist) + bot.vy * (oy / oDist);
            if (dot < 0) {
              bot.vx -= dot * (ox / oDist);
              bot.vy -= dot * (oy / oDist);
            }
          }
        }

        // C. Dynamic Entities (Bots vs Other Bots & Players - Zero Stacking & Momentum Slide)
        for (const otherPlayer of nearbyPlayers(bot.x, bot.y, botRad + 45)) {
          if (otherPlayer.id === bot.id || (otherPlayer.hp ?? 0) <= 0) continue;
          const opRad = Number(otherPlayer.radius) || 35;
          const col = NetworkPhysics.resolveCircleCircle(bot, botRad, 1.0, otherPlayer, opRad, otherPlayer.trappedBy ? 0.0 : 1.0);
          if (col && col.collided && pass === 0) {
            NetworkPhysics.projectVelocitySlide(bot, col.nx, col.ny, 0.05);
          }
        }
      }

      bot.x = Math.max(-3500, Math.min(3500, bot.x));
      bot.y = Math.max(-3500, Math.min(3500, bot.y));
      keepBotOutsideVillage(bot);

      // 5. Combat / Harvesting - NO INVISIBLE DAMAGE, VISIBLE BODY SWING ARC
      if (dist <= 125 && !bot.trappedBy) {
        const swingCooldown = bot.weapon === 2 ? 380 : 340;
        const attackDuration = bot.weapon === 2 ? 280 : 300;
        if (now - (bot.lastSwingAt || 0) >= swingCooldown) {
          bot.lastSwingAt = now;
          bot.isAttacking = true;
          bot.attackUntil = now + attackDuration;
          bot.attackTimer = 0;
          bot.attackDuration = attackDuration;

          // Broadcast attack event only to nearby players within AOI radius (eliminates global broadcast flood)
          const nearPlayers = nearbyPlayers(bot.x, bot.y, PLAYER_AOI_RADIUS);
          if (nearPlayers.length > 0) {
            const attackPacket = {
              id: bot.id,
              weapon: bot.weapon,
              angle: bot.angle,
              at: now,
              swingId: now,
              serverTime: now,
              durationMs: attackDuration
            };
            for (let npi = 0; npi < nearPlayers.length; npi++) {
              const s = io.sockets.sockets.get(nearPlayers[npi].id);
              if (s && s.connected) {
                s.emit('player_attack', attackPacket);
                s.emit('playerAttack', bot.id);
              }
            }
          }

          if (bot.target && bot.target.type === 'player' && bot.target.entity) {
            const targetPlayer = bot.target.entity;
            const toTargetAngle = Math.atan2(targetPlayer.y - bot.y, targetPlayer.x - bot.x);
            let facingDiff = Math.abs(toTargetAngle - bot.angle);
            while (facingDiff > Math.PI) facingDiff = Math.abs(facingDiff - Math.PI * 2);

            // Forward arc check: Target must be in front of the bot (+/- 75 degrees)
            if (facingDiff < Math.PI * 0.42 && (!targetPlayer.clanId || targetPlayer.clanId !== bot.clanId)) {
              const multiplier = [1, 1.4, 2.0, 3.0, 4.5][bot.swordTier || 1] || 1.4;
              const dmg = limitHitDamage(targetPlayer, Math.round((bot.weapon === 2 ? 26 : 18) * multiplier));

              targetPlayer._lastAttackedBy = bot.id;
              applyPlayerDamage(targetPlayer, dmg);
              publishPlayerDamage(targetPlayer, dmg, bot.name);

              // If target is another bot, make it retaliate!
              if (targetPlayer.isBot) {
                alertBotAttacked(targetPlayer, bot);
              }

              if (targetPlayer.hp <= 0) {
                onPlayerDeath(targetPlayer.id);
                bot.kills = (bot.kills || 0) + 1;
                bot.score = (bot.score || 0) + 200;
                bot.sc = bot.score;
                io.emit('pvp_kill_feed', { killer: bot.name, victim: targetPlayer.name || 'Oyuncu', streak: bot.kills });
                if (!targetPlayer.isBot) {
                  io.to(targetPlayer.id).emit('pvp_killed', { byName: bot.name });
                }
                bot.target = null;
              }
            }
          } else if (bot.target && bot.target.type === 'resource') {
            bot.wood = (bot.wood || 0) + 12;
            bot.stone = (bot.stone || 0) + 6;
            bot.score = (bot.score || 0) + 15;
            bot.sc = bot.score;
            if (Math.random() < 0.28) bot.target = null;
          }
        }
      }
    }

    bot.stateSeq = (bot.stateSeq || 0) + 1;
    bot.stateAt = now;
    updatePlayerRoom(bot);
  }
}, 200);

// 30Hz Server Game Tick: send player states only to nearby clients.
setInterval(() => {
  if (players.size === 0) return;
  rebuildPlayerGrid();
  const now = Date.now();
  const livingPlayers = [...players.values()].filter((p) => p && (p.hp ?? 0) > 0);
  for (const p of livingPlayers) {
    if (p.isAttacking && now > (p.attackUntil || 0)) p.isAttacking = false;
    if (p.isBot) p.stateSeq = (p.stateSeq || 0) + 1;
    updatePlayerRoom(p);
  }
  for (const [recipientId, socket] of io.sockets.sockets) {
    if (!socket.connected) continue;
    const recipient = players.get(recipientId);
    if (!recipient) continue;
    const previousVisible = recipient.visiblePlayerIds || new Set();
    const nextVisible = new Set();
    const batch = {};
    const targetRoomIds = nearbyRoomIds(Number(recipient.x) || 0, Number(recipient.y) || 0, PLAYER_AOI_RADIUS);
    if (socket.data.isSpectator) {
      const spectatorBatch = {};
      for (const p of livingPlayers) spectatorBatch[p.id] = compactStateCompressed(p);
      const previousSpectator = recipient._lastSpectatorBatch || {};
      const dirtySpectator = Object.keys(spectatorBatch).some(id => previousSpectator[id] !== compressedStateSignature(spectatorBatch[id]));
      if (dirtySpectator || Object.keys(previousSpectator).length !== Object.keys(spectatorBatch).length) {
        socket.volatile.emit('players', spectatorBatch);
      }
      recipient._lastSpectatorBatch = Object.fromEntries(
        Object.entries(spectatorBatch).map(([id, packet]) => [id, compressedStateSignature(packet)])
      );
      continue;
    }
    const nearbyPlayersSet = new Set();
    for (const roomId of targetRoomIds) {
      for (const player of getRoomMembers(roomId)) {
        if (!player || player.id === recipientId) continue;
        nearbyPlayersSet.add(player.id);
      }
    }
    const previousAoi = recipient._lastAoiBatch || {};
    for (const id of nearbyPlayersSet) {
      const p = players.get(id);
      if (!p || (p.hp ?? 0) <= 0) continue;
      nextVisible.add(p.id);
      const packet = compactStateCompressed(p);
      batch[p.id] = packet;
      if (!previousVisible.has(p.id)) {
        socket.emit('player_join', { id: p.id, state: compactFullState(p), aoi: true });
      }
    }
    for (const id of previousVisible) {
      if (!nextVisible.has(id)) socket.emit('player_despawn', { id });
    }
    recipient.visiblePlayerIds = nextVisible;
    const dirtyPlayers = Object.keys(batch).filter(id => !previousAoi[id] || previousAoi[id] !== compressedStateSignature(batch[id]));
    if (dirtyPlayers.length > 0) {
      const delta = {};
      for (const id of dirtyPlayers) delta[id] = batch[id];
      socket.volatile.emit('players', delta);
    }
    recipient._lastAoiBatch = Object.fromEntries(
      Object.entries(batch).map(([id, packet]) => [id, compressedStateSignature(packet)])
    );
  }
}, 33);

// Broadcast short-lived Thor strikes so every connected client sees the same ground effect.
setInterval(() => {
  const thorPlayers = [...players.values()].filter(p => p && p.skin === 'thor' && (p.hp ?? 0) > 0);
  if (!thorPlayers.length) return;
  const strikes = [];
  const now = Date.now();
  for (const thor of thorPlayers) {
    for (let i = 0; i < 8; i++) {
      const angle = (now * 0.001 + i * 2.399 + thor.id.length) % (Math.PI * 2);
      const distance = 120 + ((now / 90 + i * 137) % 760);
      strikes.push({ sx: thor.x, sy: thor.y, x: thor.x + Math.cos(angle) * distance, y: thor.y + Math.sin(angle) * distance, at: now, seed: i });
    }
  }
  io.emit('thor_lightning', { strikes: strikes.slice(0, 32), at: now });
}, 700);

// Periodic server loop (1Hz): Windmill generation, stats confirmation and reconciliation
setInterval(() => {
  if (players.size === 0) return;

  // 1. Authoritative Windmill (type === 4) Tick: generate +15 gold and tier score every second
  if (buildings.size > 0) {
    const WINDMILL_SCORES = [10, 22, 50, 110, 220, 500];
    const WINDMILL_GOLD = [15, 18, 22, 28, 36, 48];
    for (const b of buildings.values()) {
      if (Number(b.type) === 4 && (b.hp === undefined || b.hp > 0)) {
        const owner = players.get(b.ownerId);
        if (owner && (owner.hp ?? 0) > 0) {
          const wTier = Math.min(5, Math.max(0, Number(b.tier) || 0));
          const wmMult = Number(owner.windmillMultiplier) || 1.0;
          const wGold = Math.round((WINDMILL_GOLD[wTier] || 15) * wmMult);
          const wScore = Math.round((WINDMILL_SCORES[wTier] || 10) * wmMult);
          const ownerSocket = io.sockets.sockets.get(owner.id);
          if (!ownerSocket?.connected) continue;
          owner.gold = (owner.gold || 0) + wGold;
          owner.score = (owner.score || 0) + wScore;
          if (owner._authUser) {
            owner._authUser.coins = (owner._authUser.coins || 0) + wGold;
            owner._authUser.gold = owner._authUser.coins;
            owner._authUser.score = Math.max(owner._authUser.score || 0, owner.score);
          }
        }
      }
    }
  }

  // 1c. Passive Helmet Regen (Druid King grants +3 HP/sec)
  for (const p of players.values()) {
    if (p && (p.hp ?? 0) > 0 && !p._dead && p.hp < (p.maxHp || 250)) {
      if (p.helmetSkin === 'helmet_druid') {
        p.hp = Math.min(p.maxHp || 250, p.hp + 3);
        p.hpSeq = (p.hpSeq || 0) + 1;
        p.hpAt = Date.now();
        io.to(p.id).emit('self_state', { hp: p.hp, hpSeq: p.hpSeq, hpAt: p.hpAt });
      }
    }
  }

  // 1b. Resource collector buildings: owner keeps inventory ticking in sync with the world.
  for (const building of buildings.values()) {
    if (!building || Number(building.type) !== 10 || (building.hp ?? 100) <= 0) continue;
    const owner = players.get(building.ownerId);
    if (owner && (owner.hp ?? 0) > 0) syncOwnerResourceCollector(owner, building, Date.now());
  }

  const HEAL_PAD_VALUES = [2, 4, 7, 11, 16, 22];
  const HEAL_PAD_RANGES = [90, 105, 120, 135, 150, 165];
  for (const building of buildings.values()) {
    if (!building || Number(building.type) !== 9 || (building.hp ?? 100) <= 0) continue;
    const tier = Math.max(0, Math.min(5, Number(building.tier) || 0));
    const healAmount = HEAL_PAD_VALUES[tier];
    const healRange = HEAL_PAD_RANGES[tier];
    for (const target of players.values()) {
      if (!target || (target.hp ?? 0) <= 0 || (target.hp ?? 0) >= (target.maxHp || 250)) continue;
      const isOwner = target.id === building.ownerId;
      const isClanMate = building.ownerClanId && target.clanId === building.ownerClanId;
      if (!isOwner && !isClanMate) continue;
      const dx = (Number(target.x) || 0) - building.x;
      const dy = (Number(target.y) || 0) - building.y;
      if (dx * dx + dy * dy > healRange * healRange) continue;
      const previousHp = target.hp;
      target.hp = Math.min(target.maxHp || 250, target.hp + healAmount);
      if (target.hp !== previousHp) {
        target.hpSeq = (target.hpSeq || 0) + 1;
        target.hpAt = Date.now();
      }
    }
  }

  // 2. Periodic self_state confirmation (1Hz) — economy & vitals only, NO stale position overrides
  for (const [id, p] of players) {
    if (!p || (p.hp ?? 0) <= 0) continue;
    const s = io.sockets.sockets.get(id);
    if (s && s.connected) {
      s.emit('self_state', {
        hp: p.hp, maxHp: p.maxHp, baseMaxHp: p._loadoutBaseMaxHp,
        hpSeq: p.hpSeq || 0, hpAt: p.hpAt || 0,
        sc: p.score, g: p.gold, xp: p.xp, seq: p.stateSeq || 0,
        k: p.kills || 0,
        wood: p.wood, stone: p.stone, apples: p.apples,
        x: p.x, y: p.y, a: p.angle || 0
      });
    }
  }
}, 1000);

setInterval(() => {
  for (const [id, p] of players) {
    if (!p || (p.hp ?? 0) <= 0) continue;
    const s = io.sockets.sockets.get(id);
    if (!s || !s.connected) continue;
    const payload = {
      x: p.x,
      y: p.y,
      a: p.angle || 0,
      hp: p.hp,
      maxHp: p.maxHp,
      baseMaxHp: p._loadoutBaseMaxHp,
      hpSeq: p.hpSeq || 0,
      hpAt: p.hpAt || Date.now(),
      sc: p.score,
      g: p.gold,
      xp: p.xp,
      k: p.kills || 0,
      wood: p.wood,
      stone: p.stone,
      apples: p.apples,
      seq: p.stateSeq || 0,
      trappedBy: p.trappedBy || null,
      trappedX: p.trappedX ?? null,
      trappedY: p.trappedY ?? null
    };
    const key = stateSignature(payload);
    const lastKey = p._lastSelfStateKey;
    const lastSent = Number(p._lastSelfStateAt || 0);
    const shouldSend = lastKey !== key || Date.now() - lastSent >= 250;
    if (shouldSend) {
      s.volatile.emit('self_state', payload);
      p._lastSelfStateKey = key;
      p._lastSelfStateAt = Date.now();
    }
  }
}, 80);

setInterval(broadcastMobIds, 2000);

// Realtime leaderboard & bounty updates every 2s
setInterval(() => {
  if (players.size === 0) return;
  updateBounty();
  const list = [...players.values()]
    .filter(p => {
      if (!p || !p.id || p.isBot || isBotLeaderboardName(p.name)) return false;
      return io.sockets.sockets.get(p.id)?.connected && (p.hp ?? 0) > 0;
    })
    .map(p => ({
      id: p.id,
      name: (p.clanTag ? `[${p.clanTag}] ` : '') + (p.name || 'forestbrawl'),
      xp: Number(p.xp ?? p._authUser?.xp ?? 0),
      rankId: rankInfo(Number(p.xp ?? p._authUser?.xp ?? 0)).visualRankId,
      rankName: rankInfo(Number(p.xp ?? p._authUser?.xp ?? 0)).name,
      score: Number(p.score ?? p.gold ?? 0),
      gold: Number(p.gold ?? 0),
      kills: p.kills || 0,
      profileCosmetics: p._authUser ? {
        avatarId: p._authUser.equippedItems?.profil_avatar || 'wolf',
        effectId: p._authUser.equippedItems?.profil_efekt || p._authUser.equippedItems?.efektler || 'effect_none',
        frameId: p._authUser.equippedItems?.profil_cerceve || 'frame_woodland'
      } : (p.profileCosmetics || { avatarId: 'wolf', effectId: 'effect_none', frameId: 'frame_woodland' })
    }))
    .sort((a, b) => (b.gold - a.gold) || (b.score - a.score) || (b.xp - a.xp))
    .slice(0, 10);
  io.emit('live_lb', list);
}, 2000);

// Auto-cleanup ONLY when socket is actually disconnected.
// Never delete connected players even if they are in death/respawn screen!
setInterval(() => {
  if (players.size === 0) return;
  const now = Date.now();
  for (const [id, player] of players) {
    const socket = io.sockets.sockets.get(id);
    const isDisconnected = !socket || !socket.connected;
    if (isDisconnected && (now - (player.stateAt || now) > 60000)) {
      onPlayerDeath(id);
      if (player?.roomId && rooms.has(player.roomId)) {
        const roomSet = rooms.get(player.roomId);
        roomSet.delete(id);
        if (roomSet.size === 0) rooms.delete(player.roomId);
      }
      players.delete(id);
      io.emit('player_dead', { id });
      io.emit('player_left', { id, name: player.name || 'Oyuncu' });
      broadcastOnlineCount();
    }
  }
}, 3000);

io.on('connection', (socket) => {
  const clientIp = requestClientKey(socket.request || { headers: {}, socket: socket.conn?.transport?.socket });
  if (isClientBanned(clientIp, null)) {
    socket.emit('server_announce', { message: 'Sunucudan yasaklandınız (Banned).', msg: 'Sunucudan yasaklandınız (Banned).', text: 'Sunucudan yasaklandınız (Banned).', level: 'warning', title: 'YASAKLANDINIZ' });
    socket.disconnect(true);
    return;
  }
  socket.emit('online_count', io.engine.clientsCount);

  socket.on('spectate', (data = {}) => {
    const token = (typeof data === 'object' && data ? data.token : '') || socket.handshake?.auth?.token || socket.handshake?.query?.token || '';
    const authUser = verifyToken(token);
    const isOwner = Boolean(socket.request && getOwnerSession(socket.request));
    if (!authUser && !isOwner) {
      socket.emit('spectate_error', { msg: 'İzleyici modu için kimlik doğrulaması gereklidir.' });
      return;
    }
    socket.data.isSpectator = true;
    ensureMobs();
    const currentPlayers = Object.fromEntries([...players].map(([id, player]) => [id, compactState(player)]));
    socket.emit('welcome', {
      id: socket.id,
      players: currentPlayers,
      buildings: Object.fromEntries(buildings),
      worldSeed,
      resHp: Object.fromEntries(serverResources.map(resource => [resource.idx, { hp: resource.hp, maxHp: resource.maxHp, destroyed: resource.destroyed }])),
      mobs: [...mobs.values()].map(publicMob),
      resources: previewWorldResources,
      bountyId: currentBountyId,
      isHost: false,
      isSpectator: true,
      announcement: adminConfig.announcement || ''
    });
    socket.emit('mob_ids', [...mobs.keys()]);
    socket.emit('world_boss_states', publicWorldBosses());
  });

  socket.on('loadout_select', (data = {}) => {
    const player = players.get(socket.id);
    if (!player) return;
    const nextLoadout = sanitizePlayerLoadout(data.role, data.helmet);
    const premiumDesign = sanitizePremiumDesign(data);
    player.role = nextLoadout.role;
    player.helmet = nextLoadout.helmet;
    player.designWeapon = premiumDesign.weapon;
    player.loadoutSet = premiumDesign.set;
    applyLoadoutStats(player);
    player.hpSeq = (player.hpSeq || 0) + 1;
    player.hpAt = Date.now();
    socket.emit('self_state', {
      hp: player.hp, maxHp: player.maxHp, baseMaxHp: player._loadoutBaseMaxHp,
      hpSeq: player.hpSeq, hpAt: player.hpAt
    });
    socket.emit('loadout_update', {
      role: player.role,
      helmet: player.helmet,
      weapon: player.designWeapon,
      set: player.loadoutSet,
      weaponInfo: player.weaponInfo,
      setInfo: player.setInfo,
      roleInfo: BUILD_ROLES[player.role],
      helmetInfo: BUILD_HELMETS[player.helmet],
      maxHp: player.maxHp,
      damageMultiplier: player.damageMultiplier,
      armorMultiplier: player.armorMultiplier,
      speedMultiplier: player.speedMultiplier,
      at: Date.now()
    });
  });

  socket.on('helmet_equip', (data = {}) => {
    if (socketEventRateLimited(socket, 'helmet_equip')) return;
    const player = players.get(socket.id);
    if (!player) return;
    const helmetId = typeof data.helmetId === 'string' ? data.helmetId.trim() : '';
    if (helmetId && (!(player.ownedHelmets || []).includes(helmetId) || !getHelmetItemStats(helmetId))) {
      return socket.emit('helmet_equip_res', { ok: false, error: 'Bu kaska sahip değilsiniz.' });
    }
    player.helmetSkin = helmetId || null;
    applyLoadoutStats(player);
    player.hpSeq = (player.hpSeq || 0) + 1;
    player.hpAt = Date.now();
    const helmetItemStats = player.helmetSkin ? getHelmetItemStats(player.helmetSkin) : null;
    io.emit('equipment_update', { id: socket.id, helmetSkin: player.helmetSkin });
    socket.emit('self_state', { 
      hp: player.hp, 
      hpSeq: player.hpSeq, 
      hpAt: player.hpAt,
      maxHp: player.maxHp,
      baseMaxHp: player._loadoutBaseMaxHp,
      damageMultiplier: player.damageMultiplier,
      armorMultiplier: player.armorMultiplier,
      speedMultiplier: player.speedMultiplier,
      harvestMultiplier: player.harvestMultiplier,
      windmillMultiplier: player.windmillMultiplier,
      hpTheme: helmetItemStats?.hpTheme || ''
    });
  });

  socket.on('join', (data = {}) => {
    if (players.has(socket.id)) {
      const existing = players.get(socket.id);
      if (existing) normalizePlayerSnapshot(existing);
      socket.emit('welcome', {
        id: socket.id,
        players: Object.fromEntries([...players].filter(([id]) => id !== socket.id).map(([id, player]) => [id, compactFullState(player)])),
        buildings: Object.fromEntries(buildings),
        worldSeed,
        resHp: Object.fromEntries(serverResources.map(resource => [resource.idx, { hp: resource.hp, maxHp: resource.maxHp, destroyed: resource.destroyed }])),
        mobs: [...mobs.values()].map(publicMob),
        bountyId: currentBountyId,
        isHost: players.size <= 1,
        announcement: adminConfig.announcement || '',
        loadoutCatalog: buildLoadoutCatalog(),
        loadout: {
          role: existing.role || 'tank', helmet: existing.helmet || 'guardian',
          weapon: existing.designWeapon || 'sword', set: existing.loadoutSet || 'sunforge'
        }
      });
      socket.emit('mob_ids', [...mobs.keys()]);
      socket.emit('world_boss_states', publicWorldBosses());
      return;
    }
    const clientIp = requestClientKey(socket.request || { headers: {}, socket: socket.conn?.transport?.socket });
    const authUser = verifyToken(data.token);
    const playerName = authUser ? authUser.username : (String(data.name || 'forestbrawl').trim().slice(0, 20) || 'forestbrawl');
    if (isClientBanned(clientIp, playerName)) {
      socket.emit('server_announce', { message: 'Bu hesap veya IP adresi yasaklanmıştır.', msg: 'Bu hesap veya IP adresi yasaklanmıştır.', text: 'Bu hesap veya IP adresi yasaklanmıştır.', level: 'warning', title: 'YASAKLANDINIZ' });
      socket.disconnect(true);
      return;
    }
    if (adminConfig.maintenance) {
      socket.emit('server_announce', { message: 'Sunucu bakım modunda. Birazdan tekrar deneyin.', msg: 'Sunucu bakım modunda. Birazdan tekrar deneyin.', text: 'Sunucu bakım modunda. Birazdan tekrar deneyin.', level: 'warning', title: 'SUNUCU BAKIMI' });
      return;
    }
    socket.data.authUser = authUser || null;
    const playerRank = authUser ? rankInfo(authUser.xp || 0) : rankInfo(Number(data.xp || 0));
    const initialScore = authUser ? Math.max(0, Number(authUser.score) || 0) : 0;
    const initialGold = 0;
    const initialXp = Math.max(0, Number(authUser?.xp) || 0);
    const requestedSkin = String(data.skin || 'default');
    const equippedSkin = authUser?.equippedItems?.deriler || authUser?.equippedItems?.profil_avatar;
    const authorizedSkin = authUser && equippedSkin && canEquipShopItem(authUser, 'deriler', equippedSkin)
      ? equippedSkin
      : (authUser ? (canEquipShopItem(authUser, 'deriler', requestedSkin) ? requestedSkin : 'wolf') : requestedSkin);
    const gameMode = 'online';
    const guestId = String(data.guestId || '').slice(0, 80);
    let baseWorldX = normalizeWorldCoord(data.x, 0);
    let baseWorldY = normalizeWorldCoord(data.y, 0);
    if (!data.x && !data.y) {
      const vSpawn = getBeginnerVillageSpawn();
      baseWorldX = vSpawn.x;
      baseWorldY = vSpawn.y;
    }
    const ownedAxes = authUser
      ? normalizeOwnedTiers(authUser.ownedAxes)
      : normalizeOwnedTiers(data.ownedAxes);
    const ownedSwords = authUser
      ? normalizeOwnedTiers(authUser.ownedSwords)
      : normalizeOwnedTiers(data.ownedSwords);
    const ownedHelmets = authUser
      ? normalizeOwnedItemIds(authUser.ownedHelmets, /^helmet_[a-z0-9_]{1,48}$/)
      : normalizeOwnedItemIds(data.ownedHelmets, /^helmet_[a-z0-9_]{1,48}$/);
    const ownedScythes = authUser
      ? normalizeOwnedItemIds(authUser.ownedScythes, /^scythe_tier_[1-8]$/)
      : normalizeOwnedItemIds(data.ownedScythes, /^scythe_tier_[1-8]$/);
    const requestedAxeTier = Math.max(0, Math.min(11, Math.floor(Number(authUser?.axeTier ?? data.axeTier) || 0)));
    const requestedSwordTier = Math.max(0, Math.min(11, Math.floor(Number(authUser?.swordTier ?? data.swordTier) || 0)));
    const state = {
      ...data,
      mode: gameMode,
      x: baseWorldX,
      y: baseWorldY,
      skin: authorizedSkin === 'thor' && !canUseThor(authUser) ? 'wolf' : authorizedSkin,
      name: playerName,
      rk: playerRank.visualRankId,
      rankId: playerRank.rankId,
      visualRankId: playerRank.visualRankId,
      rankName: playerRank.name,
      hp: clampNumber(data.hp ?? 250, 250, 0, clampNumber(data.maxHp ?? 250, 250, 1, 5000)),
      maxHp: clampNumber(data.maxHp ?? 250, 250, 1, 5000),
      baseMaxHp: 250,
      hpSeq: 0,
      gold: initialGold,
      xp: initialXp,
      meleeLevel: Math.max(1, Math.min(100, Number(authUser?.meleeLevel) || 1)),
      meleeXp: Math.max(0, Number(authUser?.meleeXp) || 0),
      defenceLevel: Math.max(1, Math.min(100, Number(authUser?.defenceLevel) || 1)),
      defenceXp: Math.max(0, Number(authUser?.defenceXp) || 0),
      kills: authUser ? Math.max(0, Number(authUser.kills) || 0) : 0,
      score: initialScore,
      sc: initialScore,
      matchStartKills: authUser ? Math.max(0, Number(authUser.kills) || 0) : 0,
      matchStartScore: initialScore,
      matchStartGold: 0,
      matchStartedAt: Date.now(),
      _matchFinalized: false,
      id: socket.id,
      clanId: '',
      clanTag: '',
      wood: 50,
      stone: 30,
      apples: 5,
      acc: {
        ...(data.acc || {}),
        h: null,
        w: String(data.acc?.w || '').startsWith('scythe_') ? null : (data.acc?.w || null)
      },
      weapon: Number(data.weapon) || 1,
      designWeapon: sanitizePremiumDesign(data).weapon,
      loadoutSet: sanitizePremiumDesign(data).set,
      axeTier: ownedAxes.includes(requestedAxeTier) ? requestedAxeTier : 0,
      swordTier: ownedSwords.includes(requestedSwordTier) ? requestedSwordTier : 0,
      ownedAxes,
      ownedSwords,
      ownedHelmets,
      ownedScythes,
      lootBag: sanitizeLootBag(authUser?.lootBag),
      lootEquipment: sanitizeLootEquipment(authUser?.lootEquipment, sanitizeLootBag(authUser?.lootBag)),
      role: sanitizePlayerLoadout(data.role, data.helmet).role,
      helmet: sanitizePlayerLoadout(data.role, data.helmet).helmet,
      damageMultiplier: Number(data.damageMultiplier) || 1,
      armorMultiplier: Number(data.armorMultiplier) || 1,
      speedMultiplier: Number(data.speedMultiplier) || 1,
      axeSkin: data.axeSkin || data.acc?.b || null,
      swordSkin: String(data.swordSkin || data.acc?.w || '').startsWith('scythe_')
        ? null
        : (data.swordSkin || data.acc?.w || null),
      scytheId: ownedScythes.includes(authUser?.scytheId || data.scytheId) ? (authUser?.scytheId || data.scytheId) : null,
      helmetSkin: ownedHelmets.includes(authUser?.helmetSkin || data.helmetSkin) ? (authUser?.helmetSkin || data.helmetSkin) : null,
      buildX: typeof data.buildX === 'number' ? data.buildX : null,
      buildY: typeof data.buildY === 'number' ? data.buildY : null,
      profileCosmetics: authUser?.equippedItems ? {
        avatarId: authUser.equippedItems.profil_avatar || 'wolf',
        effectId: authUser.equippedItems.profil_efekt || authUser.equippedItems.efektler || 'effect_none',
        frameId: authUser.equippedItems.profil_cerceve || 'frame_woodland'
      } : (data.profileCosmetics || null),
      visibleMobIds: new Set(),
      visiblePlayerIds: new Set(),
      hpAt: Date.now(),
      stateAt: Date.now(),
      _guestId: guestId,
      _authUser: authUser
    };
    applyLoadoutStats(state);
    const reconnectSession = guestId ? reconnectSessions.get(guestId) : null;
    let canRestoreReconnect = false;
    if (reconnectSession && reconnectSession.savedAt > Date.now() - 60000 && reconnectSession.state?.hp > 0 && !reconnectSession.state?._dead) {
      const ipMatch = !reconnectSession.clientIp || reconnectSession.clientIp === clientIp;
      const authMatch = !reconnectSession.authUser || (authUser && authUser.username === reconnectSession.authUser.username);
      const secretMatch = Boolean(reconnectSession.reconnectSecret && data.reconnectSecret && data.reconnectSecret === reconnectSession.reconnectSecret);

      if (reconnectSession.authUser) {
        if (authMatch) canRestoreReconnect = true;
      } else {
        if ((ipMatch || secretMatch) && authMatch) canRestoreReconnect = true;
      }
    }

    if (canRestoreReconnect) {
      const saved = reconnectSession.state;
      for (const key of ['x', 'y', 'angle', 'vx', 'vy', 'hp', 'maxHp', 'hpSeq', 'hpAt', 'score', 'sc', 'gold', 'xp', 'kills', 'wood', 'stone', 'apples', 'diamond', 'amethyst', 'redite', 'weapon', 'axeTier', 'swordTier', '_preScytheSwordTier', 'axeSkin', 'swordSkin', 'scytheId', 'helmetSkin', 'ownedAxes', 'ownedSwords', 'ownedHelmets', 'ownedScythes', 'lootBag', 'lootEquipment', 'team', 'color', 'skin']) {
        if (saved[key] !== undefined) state[key] = saved[key];
      }
      for (const building of buildings.values()) {
        if (building.ownerId === reconnectSession.socketId) building.ownerId = socket.id;
      }
      reconnectSessions.delete(guestId);
    } else if (guestId) {
      reconnectSessions.delete(guestId);
    }
    state.lootBag = sanitizeLootBag(state.lootBag);
    state.lootEquipment = sanitizeLootEquipment(state.lootEquipment, state.lootBag);
    if (state.helmetSkin === 'helmet_imperator' || state.helmetSkin === 'guardian') state.helmetSkin = null;
    state.ownedHelmets = (Array.isArray(state.ownedHelmets) ? state.ownedHelmets : [])
      .filter(id => id !== 'helmet_imperator' && id !== 'guardian');
    if (state.acc?.h === 'guardian' || state.acc?.h === 'helmet_imperator') {
      state.acc = { ...state.acc, h: null };
    }
    applyLoadoutStats(state);
    state.acc = { ...(state.acc || {}), h: state.helmetSkin || null };
    const targetClanKey = String(data.clanId || '').trim();
    const requestedClan = targetClanKey ? (clans.get(targetClanKey) || Array.from(clans.values()).find(c =>
      c.id.toLowerCase() === targetClanKey.toLowerCase() ||
      c.tag.toLowerCase() === targetClanKey.toLowerCase() ||
      c.name.toLowerCase() === targetClanKey.toLowerCase()
    )) : null;
    let clanMember = requestedClan?.members?.find(member => member.name === state.name);
    if (requestedClan && !clanMember && requestedClan.ownerName === state.name && authUser && authUser.username === requestedClan.ownerName) {
      clanMember = { id: socket.id, name: state.name };
      requestedClan.members.push(clanMember);
    }
    updatePlayerRoom(state);
    if (requestedClan && clanMember) {
      clanMember.id = socket.id;
      if (requestedClan.ownerName === state.name && authUser && authUser.username === requestedClan.ownerName) {
        requestedClan.ownerId = socket.id;
      }
      state.clanId = requestedClan.id;
      state.clanTag = requestedClan.tag;
      socket.data.clanId = requestedClan.id;
      socket.data.clanName = state.name;
      socket.join(`clan:${requestedClan.id}`);
      emitClanUpdate(requestedClan);
    }
    const incomingPartyCode = String(data.partyCode || data.team || '').trim().toUpperCase();
    if (incomingPartyCode) {
      state.partyCode = incomingPartyCode;
      state.team = incomingPartyCode;
      let party = parties.get(incomingPartyCode);
      if (!party) {
        party = { code: incomingPartyCode, members: [{ id: socket.id, name: state.name || 'Oyuncu' }], owner: socket.id };
        parties.set(incomingPartyCode, party);
      } else if (!party.members.some(m => m.id === socket.id) && party.members.length < 8) {
        party.members.push({ id: socket.id, name: state.name || 'Oyuncu' });
      }
      socket.join(`party:${incomingPartyCode}`);
      io.to(`party:${incomingPartyCode}`).emit('party_update', party);
    }
    players.set(socket.id, state);
    ensureMobs(state.x || 0, state.y || 0);
    rebuildMobGrid();
    let visibleMobs = nearbyMobs(state.x || 0, state.y || 0, MOB_AOI_RADIUS);
    if (visibleMobs.length < 12) {
      const pBiome = previewBiome(state.x || 0, state.y || 0);
      for (let si = 0; si < 10; si++) {
        createMob(pBiome, state.x || 0, state.y || 0);
      }
      rebuildMobGrid();
      visibleMobs = nearbyMobs(state.x || 0, state.y || 0, MOB_AOI_RADIUS);
    }
    state.visibleMobIds = new Set(visibleMobs.map(mob => mob.id));
    const others = Object.fromEntries([...players].filter(([id, player]) => {
      if (id === socket.id) return false;
      if ((player.mode || 'online') !== (state.mode || 'online')) return false;
      const dx = (Number(player.x) || 0) - (Number(state.x) || 0);
      const dy = (Number(player.y) || 0) - (Number(state.y) || 0);
      return dx * dx + dy * dy <= PLAYER_AOI_RADIUS * PLAYER_AOI_RADIUS;
    }).map(([id, player]) => [id, compactFullState(player)]));
    state.visiblePlayerIds = new Set(Object.keys(others));
    const reconnectSecret = crypto.randomBytes(16).toString('hex');
    state._reconnectSecret = reconnectSecret;
    socket.emit('welcome', {
      id: socket.id,
      mode: state.mode || 'online',
      players: others,
      buildings: Object.fromEntries(buildings),
      worldSeed,
      resHp: Object.fromEntries(serverResources.map(resource => [resource.idx, { hp: resource.hp, maxHp: resource.maxHp, destroyed: resource.destroyed }])),
      mobs: visibleMobs.map(publicMob),
      bountyId: currentBountyId,
      reconnectSecret,
      announcement: adminConfig.announcement || '',
      isHost: players.size === 1,
      gear: {
        axeTier: state.axeTier || 0,
        swordTier: state._preScytheSwordTier ?? (state.scytheId ? 0 : state.swordTier || 0),
        equippedSwordTier: state.swordTier || 0,
        helmetSkin: state.helmetSkin || null,
        scytheId: state.scytheId || null,
        ownedAxes: state.ownedAxes || [0],
        ownedSwords: state.ownedSwords || [0],
        ownedHelmets: state.ownedHelmets || [],
        ownedScythes: state.ownedScythes || []
      },
      loadoutCatalog: buildLoadoutCatalog(),
      loadout: {
        role: state.role, helmet: state.helmet,
        weapon: state.designWeapon, set: state.loadoutSet,
        roleInfo: BUILD_ROLES[state.role], helmetInfo: BUILD_HELMETS[state.helmet],
        weaponInfo: state.weaponInfo, setInfo: state.setInfo
      }
    });
    socket.emit('self_state', {
      hp: state.hp, maxHp: state.maxHp, baseMaxHp: state._loadoutBaseMaxHp,
      hpSeq: state.hpSeq || 0, hpAt: state.hpAt || Date.now(),
      sc: state.score || 0, g: state.gold || 0, xp: state.xp || 0,
      wood: state.wood || 0, stone: state.stone || 0, apples: state.apples || 0,
      diamond: state.diamond || 0, amethyst: state.amethyst || 0, redite: state.redite || 0
    });
    socket.emit('loot_inventory_state', lootInventoryPayload(state));
    socket.emit('mob_ids', [...state.visibleMobIds]);
    socket.emit('world_boss_states', publicWorldBosses());
    for (const [otherId, otherPlayer] of players) {
      if (otherId !== socket.id && (otherPlayer.mode || 'online') === (state.mode || 'online')) {
        io.to(otherId).emit('player_join', { id: socket.id, state: compactFullState(state) });
      }
    }
    broadcastOnlineCount();
    updateBounty();
  });

  socket.on('respawn', () => {
    let player = players.get(socket.id);
    if (!player || ((player.hp ?? 0) > 0 && !player._dead)) return;
    const spawnPt = getBeginnerVillageSpawn();
    onPlayerDeath(socket.id);
    player.hp = player.maxHp ?? 250;
    player.x = spawnPt.x;
    player.y = spawnPt.y;
    player.vx = 0;
    player.vy = 0;
    player.score = 0;
    player.sc = 0;
    player.gold = 0;
    player.matchStartKills = player._authUser ? Math.max(0, Number(player._authUser.kills) || 0) : 0;
    player.matchStartScore = 0;
    player.matchStartGold = 0;
    player.matchStartedAt = Date.now();
    player._matchFinalized = false;
    player.xp = player._authUser ? Math.max(0, Number(player._authUser.xp) || 0) : Math.max(0, Number(player.xp) || 0);
    player.rankId = player._authUser ? rankInfo(player.xp).rankId : player.rankId;
    player.rankName = player._authUser ? rankInfo(player.xp).name : player.rankName;
    player.wood = 0;
    player.stone = 0;
    player.diamond = 0;
    player.amethyst = 0;
    player.redite = 0;
    persistPlayerEquipment(player);
    player.apples = 5;
    player.weapon = 1;
    player.trappedBy = null;
    player.hpSeq = 0;
    player.hpAt = Date.now();
    player.visibleMobIds = new Set();
    player.visiblePlayerIds = new Set();
    player.stateAt = Date.now();
    player._dead = false;
    if (player._guestId) reconnectSessions.delete(player._guestId);
    const loadout = sanitizePlayerLoadout(player.role, player.helmet);
    player.role = loadout.role;
    player.helmet = loadout.helmet;
    applyLoadoutStats(player);
    socket.emit('own_respawn', { x: spawnPt.x, y: spawnPt.y });
    socket.emit('self_state', { x: spawnPt.x, y: spawnPt.y, hp: player.hp, hpSeq: 0, hpAt: player.hpAt, sc: player.score, g: player.gold, xp: player.xp, k: player.kills, matchKills: 0, wood: player.wood, stone: player.stone, apples: player.apples, diamond: player.diamond || 0, amethyst: player.amethyst || 0, redite: player.redite || 0, seq: player.stateSeq || 0 });
    socket.emit('buildings_sync', { buildings: Object.fromEntries(buildings) });
    io.emit('gear_update', {
      id: socket.id, axeTier: player.axeTier, swordTier: player.swordTier,
      helmetSkin: player.helmetSkin || '', scytheId: player.scytheId || null
    });
    io.emit('player_respawn', { id: socket.id, state: compactFullState(player) });
    broadcastOnlineCount();
  });

  socket.on('state', (data = {}) => {
    if (socketEventRateLimited(socket, 'state')) return;
    let player = players.get(socket.id);
    if (!player) return;
    const prevX = Number(player.x) || 0;
    const prevY = Number(player.y) || 0;
    const incomingX = Number(data.x);
    const incomingY = Number(data.y);
    const incomingSeq = Number.isFinite(data.seq) ? Number(data.seq) : null;
    let acceptedX = incomingX;
    let acceptedY = incomingY;

    // Sequence check with wrap tolerance: drop strictly older packets unless a wrap/respawn happened
    if (incomingSeq !== null && incomingSeq <= (player.stateSeq || 0) && (player.stateSeq - incomingSeq < 1000)) {
      return;
    }

    let needsPosCorrection = false;
    if (Number.isFinite(incomingX) && Number.isFinite(incomingY)) {
      const dx = incomingX - prevX;
      const dy = incomingY - prevY;
      const dist = Math.hypot(dx, dy);
      const worldLimit = WORLD;
      const now = Date.now();
      const elapsedMs = Math.max(16, Math.min(1000, now - (player.stateAt || now)));

      // ── Boost Pad Detection & Anti-Cheat Allowance ──
      const momMag = Math.hypot(Number(data.momX) || 0, Number(data.momY) || 0);
      const nearBoostPad = nearbyBuildings(prevX, prevY, 480).some(b => b.type === 5 && (b.hp ?? 100) > 0) ||
                           nearbyBuildings(incomingX, incomingY, 480).some(b => b.type === 5 && (b.hp ?? 100) > 0);
      const hasPhysicalImpulse = momMag > 5 && (Boolean(player.momX) || Boolean(player.momY));
      const legitimateBoost = nearBoostPad || Boolean(player.onTrain) || hasPhysicalImpulse;
      if (legitimateBoost) {
        player.boostUntil = Math.max(player.boostUntil || 0, now + 2000);
      }
      const isBoosted = Boolean((player.boostUntil && now < player.boostUntil) || player.onTrain);

      const maxAllowedDist = isBoosted
        ? Math.max(700, Math.min(600 + elapsedMs * 4.5, 3600))
        : Math.max(220, Math.min(MAX_MOVE_DELTA_PER_TICK + elapsedMs * 2.8, 1600));
      const currentMaxSpeed = isBoosted ? 3500 : MAX_PLAYER_SPEED;

      if (Math.abs(incomingX) > worldLimit || Math.abs(incomingY) > worldLimit) {
        acceptedX = Math.max(-worldLimit, Math.min(worldLimit, incomingX));
        acceptedY = Math.max(-worldLimit, Math.min(worldLimit, incomingY));
        needsPosCorrection = true;
      } else if (dist > maxAllowedDist) {
        // Smoothly clamp displacement in direction of movement instead of freezing completely.
        const ratio = maxAllowedDist / dist;
        acceptedX = prevX + dx * ratio;
        acceptedY = prevY + dy * ratio;
        data.vx = Number.isFinite(Number(data.vx)) ? clampNumber(Number(data.vx) * ratio, 0, -currentMaxSpeed, currentMaxSpeed) : 0;
        data.vy = Number.isFinite(Number(data.vy)) ? clampNumber(Number(data.vy) * ratio, 0, -currentMaxSpeed, currentMaxSpeed) : 0;
        needsPosCorrection = true;
      }
      if (Number.isFinite(Number(data.vx))) data.vx = clampNumber(Number(data.vx), 0, -currentMaxSpeed, currentMaxSpeed);
      if (Number.isFinite(Number(data.vy))) data.vy = clampNumber(Number(data.vy), 0, -currentMaxSpeed, currentMaxSpeed);
    }

    if (player.trappedBy) {
      const b = buildings.get(player.trappedBy);
      if (!b || b.type !== 6 || (b.hp ?? 100) <= 0 || b.ownerId === player.id) {
        releaseTrapVictim(player.id, player.trappedBy);
        player.trappedBy = null;
        player.trappedX = null;
        player.trappedY = null;
      } else {
        const offsetX = (Number(data.x) || prevX) - (player.trappedX ?? prevX);
        const offsetY = (Number(data.y) || prevY) - (player.trappedY ?? prevY);
        const trapRadius = (Number(b.radius) || 78) + 26;
        const trapDistance = Math.hypot((Number(player.x) || 0) - (Number(b.x) || 0), (Number(player.y) || 0) - (Number(b.y) || 0));
        if (Math.hypot(offsetX, offsetY) > 2 || trapDistance > trapRadius) {
          needsPosCorrection = true;
        }
        if (!dedupeTrapState(player, player.trappedBy)) {
          needsPosCorrection = true;
        }
        if (enforceCanonicalTrapLock(player)) {
          needsPosCorrection = true;
        }
        data.vx = 0;
        data.vy = 0;
        data.x = player.trappedX ?? data.x;
        data.y = player.trappedY ?? data.y;
        acceptedX = normalizeWorldCoord(data.x, prevX);
        acceptedY = normalizeWorldCoord(data.y, prevY);
      }
    }
    if (player._ownerFrozen) {
      acceptedX = prevX;
      acceptedY = prevY;
      data.vx = 0;
      data.vy = 0;
      needsPosCorrection = true;
    }
    acceptedX = normalizeWorldCoord(acceptedX, prevX);
    acceptedY = normalizeWorldCoord(acceptedY, prevY);
    const previousEquipmentKey = `${player.scytheId || ''}|${player.helmetSkin || ''}`;
    for (const key of ['x', 'y', 'angle', 'vx', 'vy', 'isAttacking', 'attackTimer', 'attackDuration', 'team', 'color', 'skin', 'acc', 'buildX', 'buildY', 'weapon', 'designWeapon', 'loadoutSet', 'axeTier', 'swordTier', 'axeSkin', 'swordSkin', 'scytheId', 'helmetSkin']) {
      if (key === 'x' && Number.isFinite(acceptedX)) player.x = acceptedX;
      else if (key === 'y' && Number.isFinite(acceptedY)) player.y = acceptedY;
      else if (key === 'skin' && data[key] !== undefined) player.skin = String(data[key]) === 'thor' && !canUseThor(player._authUser) ? 'wolf' : String(data[key]);
      else if (key === 'weapon' && data[key] !== undefined) player.weapon = Number(data[key]) || 1;
      else if (key === 'designWeapon' && data[key] !== undefined) player.designWeapon = sanitizePremiumDesign({ weapon: data[key], set: player.loadoutSet }).weapon;
      else if (key === 'loadoutSet' && data[key] !== undefined) player.loadoutSet = sanitizePremiumDesign({ weapon: player.designWeapon, set: data[key] }).set;
      else if (key === 'axeTier' && data[key] !== undefined) {
          const reqTier = Math.max(0, Math.min(11, Number(data[key]) || 0));
          if ((player.ownedAxes || [0]).includes(reqTier)) player.axeTier = reqTier;
      }
      else if (key === 'swordTier' && data[key] !== undefined) {
        const reqTier = Math.max(0, Math.min(11, Number(data[key]) || 0));
        if ((player.ownedSwords || [0]).includes(reqTier)) player.swordTier = reqTier;
      }
      else if (key === 'helmetSkin' && data[key] !== undefined) {
        if (data[key] === null || data[key] === '') player.helmetSkin = null;
        else if ((player.ownedHelmets || []).includes(String(data[key])) && getHelmetItemStats(data[key])) {
          player.helmetSkin = String(data[key]);
        } else {
          player.helmetSkin = null;
        }
      }
      else if (key === 'scytheId' && data[key] !== undefined) {
        if (data[key] === null || data[key] === '') {
          player.scytheId = null;
          player._preScytheSwordTier = null;
        }
        else if ((player.ownedScythes || []).includes(String(data[key])) && getScytheItemStats(data[key])) {
          player.scytheId = String(data[key]);
        }
      }
      else if (key === 'acc' && data[key] !== undefined && data[key] && typeof data[key] === 'object') {
        const nextAcc = { ...data[key], h: player.helmetSkin || null };
        if (String(nextAcc.w || '').startsWith('scythe_') &&
            (!(player.ownedScythes || []).includes(String(nextAcc.w)) || !getScytheItemStats(nextAcc.w))) {
          nextAcc.w = null;
        }
        player.acc = nextAcc;
      }
      else if (key === 'swordSkin' && data[key] !== undefined) {
        const swordSkin = String(data[key] || '');
        if (swordSkin.startsWith('scythe_')) {
          if ((player.ownedScythes || []).includes(swordSkin) && getScytheItemStats(swordSkin)) {
            player.swordSkin = swordSkin;
            player.scytheId = swordSkin;
          }
        } else {
          player.swordSkin = data[key];
        }
      }
      else if (data[key] !== undefined) player[key] = data[key];
    }
    player.acc = { ...(player.acc || {}), h: player.helmetSkin || null };
    if (`${player.scytheId || ''}|${player.helmetSkin || ''}` !== previousEquipmentKey) {
      applyLoadoutStats(player);
      player.hpSeq = (player.hpSeq || 0) + 1;
      player.hpAt = Date.now();
      const helmetItemStats = player.helmetSkin ? getHelmetItemStats(player.helmetSkin) : null;
      socket.emit('self_state', {
        hp: player.hp,
        maxHp: player.maxHp,
        baseMaxHp: player._loadoutBaseMaxHp,
        hpSeq: player.hpSeq,
        hpAt: player.hpAt,
        hpSeq: player.hpSeq || 0, 
        hpAt: Date.now(),
        hpTheme: helmetItemStats?.hpTheme || ''
      });
      broadcastPlayerEventNear(player, 'equipment_update', {
        id: socket.id,
        scytheId: player.scytheId || null,
        helmetSkin: player.helmetSkin || null,
        swordSkin: player.swordSkin || null,
        swordTier: player.swordTier || 0,
        acc: player.acc || {}
      });
    }
    // Accept predicted client resource gathering monotonically only if player is alive with rate clamp
    if (!player._dead && (player.hp ?? 100) > 0) {
      if (data.wood !== undefined) {
        const wVal = Number(data.wood);
        if (Number.isFinite(wVal) && wVal >= 0) player.wood = Math.min(2_000_000, Math.max(player.wood || 0, Math.min((player.wood || 0) + 120, wVal)));
      }
      if (data.stone !== undefined) {
        const sVal = Number(data.stone);
        if (Number.isFinite(sVal) && sVal >= 0) player.stone = Math.min(2_000_000, Math.max(player.stone || 0, Math.min((player.stone || 0) + 120, sVal)));
      }
      if (data.apples !== undefined) {
        const aVal = Number(data.apples);
        if (Number.isFinite(aVal) && aVal >= 0) player.apples = Math.min(10000, Math.max(player.apples || 0, Math.min((player.apples || 0) + 10, aVal)));
      }
    }
    capturePlayerInTrap(player);
    resolveTrapOwnerCollisions(player);

    // Advanced Networked Physics: 2-pass solid penetration resolution & velocity sliding
    const pRad = Number(player.radius) || 35;
    const initialColX = player.x;
    const initialColY = player.y;
    // Check spike contact for every player, including trapped players. A stationary
    // target must not need a movement or push event to take damage.
    const now = Date.now();
    for (const b of nearbyBuildings(player.x, player.y, pRad + 50)) {
      if (b.type === 3 && (b.hp ?? 0) > 0 && b.ownerId !== player.id) {
        const sDist = Math.hypot(player.x - b.x, player.y - b.y);
        if (sDist <= pRad + (Number(b.radius) || 34)) applySpikeDamageToTarget(player, b, now);
      }
    }

    if (!player.trappedBy) {

      for (let pass = 0; pass < 2; pass++) {
        // 1. Solid Buildings & Traps (Static, invMass = 0)
        for (const b of nearbyBuildings(player.x, player.y, pRad + 120)) {
          if (b.type === 5) continue; // Boost pad allows walkover
          if (b.type === 6) continue; // Trap capture handles entry; outer asset is not solid
          if (b.type === 6 && b.ownerId === player.id) continue; // Owner can cross own trap
          if ((b.hp ?? 100) <= 0) continue;
          const bRad = Number(b.radius) || (b.type === 8 ? 24 : (b.type === 6 ? 78 : (b.type === 10 ? 30 : 36)));
          if (resolveStaticCircleCollision(player, pRad, b.x, b.y, bRad, { x: prevX, y: prevY }) &&
              pass === 0 && data.vx !== undefined && data.vy !== undefined) {
            const dx = player.x - b.x;
            const dy = player.y - b.y;
            const distance = Math.hypot(dx, dy) || 1;
            const nx = dx / distance;
            const ny = dy / distance;
            const inwardVelocity = (Number(data.vx) || 0) * nx + (Number(data.vy) || 0) * ny;
            if (inwardVelocity < 0) {
              data.vx = (Number(data.vx) || 0) - inwardVelocity * nx;
              data.vy = (Number(data.vy) || 0) - inwardVelocity * ny;
              player.vx = data.vx;
              player.vy = data.vy;
            }
          }
        }

        // 2. Village Solid Colliders (Buildings, Well, Props, NPCs & Square Palisade Fence)
        if (Math.abs(player.x) < 850 && Math.abs(player.y) < 850) {
          for (const vc of VILLAGE_COLLIDERS) {
            if (resolveStaticCircleCollision(player, pRad, vc.x, vc.y, vc.rad, { x: prevX, y: prevY }) &&
                pass === 0 && data.vx !== undefined && data.vy !== undefined) {
              const dx = player.x - vc.x;
              const dy = player.y - vc.y;
              const distance = Math.hypot(dx, dy) || 1;
              const nx = dx / distance;
              const ny = dy / distance;
              const inwardVelocity = (Number(data.vx) || 0) * nx + (Number(data.vy) || 0) * ny;
              if (inwardVelocity < 0) {
                data.vx = (Number(data.vx) || 0) - inwardVelocity * nx;
                data.vy = (Number(data.vy) || 0) - inwardVelocity * ny;
                player.vx = data.vx;
                player.vy = data.vy;
              }
            }
          }
          resolveVillageFenceCollision(player, pRad);
        }
        const resourceSearchRadius = pRad + 224 * 0.82;
        for (const obstacle of nearbyServerObstacles(player.x, player.y, resourceSearchRadius)) {
          const resource = obstacle.resource;
          if (!resource || resource.destroyed) continue;
          const resourceRadius = (Number(resource.radius) || 38) * (SERVER_RESOURCE_COLLISION_FRACTIONS[resource.type] || 0.6);
          if (resolveStaticCircleCollision(player, pRad, obstacle.x, obstacle.y, resourceRadius, { x: prevX, y: prevY }) &&
              pass === 0 && data.vx !== undefined && data.vy !== undefined) {
            const velocity = { vx: Number(data.vx) || 0, vy: Number(data.vy) || 0 };
            const nx = player.x - obstacle.x;
            const ny = player.y - obstacle.y;
            const distance = Math.hypot(nx, ny) || 1;
            const normalX = nx / distance;
            const normalY = ny / distance;
            const inwardVelocity = velocity.vx * normalX + velocity.vy * normalY;
            if (inwardVelocity < 0) {
              velocity.vx -= inwardVelocity * normalX;
              velocity.vy -= inwardVelocity * normalY;
              data.vx = velocity.vx;
              data.vy = velocity.vy;
              player.vx = velocity.vx;
              player.vy = velocity.vy;
            }
          }
        }

        // 2. Dynamic Players (Solid Separation, Trap Pushing & Momentum Impulse)
        const nearOthers = nearbyPlayers(player.x, player.y, pRad + 80, socket.id);
        for (let oi = 0; oi < nearOthers.length; oi++) {
          const other = nearOthers[oi];
          if (!other || other.hp <= 0) continue;
          const otherRad = Number(other.radius) || 35;
          const minDist = pRad + otherRad;
          if (other.trappedBy) {
            const trappedBuilding = buildings.get(other.trappedBy);
            if (trappedBuilding?.ownerId === socket.id) {
              // Owner pushing trapped victim: enforce solid contact and push victim forward
              const tdx = (Number(other.x) || 0) - player.x;
              const tdy = (Number(other.y) || 0) - player.y;
              const tdist = Math.hypot(tdx, tdy) || 0.01;
              if (tdist < minDist) {
                pushTrappedVictim(player, other, tdx, tdy, Math.max(1.0, minDist - tdist));
              }
              continue;
            } else {
              // Non-owner cannot push trapped victim; trapped victim acts as solid obstacle
              const col = NetworkPhysics.resolveCircleCircle(player, pRad, 1.0, other, otherRad, 0.0);
              if (col && col.collided && pass === 0 && data.vx !== undefined && data.vy !== undefined) {
                NetworkPhysics.projectVelocitySlide(data, col.nx, col.ny, 0.05);
              }
              continue;
            }
          }

          // Normal dynamic player vs player (50/50 mass-weighted separation + momentum push)
          const col = NetworkPhysics.resolveCircleCircle(player, pRad, 1.0, other, otherRad, 1.0);
          if (col && col.collided) {
            if (pass === 0 && data.vx !== undefined && data.vy !== undefined) {
              NetworkPhysics.projectVelocitySlide(data, col.nx, col.ny, 0.05);
            }
            // Transmit momentum impulse to other entity
            const relVx = (player.vx || 0) - (other.vx || 0);
            const relVy = (player.vy || 0) - (other.vy || 0);
            const dot = relVx * col.nx + relVy * col.ny;
            if (dot < 0) {
              const impulse = -dot * 0.35;
              other.momX = (other.momX || 0) - col.nx * impulse;
              other.momY = (other.momY || 0) - col.ny * impulse;
            }
          }
        }
      }

      if (Math.hypot(player.x - initialColX, player.y - initialColY) > 65.0) {
        needsPosCorrection = true;
      }
    }
    if (incomingSeq !== null) player.stateSeq = incomingSeq;
    player.stateAt = Date.now();
    updatePlayerRoom(player);

    if (needsPosCorrection) {
      socket.emit('pos_correction', { x: player.x, y: player.y, seq: player.stateSeq || 0 });
    }
  });

  socket.on('loot_inventory_init', (data = {}) => {
    if (socketEventRateLimited(socket, 'loot_inventory_init')) return;
    const player = players.get(socket.id);
    if (!player) return;
    if (!player._authUser) {
      player.lootBag = sanitizeLootBag(data.bag);
      player.lootEquipment = sanitizeLootEquipment(data.equipped, player.lootBag);
      applyLoadoutStats(player);
      player.hpSeq = (player.hpSeq || 0) + 1;
      player.hpAt = Date.now();
    }
    emitLootInventory(player, socket);
    socket.emit('self_state', {
      hp: player.hp, maxHp: player.maxHp, baseMaxHp: player._loadoutBaseMaxHp,
      hpSeq: player.hpSeq || 0, hpAt: player.hpAt || Date.now()
    });
  });

  socket.on('loot_item_action', (data = {}) => {
    if (socketEventRateLimited(socket, 'loot_item_action')) return;
    const player = players.get(socket.id);
    if (!player || (player.hp ?? 0) <= 0 || player._dead) {
      socket.emit('loot_item_action_result', { ok: false, message: 'Esya islemi icin hayatta olmalisin.' });
      return;
    }
    const action = String(data.action || '');
    const uid = String(data.uid || '');
    player.lootBag = sanitizeLootBag(player.lootBag);
    player.lootEquipment = sanitizeLootEquipment(player.lootEquipment, player.lootBag);
    const bagIndex = player.lootBag.findIndex(item => item.uid === uid);

    if (action === 'equip') {
      if (bagIndex < 0) {
        socket.emit('loot_item_action_result', { ok: false, message: 'Bu esya cantanda bulunamadi.' });
        return;
      }
      const item = player.lootBag[bagIndex];
      const definition = LootCatalog.ITEM_BY_ID[item.id];
      const level = calculatePlayerLevel(player);
      if (!definition || level < definition.minLevel) {
        socket.emit('loot_item_action_result', { ok: false, message: `Bu esya icin ${definition?.minLevel || 1}. seviye gerekli.` });
        return;
      }
      const slot = definition.preferredRing || definition.slot;
      const previous = player.lootEquipment[slot];
      player.lootBag.splice(bagIndex, 1);
      if (previous) player.lootBag.push(previous);
      player.lootEquipment[slot] = item;
    } else if (action === 'delete') {
      if (bagIndex < 0) {
        socket.emit('loot_item_action_result', { ok: false, message: 'Yalnizca cantadaki esyalar silinebilir.' });
        return;
      }
      player.lootBag.splice(bagIndex, 1);
    } else if (action === 'unequip') {
      const slot = String(data.slot || '');
      const item = player.lootEquipment[slot];
      if (!item) {
        socket.emit('loot_item_action_result', { ok: false, message: 'Bu ekipman yuvasi bos.' });
        return;
      }
      if (player.lootBag.length >= 32) {
        socket.emit('loot_item_action_result', { ok: false, message: 'Cantada yer yok; once bir esya sil.' });
        return;
      }
      player.lootBag.push(item);
      delete player.lootEquipment[slot];
    } else {
      socket.emit('loot_item_action_result', { ok: false, message: 'Gecersiz esya islemi.' });
      return;
    }

    persistLootInventory(player);
    applyLoadoutStats(player);
    player.hpSeq = (player.hpSeq || 0) + 1;
    player.hpAt = Date.now();
    socket.emit('loot_item_action_result', { ok: true, action });
    emitLootInventory(player, socket);
    socket.emit('self_state', { hp: player.hp, maxHp: player.maxHp, baseMaxHp: player._loadoutBaseMaxHp, hpSeq: player.hpSeq || 0, hpAt: player.hpAt || Date.now() });
    broadcastPlayerStateNear(player);
  });

  socket.on('swing', (data = {}) => {
    if (socketEventRateLimited(socket, 'swing')) return;
    const attacker = players.get(socket.id);
    if (!attacker || (attacker.hp ?? 0) <= 0 || attacker._dead) return;
    const incomingWeapon = Number(data.weapon ?? attacker.weapon);
    const isBuildingWeapon = incomingWeapon >= 3 && incomingWeapon <= 10;
    const weapon = isBuildingWeapon ? incomingWeapon : (incomingWeapon === 2 ? 2 : 1);
    attacker.weapon = incomingWeapon;
    const isScythe = weapon === 2 && Boolean(attacker.scytheId || data.scytheId || (attacker.swordSkin && String(attacker.swordSkin).startsWith('scythe_')) || (data.swordSkin && String(data.swordSkin).startsWith('scythe_')));
    const now = Date.now();
    const attackSpeed = Math.max(0.88, Math.min(1.18, Number(attacker.attackSpeedMultiplier) || 1));
    const baseSwingCooldown = isBuildingWeapon ? 40 : (isScythe ? 380 : (weapon === 2 ? 330 : 300));
    const swingCooldown = isBuildingWeapon ? baseSwingCooldown : Math.round(baseSwingCooldown / attackSpeed);
    if (now - (attacker.lastSwingAt || 0) < swingCooldown) return;
    const swingId = Number.isFinite(Number(data.swingId)) ? Number(data.swingId) : null;
    if (swingId !== null && attacker.lastSwingId === swingId) return;
    const range = isScythe ? 168 : (weapon === 2 ? 140 : 128);
    const spread = isScythe ? Math.PI / 2.6 : (weapon === 2 ? Math.PI / 3.25 : Math.PI / 2.57);
    const tier = Math.max(0, Math.min(11, Number(weapon === 2 ? attacker.swordTier : attacker.axeTier) || 0));
    const dmgMult = Math.max(0.5, Math.min(3.0, Number(attacker.damageMultiplier) || 1.0));
    const damage = isBuildingWeapon ? 0 : calculateMeleeDamage(weapon, tier, { isScythe, damageMultiplier: dmgMult });
    const angle = Number(data.angle);
    if (!Number.isFinite(angle)) return;
    attacker.lastSwingAt = now;
    attacker.lastSwingId = swingId;
    attacker.lastMobHitIds = new Set();
    attacker.lastBossHitIds = new Set();
    attacker.lastBuildingHitIds = new Set();
    attacker.lastAttackAngle = angle;
    attacker.attackUntil = now + (isBuildingWeapon ? 240 : swingCooldown);
    attacker.isAttacking = true;
    attacker.attackTimer = 0;
    attacker.attackDuration = isBuildingWeapon ? 240 : Math.round((isScythe ? 380 : (weapon === 2 ? 330 : 300)) / attackSpeed);
    const attackPacket = {
      id: socket.id,
      weapon,
      angle,
      at: now,
      swingId: swingId ?? now,
      serverTime: now,
      durationMs: attacker.attackDuration
    };
    broadcastPlayerEventNear(attacker, 'player_attack', attackPacket);
    broadcastPlayerEventNear(attacker, 'playerAttack', socket.id);
    if (isBuildingWeapon) return;
    const attackerX = Number(attacker.x) || 0, attackerY = Number(attacker.y) || 0;
    if (!pvpAllowed()) return;
    // Gövde dönüşünü engelle: Oyuncunun gövde açısı saldırıyla zorla değiştirilmez, sürekli nişan açısında kalır.
    for (const [targetId, target] of players) {
      if (targetId === socket.id || target.hp <= 0) continue;
      if (!validateCombatState(attacker, target, { allowTrapHit: true, rangeLimit: range + 64, damage })) continue;
      if (swingId && target.lastHitSwingId === swingId) continue;
      if (now - (target.lastHitTime || 0) < Math.round((isScythe ? 380 : (weapon === 2 ? 330 : 300)) / attackSpeed)) continue;
      const dx = (Number(target.x) || 0) - attackerX, dy = (Number(target.y) || 0) - attackerY;
      let difference = Math.abs(Math.atan2(dy, dx) - angle);
      if (difference > Math.PI) difference = Math.PI * 2 - difference;
      if (difference > spread) continue;
      if (swingId) target.lastHitSwingId = swingId;
      target.lastHitTime = now;

      // Seviye farkı ve Melee / Defence statı etkisi (PvP)
      const aLvl = calculatePlayerLevel(attacker);
      const tLvl = calculatePlayerLevel(target);
      const lvlFactor = calculateLevelGapMultiplier(aLvl, tLvl);
      const mBonus = 1 + Math.min(0.75, (Math.max(1, Number(attacker.meleeLevel || 1)) - 1) * 0.022);
      const tDefBonus = 1 - Math.min(0.40, (Math.max(1, Number(target.defenceLevel || 1)) - 1) * 0.015);
      const finalPvpDmg = limitHitDamage(target, Math.round(damage * lvlFactor * mBonus * tDefBonus));

      applyPlayerDamage(target, finalPvpDmg);

      // Melee XP saldırgana, Defence XP hedefe
      awardCombatXp(attacker, 'melee', Math.max(6, Math.round(finalPvpDmg * 0.45)), { hitId: targetId });
      awardCombatXp(target, 'defence', Math.max(6, Math.round(finalPvpDmg * 0.55)), { from: attacker.name || 'Oyuncu' });

      // Knockback / Geri itme
      const kbForce = isScythe ? 16 : 11;
      target.vx = (target.vx || 0) + Math.cos(angle) * kbForce;
      target.vy = (target.vy || 0) + Math.sin(angle) * kbForce;
      target.x += Math.cos(angle) * (kbForce * 0.6);
      target.y += Math.sin(angle) * (kbForce * 0.6);
      if (target.isBot) alertBotAttacked(target, attacker);
      io.to(targetId).emit('pvp_hit', { dmg: finalPvpDmg, fromName: attacker.name || 'Oyuncu', angle, kbForce });
      io.to(targetId).emit('self_state', { hp: target.hp, hpSeq: target.hpSeq, hpAt: target.hpAt });
      io.emit('players', { [targetId]: compactState(target) });
      socket.emit('pvp_confirm', { targetId, dmg: finalPvpDmg, targetName: target.name || 'Oyuncu' });
      if (target.hp <= 0) {
        stealDeathLoot(attacker, target);
        onPlayerDeath(targetId);
        target.kills = target.kills || 0;
        attacker.kills = (attacker.kills || 0) + 1;
        attacker.score = (attacker.score || 0) + 150;
        socket.emit('self_state', {
          matchKills: Math.max(0, attacker.kills - (attacker.matchStartKills || 0)),
          sc: attacker.score
        });
        if (!attacker.isBot && !target.isBot) {
          recordServerQuestProgress(attacker, {
            pvpKills: 1,
            ...(BOUNTY_EVENT_ENABLED && currentBountyId && targetId === currentBountyId ? { kingKills: 1 } : {})
          });
        }
        if (BOUNTY_EVENT_ENABLED && currentBountyId && targetId === currentBountyId) {
          const bountyBonus = 300;
          attacker.gold = (attacker.gold || 0) + bountyBonus;
          attacker.score = (attacker.score || 0) + bountyBonus;
          socket.emit('bounty_kill_reward', { name: target.name || 'Oyuncu', bonus: bountyBonus });
          io.emit('bounty_killed_broadcast', { killer: attacker.name || 'Oyuncu', victim: target.name || 'Oyuncu', bonus: bountyBonus });
          currentBountyId = null;
          io.emit('bounty_update', { id: null });
        }
        io.to(targetId).emit('pvp_killed', { byName: attacker.name || 'Oyuncu' });
        io.emit('player_dead', { id: targetId });
        socket.emit('pvp_kill_confirm', { targetId, targetName: target.name || 'Oyuncu' });
        io.emit('pvp_kill_feed', { killer: attacker.name || 'Oyuncu', victim: target.name || 'Oyuncu', streak: attacker.kills });
        persistPlayerScore(attacker);
      }
      break;
    }
  });

  socket.on('pvp_hit', (data = {}) => {
    if (socketEventRateLimited(socket, 'pvp_hit')) return;
    if (!pvpAllowed()) return;
    const attacker = players.get(socket.id);
    const target = players.get(data.targetId);
    if (!attacker || !target || (attacker.hp ?? 0) <= 0 || (target.hp ?? 0) <= 0 || attacker._dead || target._dead) return;
    if (!validateCombatState(attacker, target, { allowTrapHit: true, rangeLimit: 200, damage: 1 })) return;
    const swingId = Number(data.swingId);
    const now = Date.now();
    if (!Number.isFinite(attacker.lastSwingAt) || now - attacker.lastSwingAt > 750) return;
    if (swingId && target.lastHitSwingId === swingId) return; // Dedup against swing event
    const weapon = attacker.weapon === 2 ? 2 : 1;
    const isScythe = weapon === 2 && Boolean(attacker.scytheId || (attacker.swordSkin && String(attacker.swordSkin).startsWith('scythe_')));
    const attackSpeed = Math.max(0.88, Math.min(1.18, Number(attacker.attackSpeedMultiplier) || 1));
    if (now - (target.lastHitTime || 0) < Math.round((isScythe ? 380 : 300) / attackSpeed)) return; // Prevent duplicate rapid damage
    const dx = (Number(target.x) || 0) - (Number(attacker.x) || 0);
    const dy = (Number(target.y) || 0) - (Number(attacker.y) || 0);
    const dist = Math.hypot(dx, dy);
    const range = (isScythe ? 168 : (attacker.weapon === 2 ? 140 : 128)) + 120;
    if (dist > range) return;
    const tier = Math.max(0, Math.min(11, Number(weapon === 2 ? attacker.swordTier : attacker.axeTier) || 0));
    const dmgMult = Math.max(0.5, Math.min(3.0, Number(attacker.damageMultiplier) || 1.0));
    const rawDamage = calculateMeleeDamage(weapon, tier, { isScythe, damageMultiplier: dmgMult });

    // Seviye farkı ve Melee / Defence statı etkisi (PvP)
    const aLvl = calculatePlayerLevel(attacker);
    const tLvl = calculatePlayerLevel(target);
    const lvlFactor = calculateLevelGapMultiplier(aLvl, tLvl);
    const mBonus = 1 + Math.min(0.75, (Math.max(1, Number(attacker.meleeLevel || 1)) - 1) * 0.022);
    const tDefBonus = 1 - Math.min(0.40, (Math.max(1, Number(target.defenceLevel || 1)) - 1) * 0.015);
    let damage = Math.max(1, Math.round(rawDamage * lvlFactor * mBonus * tDefBonus));

    // Draconic Crit (Ejderha Barbar)
    if (attacker.critChance && Math.random() < attacker.critChance) {
      damage = Math.round(damage * (attacker.critMultiplier || 1.75));
    }
    damage = limitHitDamage(target, damage);

    // Necromancer Lifesteal (Ruh Necromancer)
    if (attacker.lifesteal && attacker.lifesteal > 0 && (attacker.hp ?? 0) < (attacker.maxHp || 250)) {
      const heal = Math.max(1, Math.round(damage * attacker.lifesteal));
      attacker.hp = Math.min(attacker.maxHp || 250, attacker.hp + heal);
      attacker.hpSeq = (attacker.hpSeq || 0) + 1;
      attacker.hpAt = now;
      socket.emit('self_state', { hp: attacker.hp, hpSeq: attacker.hpSeq, hpAt: attacker.hpAt });
    }

    if (swingId) target.lastHitSwingId = swingId;
    target.lastHitTime = now;
    applyPlayerDamage(target, damage);

    // Melee XP saldırgana, Defence XP hedefe
    awardCombatXp(attacker, 'melee', Math.max(6, Math.round(damage * 0.45)), { hitId: data.targetId });
    awardCombatXp(target, 'defence', Math.max(6, Math.round(damage * 0.55)), { from: attacker.name || 'Oyuncu' });

    // Knockback / Geri itme
    const hitAngle = Number.isFinite(Number(data.angle)) ? Number(data.angle) : Math.atan2((Number(target.y)||0) - (Number(attacker.y)||0), (Number(target.x)||0) - (Number(attacker.x)||0));
    const kbForce = isScythe ? 16 : 11;
    target.vx = (target.vx || 0) + Math.cos(hitAngle) * kbForce;
    target.vy = (target.vy || 0) + Math.sin(hitAngle) * kbForce;
    target.x += Math.cos(hitAngle) * (kbForce * 0.6);
    target.y += Math.sin(hitAngle) * (kbForce * 0.6);
    if (target.isBot) alertBotAttacked(target, attacker);
    io.to(data.targetId).emit('pvp_hit', { dmg: damage, fromName: attacker.name || 'Oyuncu', angle: hitAngle, kbForce });
    io.to(data.targetId).emit('self_state', { hp: target.hp, hpSeq: target.hpSeq, hpAt: target.hpAt });
    io.emit('players', { [data.targetId]: compactState(target) });
    socket.emit('pvp_confirm', { targetId: data.targetId, dmg: damage, targetName: target.name || 'Oyuncu' });
    if (target.hp <= 0) {
      // Necromancer kill heal
      if (attacker.itemStats?.helmet?.killHeal && (attacker.hp ?? 0) < (attacker.maxHp || 250)) {
        attacker.hp = Math.min(attacker.maxHp || 250, attacker.hp + attacker.itemStats.helmet.killHeal);
        socket.emit('self_state', { hp: attacker.hp });
      }
      onPlayerDeath(data.targetId);
      target.kills = target.kills || 0;
      attacker.kills = (attacker.kills || 0) + 1;
      attacker.score = (attacker.score || 0) + 150;
      socket.emit('self_state', {
        matchKills: Math.max(0, attacker.kills - (attacker.matchStartKills || 0)),
        sc: attacker.score
      });
      if (!attacker.isBot && !target.isBot) {
        recordServerQuestProgress(attacker, {
          pvpKills: 1,
          ...(BOUNTY_EVENT_ENABLED && currentBountyId && data.targetId === currentBountyId ? { kingKills: 1 } : {})
        });
      }
      if (BOUNTY_EVENT_ENABLED && currentBountyId && data.targetId === currentBountyId) {
        const bountyBonus = 300;
        attacker.gold = (attacker.gold || 0) + bountyBonus;
        attacker.score = (attacker.score || 0) + bountyBonus;
        socket.emit('bounty_kill_reward', { name: target.name || 'Oyuncu', bonus: bountyBonus });
        io.emit('bounty_killed_broadcast', { killer: attacker.name || 'Oyuncu', victim: target.name || 'Oyuncu', bonus: bountyBonus });
        currentBountyId = null;
        io.emit('bounty_update', { id: null });
      }
      io.to(data.targetId).emit('pvp_killed', { byName: attacker.name || 'Oyuncu' });
      io.emit('player_dead', { id: data.targetId });
      socket.emit('pvp_kill_confirm', { targetId: data.targetId, targetName: target.name || 'Oyuncu' });
      io.emit('pvp_kill_feed', { killer: attacker.name || 'Oyuncu', victim: target.name || 'Oyuncu', streak: attacker.kills });
      persistPlayerScore(attacker);
    }
  });

  socket.on('arrow_hit', (data = {}) => {
    if (socketEventRateLimited(socket, 'arrow_hit')) return;
    if (!pvpAllowed()) return;
    const attacker = players.get(socket.id);
    const target = players.get(data.targetId);
    if (!attacker || !target || attacker.hp <= 0 || target.hp <= 0) return;

    let sourceX = Number(attacker.x) || 0;
    let sourceY = Number(attacker.y) || 0;
    let validationRange = 780;
    if (data.buildingId) {
      const turret = buildings.get(String(data.buildingId || ''));
      if (!turret || Number(turret.type) !== 7 || (turret.hp ?? 0) <= 0 || turret.ownerId !== socket.id) return;
      sourceX = Number(turret.x) || 0;
      sourceY = Number(turret.y) || 0;
      validationRange = turretRange(turret) + (Number(target.radius) || 35);
    }

    if (!validateCombatState({ ...attacker, x: sourceX, y: sourceY }, target, { allowTrapHit: true, rangeLimit: validationRange, damage: 1 })) return;
    if (attacker.roomId && target.roomId && attacker.roomId !== target.roomId && !nearbyRoomIds(attacker.x || 0, attacker.y || 0, validationRange).has(target.roomId)) return;
    const distance = Math.hypot((Number(target.x) || 0) - sourceX, (Number(target.y) || 0) - sourceY);
    if (distance > validationRange) return;
    const now = Date.now();
    if (now - (attacker.lastArrowAt || 0) < 140) return;
    attacker.lastArrowAt = now;
    const tier = Math.max(0, Math.min(5, Number(attacker.axeTier ?? attacker.swordTier) || 0));
    let damage = Math.min(140, Math.max(1, Math.round((14 + tier * 6) * (Number(attacker.damageMultiplier) || 1))));
    if (data.buildingId) {
      const turret = buildings.get(String(data.buildingId || ''));
      if (turret && Number(turret.type) === 7) {
        damage = turretProjectileDamage(turret);
      }
    }
    damage = limitHitDamage(target, damage);
    applyPlayerDamage(target, damage);
    if (target.isBot) alertBotAttacked(target, attacker);
    io.to(data.targetId).emit('pvp_hit', { dmg: damage, fromName: attacker.name || 'Oyuncu' });
    io.to(data.targetId).emit('self_state', { hp: target.hp, hpSeq: target.hpSeq, hpAt: target.hpAt });
    io.emit('players', { [data.targetId]: compactState(target) });
    socket.emit('pvp_confirm', { targetId: data.targetId, dmg: damage, targetName: target.name || 'Oyuncu' });
    if (target.hp <= 0) {
      onPlayerDeath(data.targetId);
      target.kills = target.kills || 0;
      attacker.kills = (attacker.kills || 0) + 1;
      attacker.score = (attacker.score || 0) + 150;
      socket.emit('self_state', {
        matchKills: Math.max(0, attacker.kills - (attacker.matchStartKills || 0)),
        sc: attacker.score
      });
      if (!attacker.isBot && !target.isBot) {
        recordServerQuestProgress(attacker, {
          pvpKills: 1,
          ...(BOUNTY_EVENT_ENABLED && currentBountyId && data.targetId === currentBountyId ? { kingKills: 1 } : {})
        });
      }
      if (BOUNTY_EVENT_ENABLED && currentBountyId && data.targetId === currentBountyId) {
        const bountyBonus = 300;
        attacker.gold = (attacker.gold || 0) + bountyBonus;
        attacker.score = (attacker.score || 0) + bountyBonus;
        socket.emit('bounty_kill_reward', { name: target.name || 'Oyuncu', bonus: bountyBonus });
        io.emit('bounty_killed_broadcast', { killer: attacker.name || 'Oyuncu', victim: target.name || 'Oyuncu', bonus: bountyBonus });
        currentBountyId = null;
        io.emit('bounty_update', { id: null });
      }
      io.to(data.targetId).emit('pvp_killed', { byName: attacker.name || 'Oyuncu' });
      io.emit('player_dead', { id: data.targetId });
      socket.emit('pvp_kill_confirm', { targetId: data.targetId, targetName: target.name || 'Oyuncu' });
      io.emit('pvp_kill_feed', { killer: attacker.name || 'Oyuncu', victim: target.name || 'Oyuncu', streak: attacker.kills });
      persistPlayerScore(attacker);
    }
  });

  socket.on('spike_hit', (data = {}) => {
    if (socketEventRateLimited(socket, 'spike_hit')) return;
    if (!pvpAllowed()) return;
    const attacker = players.get(socket.id);
    const target = players.get(data.targetId);
    const spikeId = String(data.bId || data.buildingId || '');
    const spike = buildings.get(spikeId);
    if (!attacker || !target || (target.hp ?? 0) <= 0 || !spike || Number(spike.type) !== 3 || (spike.hp ?? 0) <= 0) return;
    // Allow either the spike owner OR the victim to notify server.
    // Validate against the actual spike building position so remote hits still work.
    if (spike.ownerId !== socket.id && target.id !== socket.id) return;
    const sourceX = Number.isFinite(Number(data.sourceX)) ? Number(data.sourceX) : Number(spike.x) || 0;
    const sourceY = Number.isFinite(Number(data.sourceY)) ? Number(data.sourceY) : Number(spike.y) || 0;
    if (attacker.roomId && target.roomId && attacker.roomId !== target.roomId && !nearbyRoomIds(attacker.x || 0, attacker.y || 0, 800).has(target.roomId)) return;
    const targetRad = Number(target.radius) || 35;
    const spikeRad = Number(spike.radius) || 34;
    const maxContactDist = targetRad + spikeRad + 24;
    const dist = Math.hypot((Number(target.x) || 0) - sourceX, (Number(target.y) || 0) - sourceY);
    if (dist > maxContactDist) return;
    applySpikeDamageToTarget(target, spike, Date.now());
  });

  socket.on('trap_touch', (data = {}) => {
    if (socketEventRateLimited(socket, 'trap_touch')) return;
    if (data.victimId && String(data.victimId) !== socket.id) return;
    const target = players.get(data.victimId);
    const building = buildings.get(String(data.buildingId || ''));
    if (!target || target.hp <= 0) return;
    if (!building || building.type !== 6 || (building.hp ?? 0) <= 0) return;
    if (building.ownerId === data.victimId) return;
    if (building.ownerId !== socket.id && data.victimId !== socket.id) return;
    if (!validateTrapCapture(socket ? players.get(socket.id) : null, target, building)) return;
    capturePlayerInSpecificTrap(target, building);
  });

  socket.on('mob_trap_hit', (data = {}) => {
    if (socketEventRateLimited(socket, 'mob_trap_hit')) return;
    const mob = mobs.get(String(data.mobId || ''));
    if (!mob || mob.hp <= 0) return;
    const b = buildings.get(String(data.buildingId || ''));
    const owner = b ? players.get(b.ownerId) : null;
    if (!b || b.type !== 6 || (b.hp ?? 0) <= 0 || !owner || owner.hp <= 0 || owner.id !== socket.id) return;
    const now = Date.now();
    if (mob.trappedBy || (mob.trapIgnoreBuildingId === b.id && now < (mob.trapIgnoreUntil || 0))) return;
    const dx = mob.x - b.x, dy = mob.y - b.y;
    const triggerRadius = trapCaptureRadius(b, mob.radius || 36);
    if (dx * dx + dy * dy > triggerRadius * triggerRadius) return;
    if (b && (b.hp ?? 100) > 0) {
      mob.trappedBy = b.id;
      mob.trappedUntil = now + MOB_TRAP_HOLD_MS;
      mob.trappedX = mob.x;
      mob.trappedY = mob.y;
      mob.vx = 0;
      mob.vy = 0;
      mob.state = 'walk';
      mob.nextAttackAt = now + MOB_TRAP_HOLD_MS;
      io.emit('mob_trapped', { mobId: mob.id, buildingId: b.id, x: mob.x, y: mob.y });
    }
  });

  socket.on('trap_owner_push', (data = {}) => {
    if (socketEventRateLimited(socket, 'trap_owner_push')) return;
    const owner = players.get(socket.id);
    const target = players.get(data.victimId);
    const dx = Number(data.dx);
    const dy = Number(data.dy);
    if (!Number.isFinite(dx) || !Number.isFinite(dy)) return;
    pushTrappedVictim(owner, target, dx, dy, data.step);
  });

  socket.on('train_board', () => {
    const player = players.get(socket.id);
    if (player) player.onTrain = true;
    socket.emit('train_boarded', { x: player?.x || 0, y: player?.y || 0 });
    relayToOthers(socket, 'train_boarded', { id: socket.id });
  });

  socket.on('train_exit', () => {
    const player = players.get(socket.id);
    if (player) player.onTrain = false;
    socket.emit('train_exited');
    relayToOthers(socket, 'train_exited', { id: socket.id });
  });

  socket.on('res_hit', (data = {}) => {
    if (socketEventRateLimited(socket, 'res_hit')) return;
    const player = players.get(socket.id);
    const idx = Number(data.idx);
    const resource = Number.isInteger(idx) ? serverResources[idx] : null;
    if (!player || !resource || resource.destroyed || player.hp <= 0) return;
    const swingId = Number(data.swingId);
    const now = Date.now();
    if (!Number.isFinite(swingId) || swingId !== player.lastSwingId || now - (player.lastSwingAt || 0) > 350 || !player.isAttacking) return;
    if (player.weapon !== 1 && player.weapon !== 2) return;
    const previousSwing = resource.lastHitSwingBy.get(socket.id);
    if (previousSwing === swingId) return;
    const distance = Math.hypot((Number(player.x) || 0) - resource.x, (Number(player.y) || 0) - resource.y);
    const weapon = Number(player.weapon) === 2 ? 2 : 1;
    const attackRange = weapon === 2 ? 140 : 128;
    if (distance > attackRange + resource.radius) return;
    const attackAngle = Number(player.lastAttackAngle);
    let angleDiff = Math.abs(Math.atan2(resource.y - player.y, resource.x - player.x) - attackAngle);
    if (angleDiff > Math.PI) angleDiff = 2 * Math.PI - angleDiff;
    const attackSpread = weapon === 2 ? Math.PI / 3.25 : Math.PI / 2.57;
    if (!Number.isFinite(attackAngle) || angleDiff > attackSpread) return;
    if (now - (resource.lastHitBy.get(socket.id) || 0) < 80) return;
    resource.lastHitBy.set(socket.id, now);
    resource.lastHitSwingBy.set(socket.id, swingId);
    const tier = Math.max(0, Math.min(11, Number(weapon === 2 ? player.swordTier : player.axeTier) || 0));
    const resourceYield = ResourceYield.calculateResourceYield(resource.type, weapon === 1 ? 'axe' : 'sword', tier);
    const damage = Math.round((weapon === 2 ? 30 : 22) * [1, 1.5, 2.2, 3.5, 5, 8, 10, 13, 16, 19, 23, 28][tier]);
    // Natural resources never break / deplete: keep HP full so players can farm infinitely
    resource.hp = resource.maxHp || 500;
    resource.destroyed = false;
    const resPayload = { idx, hp: resource.hp, maxHp: resource.maxHp, shake: true, destroyed: false };
    socket.emit('res_sync', resPayload);
    broadcastPlayerEventNear(player, 'res_sync', resPayload);

    // Per-hit harvesting rewards
    let gainedWood = 0, gainedStone = 0, gainedGold = 0, gainedApples = 0, gainedHp = 0, gainedXp = 0, gainedScore = 0;
    let gainedDiamond = 0, gainedAmethyst = 0, gainedRedite = 0;
    switch (resource.type) {
      case 'wood':
        gainedWood = resourceYield.wood;
        if (Math.random() < 0.28) gainedApples = 1;
        gainedScore = Math.round(gainedWood * 0.5);
        break;
      case 'stone':
        gainedStone = resourceYield.stone;
        gainedScore = Math.round(gainedStone * 0.6);
        break;
      case 'gold':
        gainedGold = resourceYield.gold;
        gainedStone = resourceYield.stone;
        gainedScore = Math.round(gainedGold * 2);
        break;
      case 'apple':
        gainedWood = resourceYield.wood;
        gainedApples = 1 + (Math.random() < 0.4 ? 1 : 0);
        gainedScore = 15;
        break;
      case 'bush':
        gainedWood = resourceYield.wood;
        if (Math.random() < 0.65) gainedApples = 1;
        gainedScore = 8;
        break;
      case 'mushroom':
        gainedGold = resourceYield.gold;
        gainedHp = 35;
        player.hp = Math.min(player.maxHp ?? 250, (player.hp ?? 0) + gainedHp);
        gainedScore = 12;
        break;
      case 'crystal':
        gainedXp = 45;
        gainedScore = 30;
        break;
      case 'hive':
        gainedGold = resourceYield.gold;
        gainedScore = 20;
        break;
      case 'diamond':
        gainedDiamond = resourceYield.diamond;
        gainedXp = 25;
        gainedScore = 30;
        awardCombatXp(player, 'melee', 8, { targetName: '💎 Elmas' });
        break;
      case 'amethyst':
        gainedAmethyst = resourceYield.amethyst;
        gainedXp = 50;
        gainedScore = 60;
        awardCombatXp(player, 'melee', 16, { targetName: '🔮 Ametist' });
        break;
      case 'redite':
        gainedRedite = resourceYield.redite;
        gainedXp = 100;
        gainedScore = 150;
        awardCombatXp(player, 'melee', 35, { targetName: '👑 Kadim Redite' });
        break;
      default:
        gainedWood = resourceYield.wood;
        break;
    }

    player.wood = (player.wood || 0) + gainedWood;
    player.stone = (player.stone || 0) + gainedStone;
    player.gold = (player.gold || 0) + gainedGold;
    player.apples = (player.apples || 0) + gainedApples;
    player.diamond = (player.diamond || 0) + gainedDiamond;
    player.amethyst = (player.amethyst || 0) + gainedAmethyst;
    player.redite = (player.redite || 0) + gainedRedite;
    player.score = (player.score || 0) + gainedScore;
    player.xp = (player.xp || 0) + gainedXp;
    recordServerQuestProgress(player, { wood: gainedWood, stone: gainedStone, gold: gainedGold });

    if (player._authUser && gainedGold > 0) {
      player._authUser.coins = (player._authUser.coins || 0) + gainedGold;
      player._authUser.gold = player._authUser.coins;
      player._authUser.score = Math.max(player._authUser.score || 0, player.score);
    }
    if (player._authUser && gainedXp > 0) {
      player._authUser.xp = (player._authUser.xp || 0) + gainedXp;
      player._authUser.rankId = rankInfo(player._authUser.xp).rankId;
    }
    if (gainedXp > 0) player.rankId = rankInfo(player.xp).rankId;

    socket.emit('res_reward', {
      wood: player.wood,
      stone: player.stone,
      gold: player.gold,
      apples: player.apples,
      diamond: player.diamond,
      amethyst: player.amethyst,
      redite: player.redite,
      score: player.score,
      xp: player.xp,
      gainedWood,
      gainedStone,
      gainedGold,
      gainedApples,
      gainedDiamond,
      gainedAmethyst,
      gainedRedite,
      gainedHp,
      gainedXp,
      gainedScore,
      hitType: resource.type,
      resX: resource.x,
      resY: resource.y,
      destroyed: resource.hp <= 0
    });
  });

  // ── USTA DEMİRCİ ATÖLYESİ (MASTER BLACKSMITH) RECIPES & CRAFTING ──────────
  const SERVER_BLACKSMITH_RECIPES = {
    axe: [
      { tier: 0, name: 'Tahta Balta', level: 1, wood: 0, stone: 0, gold: 0, diamond: 0, amethyst: 0, redite: 0 },
      { tier: 1, name: 'Taş Balta', level: 3, wood: 180, stone: 150, gold: 0, diamond: 0, amethyst: 0, redite: 0 },
      { tier: 2, name: 'Altın Balta', level: 6, wood: 450, stone: 380, gold: 350, diamond: 0, amethyst: 0, redite: 0 },
      { tier: 3, name: 'Elmas Balta', level: 10, wood: 900, stone: 750, gold: 850, diamond: 180, amethyst: 0, redite: 0 },
      { tier: 4, name: 'Ametist Balta', level: 16, wood: 1600, stone: 1400, gold: 2200, diamond: 0, amethyst: 350, redite: 0 },
      { tier: 5, name: 'Kadim Redite Balta', level: 22, wood: 2800, stone: 2500, gold: 4800, diamond: 0, amethyst: 0, redite: 600 },
      { tier: 6, name: 'Nihai Gökkuşağı Balta', level: 30, wood: 4500, stone: 4000, gold: 9500, diamond: 500, amethyst: 500, redite: 400 },
      { tier: 7, name: 'Yıldız Çeliği Balta', level: 38, wood: 6500, stone: 6000, gold: 16000, diamond: 800, amethyst: 0, redite: 700 },
      { tier: 8, name: 'Nebula Baltası', level: 45, wood: 9000, stone: 8500, gold: 25000, diamond: 0, amethyst: 1200, redite: 1000 },
      { tier: 9, name: 'Kara Yıldız Baltası', level: 52, wood: 12000, stone: 11000, gold: 38000, diamond: 0, amethyst: 0, redite: 1800 },
      { tier: 10, name: 'Tutulma Baltası', level: 60, wood: 16000, stone: 15000, gold: 55000, diamond: 0, amethyst: 0, redite: 2500 },
      { tier: 11, name: 'Yaratılış Baltası', level: 70, wood: 25000, stone: 25000, gold: 90000, diamond: 0, amethyst: 0, redite: 4000 }
    ],
    sword: [
      { tier: 0, name: 'Tahta Kılıç', level: 1, wood: 0, stone: 0, gold: 0, diamond: 0, amethyst: 0, redite: 0 },
      { tier: 1, name: 'Taş Kılıç', level: 3, wood: 140, stone: 200, gold: 0, diamond: 0, amethyst: 0, redite: 0 },
      { tier: 2, name: 'Altın Kılıç', level: 6, wood: 350, stone: 500, gold: 400, diamond: 0, amethyst: 0, redite: 0 },
      { tier: 3, name: 'Elmas Kılıç', level: 10, wood: 700, stone: 950, gold: 1100, diamond: 220, amethyst: 0, redite: 0 },
      { tier: 4, name: 'Ametist Kılıç', level: 16, wood: 1200, stone: 1800, gold: 2600, diamond: 0, amethyst: 420, redite: 0 },
      { tier: 5, name: 'Kadim Redite Kılıç', level: 22, wood: 2200, stone: 3200, gold: 5500, diamond: 0, amethyst: 0, redite: 750 },
      { tier: 6, name: 'Nihai Gökkuşağı Kılıç', level: 30, wood: 3800, stone: 5000, gold: 11000, diamond: 600, amethyst: 600, redite: 500 },
      { tier: 7, name: 'Yıldız Çeliği Kılıç', level: 38, wood: 5000, stone: 7500, gold: 18000, diamond: 950, amethyst: 0, redite: 850 },
      { tier: 8, name: 'Nebula Kılıcı', level: 45, wood: 7500, stone: 10500, gold: 28000, diamond: 0, amethyst: 1400, redite: 1200 },
      { tier: 9, name: 'Kara Yıldız Kılıcı', level: 52, wood: 10000, stone: 14000, gold: 42000, diamond: 0, amethyst: 0, redite: 2000 },
      { tier: 10, name: 'Tutulma Kılıcı', level: 60, wood: 14000, stone: 19000, gold: 60000, diamond: 0, amethyst: 0, redite: 2800 },
      { tier: 11, name: 'Yaratılış Kılıcı', level: 70, wood: 22000, stone: 30000, gold: 95000, diamond: 0, amethyst: 0, redite: 4500 }
    ],
    helmet: [
      { id: 'helmet_cehennem', name: 'Cehennem Efendisi', level: 12, wood: 0, stone: 600, gold: 1800, diamond: 150, amethyst: 80, redite: 0 },
      { id: 'helmet_cyber', name: 'Cyber Mecha Prime', level: 18, wood: 0, stone: 1100, gold: 3200, diamond: 260, amethyst: 180, redite: 0 },
      { id: 'helmet_ejderha', name: 'Ejderha Barbar', level: 25, wood: 0, stone: 1700, gold: 5200, diamond: 0, amethyst: 450, redite: 160 },
      { id: 'helmet_druid', name: 'Kadim Druid Kralı', level: 32, wood: 2500, stone: 2200, gold: 7500, diamond: 0, amethyst: 0, redite: 350 },
      { id: 'helmet_necromancer', name: 'Ruh Necromancer', level: 40, wood: 0, stone: 3500, gold: 12000, diamond: 0, amethyst: 800, redite: 650 }
    ]
  };
  for (const recipes of Object.values(SERVER_BLACKSMITH_RECIPES)) {
    for (const recipe of recipes) {
      for (const material of ['wood', 'stone', 'gold', 'diamond', 'amethyst', 'redite']) {
        recipe[material] *= 2;
      }
    }
  }

  socket.on('scythe_purchase', (data = {}) => {
    if (socketEventRateLimited(socket, 'scythe_purchase')) return;
    const player = players.get(socket.id);
    const id = String(data.id || '');
    const cost = SCYTHE_SHOP_PRICES[id];
    const tier = Number(id.match(/^scythe_tier_(\d+)$/)?.[1]);
    if (!player || player.hp <= 0) {
      return socket.emit('scythe_action_res', { ok: false, error: 'Tırpan satın almak için hayatta olmalısınız.' });
    }
    if (!cost || !getScytheItemStats(id) || !Number.isInteger(tier)) {
      return socket.emit('scythe_action_res', { ok: false, error: 'Geçersiz tırpan.' });
    }
    if ((player.ownedScythes || []).includes(id)) {
      return socket.emit('scythe_action_res', { ok: false, error: 'Bu tırpana zaten sahipsiniz.' });
    }
    if ((player.gold || 0) < cost && (player.score || 0) < cost) {
      return socket.emit('scythe_action_res', {
        ok: false, error: `Yetersiz altın veya skor! Gereken: ${cost}`,
        gold: player.gold || 0, score: player.score || 0, ownedScythes: player.ownedScythes || []
      });
    }
    if (!player.ownedScythes) player.ownedScythes = [];
    player.ownedScythes.push(id);
    if ((player.gold || 0) >= cost) player.gold -= cost;
    else player.score -= cost;
    player._preScytheSwordTier = player.scytheId ? player._preScytheSwordTier : player.swordTier;
    player.scytheId = id;
    player.swordSkin = id;
    player.swordTier = tier;
    applyLoadoutStats(player);
    persistPlayerEquipment(player);
    player.hpSeq = (player.hpSeq || 0) + 1;
    player.hpAt = Date.now();
    socket.emit('self_state', {
      hp: player.hp, maxHp: player.maxHp, baseMaxHp: player._loadoutBaseMaxHp,
      hpSeq: player.hpSeq, hpAt: player.hpAt, g: player.gold, sc: player.score
    });
    broadcastPlayerEventNear(player, 'gear_update', {
      id: socket.id, axeTier: player.axeTier, swordTier: player.swordTier,
      helmetSkin: player.helmetSkin, scytheId: player.scytheId
    });
    broadcastPlayerEventNear(player, 'equipment_update', {
      id: socket.id, scytheId: player.scytheId, swordSkin: player.swordSkin,
      swordTier: player.swordTier, helmetSkin: player.helmetSkin
    });
    socket.emit('scythe_action_res', {
      ok: true, id, ownedScythes: player.ownedScythes, gold: player.gold, score: player.score
    });
  });

  socket.on('scythe_equip', (data = {}) => {
    if (socketEventRateLimited(socket, 'scythe_equip')) return;
    const player = players.get(socket.id);
    const id = String(data.id || '');
    const tier = Number(id.match(/^scythe_tier_(\d+)$/)?.[1]);
    if (!player || player.hp <= 0) {
      return socket.emit('scythe_action_res', { ok: false, error: 'Tırpan kuşanmak için hayatta olmalısınız.' });
    }
    if (!(player.ownedScythes || []).includes(id) || !getScytheItemStats(id) || !Number.isInteger(tier)) {
      return socket.emit('scythe_action_res', {
        ok: false, error: 'Bu tırpana sahip değilsiniz.',
        gold: player.gold || 0, score: player.score || 0, ownedScythes: player.ownedScythes || []
      });
    }
    player._preScytheSwordTier = player.scytheId ? player._preScytheSwordTier : player.swordTier;
    player.scytheId = id;
    player.swordSkin = id;
    player.swordTier = tier;
    applyLoadoutStats(player);
    persistPlayerEquipment(player);
    player.hpSeq = (player.hpSeq || 0) + 1;
    player.hpAt = Date.now();
    socket.emit('self_state', {
      hp: player.hp, maxHp: player.maxHp, baseMaxHp: player._loadoutBaseMaxHp,
      hpSeq: player.hpSeq, hpAt: player.hpAt
    });
    broadcastPlayerEventNear(player, 'gear_update', {
      id: socket.id, axeTier: player.axeTier, swordTier: player.swordTier,
      helmetSkin: player.helmetSkin, scytheId: player.scytheId
    });
    broadcastPlayerEventNear(player, 'equipment_update', {
      id: socket.id, scytheId: player.scytheId, swordSkin: player.swordSkin,
      swordTier: player.swordTier, helmetSkin: player.helmetSkin
    });
    socket.emit('scythe_action_res', {
      ok: true, id, ownedScythes: player.ownedScythes || [],
      gold: player.gold || 0, score: player.score || 0
    });
  });

  socket.on('craft_blacksmith_item', (data = {}) => {
    if (socketEventRateLimited(socket, 'craft_blacksmith_item')) return;
    const player = players.get(socket.id);
    if (!player || player.hp <= 0) {
      return socket.emit('blacksmith_craft_res', { ok: false, error: 'Üretim için hayatta olmalısınız.' });
    }
    const craftFailure = error => {
      socket.emit('self_state', {
        sc: player.score || 0, g: player.gold || 0,
        wood: player.wood || 0, stone: player.stone || 0, apples: player.apples || 0,
        diamond: player.diamond || 0, amethyst: player.amethyst || 0, redite: player.redite || 0
      });
      socket.emit('blacksmith_craft_res', { ok: false, error });
    };
    const { category, targetIndex, targetId } = data;
    const recipeList = SERVER_BLACKSMITH_RECIPES[category];
    if (!recipeList) return craftFailure('Geçersiz kategori.');

    let recipe = null;
    if (category === 'helmet') {
      recipe = recipeList.find(r => r.id === targetId);
    } else {
      recipe = recipeList.find(r => r.tier === Number(targetIndex));
    }
    if (!recipe) return craftFailure('Tarif bulunamadı.');
    const ownedList = category === 'axe' ? player.ownedAxes : category === 'sword' ? player.ownedSwords : player.ownedHelmets;
    const ownedValue = category === 'helmet' ? recipe.id : recipe.tier;
    if ((ownedList || []).includes(ownedValue)) {
      return craftFailure('Bu eşyaya zaten sahipsiniz.');
    }

    // Level check
    const pLevel = calculatePlayerLevel(player);
    if (pLevel < recipe.level) {
      return craftFailure(`Seviye yetersiz! Gerekli seviye: ${recipe.level} (Mevcut: ${pLevel})`);
    }

    // Material checks
    if ((player.wood || 0) < recipe.wood) return craftFailure(`Yetersiz Odun! (${player.wood || 0}/${recipe.wood})`);
    if ((player.stone || 0) < recipe.stone) return craftFailure(`Yetersiz Taş! (${player.stone || 0}/${recipe.stone})`);
    if ((player.gold || 0) < recipe.gold) return craftFailure(`Yetersiz Altın! (${player.gold || 0}/${recipe.gold})`);
    if ((player.diamond || 0) < recipe.diamond) return craftFailure(`Yetersiz Elmas! (${player.diamond || 0}/${recipe.diamond})`);
    if ((player.amethyst || 0) < recipe.amethyst) return craftFailure(`Yetersiz Ametist! (${player.amethyst || 0}/${recipe.amethyst})`);
    if ((player.redite || 0) < recipe.redite) return craftFailure(`Yetersiz Redite! (${player.redite || 0}/${recipe.redite})`);

    // Deduct materials
    player.wood = Math.max(0, (player.wood || 0) - recipe.wood);
    player.stone = Math.max(0, (player.stone || 0) - recipe.stone);
    player.gold = Math.max(0, (player.gold || 0) - recipe.gold);
    player.diamond = Math.max(0, (player.diamond || 0) - recipe.diamond);
    player.amethyst = Math.max(0, (player.amethyst || 0) - recipe.amethyst);
    player.redite = Math.max(0, (player.redite || 0) - recipe.redite);

    // Apply upgrade
    if (category === 'axe') {
      player.axeTier = recipe.tier;
      if (!player.ownedAxes) player.ownedAxes = [0];
      if (!player.ownedAxes.includes(recipe.tier)) player.ownedAxes.push(recipe.tier);
    } else if (category === 'sword') {
      player.swordTier = recipe.tier;
      player.scytheId = null;
      player._preScytheSwordTier = null;
      if (String(player.swordSkin || '').startsWith('scythe_')) player.swordSkin = null;
      if (!player.ownedSwords) player.ownedSwords = [0];
      if (!player.ownedSwords.includes(recipe.tier)) player.ownedSwords.push(recipe.tier);
      applyLoadoutStats(player);
    } else if (category === 'helmet') {
      player.helmetSkin = recipe.id;
      if (!player.ownedHelmets) player.ownedHelmets = [];
      if (!player.ownedHelmets.includes(recipe.id)) player.ownedHelmets.push(recipe.id);
      applyLoadoutStats(player);
      player.hpSeq = (player.hpSeq || 0) + 1;
      player.hpAt = Date.now();
      const helmetItemStats = player.helmetSkin ? getHelmetItemStats(player.helmetSkin) : null;
      socket.emit('self_state', {
        hp: player.hp,
        maxHp: player.maxHp,
        baseMaxHp: player._loadoutBaseMaxHp,
        hpSeq: player.hpSeq,
        hpAt: player.hpAt,
        speedMultiplier: player.speedMultiplier,
        damageMultiplier: player.damageMultiplier,
        armorMultiplier: player.armorMultiplier,
        hpTheme: helmetItemStats?.hpTheme || ''
      });
    }

    persistPlayerEquipment(player);

    // Success response
    socket.emit('blacksmith_craft_res', {
      ok: true,
      category,
      tier: recipe.tier,
      id: recipe.id,
      name: recipe.name,
      ownedAxes: player.ownedAxes || [0],
      ownedSwords: player.ownedSwords || [0],
      ownedHelmets: player.ownedHelmets || [],
      materials: {
        wood: player.wood,
        stone: player.stone,
        gold: player.gold,
        diamond: player.diamond,
        amethyst: player.amethyst,
        redite: player.redite
      }
    });

    // Broadcast gear update to nearby players
    const updatePayload = {
      id: socket.id,
      axeTier: player.axeTier,
      swordTier: player.swordTier,
      helmetSkin: player.helmetSkin
    };
    broadcastPlayerEventNear(player, 'gear_update', updatePayload);
  });

  socket.on('equip_blacksmith_item', (data = {}) => {
    if (socketEventRateLimited(socket, 'equip_blacksmith_item')) return;
    const player = players.get(socket.id);
    if (!player || player.hp <= 0) {
      return socket.emit('blacksmith_equip_res', { ok: false, error: 'Eşya kuşanmak için hayatta olmalısınız.' });
    }
    const { category, tier, id } = data;
    if (category === 'axe' && Number.isInteger(tier) && (player.ownedAxes || [0]).includes(tier)) {
      player.axeTier = tier;
    } else if (category === 'sword' && Number.isInteger(tier) && (player.ownedSwords || [0]).includes(tier)) {
      player.swordTier = tier;
      player.scytheId = null;
      player._preScytheSwordTier = null;
      if (String(player.swordSkin || '').startsWith('scythe_')) player.swordSkin = null;
      applyLoadoutStats(player);
    } else if (category === 'helmet') {
      const helmetId = typeof id === 'string' ? id.trim() : '';
      if (helmetId && (!(player.ownedHelmets || []).includes(helmetId) ||
          !SERVER_BLACKSMITH_RECIPES.helmet.some(recipe => recipe.id === helmetId))) {
        return socket.emit('blacksmith_equip_res', { ok: false, error: 'Bu kaska sahip değilsiniz.' });
      }
      player.helmetSkin = helmetId || null;
      applyLoadoutStats(player);
      player.hpSeq = (player.hpSeq || 0) + 1;
      player.hpAt = Date.now();
      const helmetItemStats = player.helmetSkin ? getHelmetItemStats(player.helmetSkin) : null;
      socket.emit('self_state', {
        hp: player.hp,
        maxHp: player.maxHp,
        baseMaxHp: player._loadoutBaseMaxHp,
        hpSeq: player.hpSeq || 0,
        hpAt: player.hpAt || Date.now(),
        speedMultiplier: player.speedMultiplier,
        damageMultiplier: player.damageMultiplier,
        armorMultiplier: player.armorMultiplier,
        hpTheme: helmetItemStats?.hpTheme || ''
      });
    } else {
      return socket.emit('blacksmith_equip_res', { ok: false, error: 'Bu eşyaya sahip değilsiniz.' });
    }
    persistPlayerEquipment(player);
    broadcastPlayerEventNear(player, 'gear_update', {
      id: socket.id,
      axeTier: player.axeTier,
      swordTier: player.swordTier,
      helmetSkin: player.helmetSkin
    });
    socket.emit('blacksmith_equip_res', {
      ok: true, category, tier: player[category === 'axe' ? 'axeTier' : 'swordTier'],
      id: category === 'helmet' ? player.helmetSkin : undefined
    });
  });

  socket.on('chat', (data = {}) => {
    if (socketEventRateLimited(socket, 'chat')) return;
    const now = Date.now();
    if (now - (socket._lastChatAt || 0) < 500) return;
    socket._lastChatAt = now;
    const cleanMsg = String(data.msg || '').replace(/[\u0000-\u001f\u007f]/g, '').trim().slice(0, 120);
    if (!cleanMsg) return;
    const player = players.get(socket.id);
    const message = {
      name: player?.name || 'Oyuncu',
      level: player ? calculatePlayerLevel(player) : 1,
      msg: cleanMsg,
      id: socket.id,
      at: now
    };
    io.emit('chat', message);
  });
  socket.on('quick_chat', (data = {}) => {
    if (socketEventRateLimited(socket, 'quick_chat')) return;
    const player = players.get(socket.id);
    const idx = Number(data.idx);
    if (!player || !Number.isInteger(idx) || idx < 0 || idx >= 8) return;
    io.emit('quick_chat', {
      id: socket.id,
      name: player.name || 'Oyuncu',
      level: calculatePlayerLevel(player),
      idx,
      x: Number(player.x) || 0,
      y: Number(player.y) || 0,
      at: Date.now()
    });
  });
  socket.on('ping_req', (data) => socket.emit('pong_res', typeof data === 'object' && data ? data : { t: data }));
  socket.on('eat_apple', () => {
    if (socketEventRateLimited(socket, 'eat_apple')) return;
    const player = players.get(socket.id);
    if (player && player.hp > 0 && player.apples > 0 && player.hp < (player.maxHp ?? 250)) {
      player.apples--;
      player.hp = Math.min(player.maxHp ?? 250, (player.hp ?? 0) + 30);
    }
    if (player) {
      player.level = calculatePlayerLevel(player);
      applyLoadoutStats(player);
      player.hpSeq = (player.hpSeq || 0) + 1;
      player.hpAt = Date.now();
    }
    socket.emit('self_state', {
      hp: player?.hp ?? 250, maxHp: player?.maxHp ?? 250,
      baseMaxHp: player?._loadoutBaseMaxHp,
      hpSeq: player?.hpSeq || 0, hpAt: player?.hpAt || Date.now(),
      apples: player?.apples || 0
    });
  });

  socket.on('sync_combat_stats', () => {
    if (socketEventRateLimited(socket, 'sync_combat_stats')) return;
    const player = players.get(socket.id);
    if (!player) return;
    player.level = calculatePlayerLevel(player);
    applyLoadoutStats(player);
    player.hpSeq = (player.hpSeq || 0) + 1;
    player.hpAt = Date.now();
    socket.emit('combat_stats_state', {
      meleeLevel: Math.max(1, Number(player.meleeLevel) || 1),
      meleeXp: Math.max(0, Number(player.meleeXp) || 0),
      defenceLevel: Math.max(1, Number(player.defenceLevel) || 1),
      defenceXp: Math.max(0, Number(player.defenceXp) || 0)
    });
    socket.emit('self_state', {
      hp: player.hp, maxHp: player.maxHp, baseMaxHp: player._loadoutBaseMaxHp,
      hpSeq: player.hpSeq, hpAt: player.hpAt
    });
  });

  socket.on('interact_npc', (data = {}) => {
    const player = players.get(socket.id);
    if (!player) return;
    const px = Number(player.x) || 0;
    const py = Number(player.y) || 0;
    
    // Check which NPC is nearby
    for (const npc of VILLAGE_NPCS) {
      const dist = Math.hypot(px - npc.x, py - npc.y);
      if (dist < npc.rad) {
        // Player is near this NPC - send back which one
        socket.emit('npc_interact', { npc: npc.name, title: npc.title });
        return;
      }
    }
  });

  socket.on('mob_hit_req', (data = {}) => {
    if (socketEventRateLimited(socket, 'mob_hit_req')) return;
    const now = Date.now();
    const mobId = String(data.mobId || '');
    const mob = mobs.get(mobId);
    if (!mob || mob.hp <= 0) return;
    const attacker = players.get(socket.id);
    if (!attacker || (attacker.hp ?? 0) <= 0 || attacker._dead) return;
    let sourceX = Number(attacker.x) || 0;
    let sourceY = Number(attacker.y) || 0;
    const isScythe = Number(attacker.weapon) === 2 && Boolean(attacker.scytheId || (attacker.swordSkin && String(attacker.swordSkin).startsWith('scythe_')));
    let range = isScythe ? 185 : 155;
    let turret = null;
    if (data.buildingId) {
      turret = buildings.get(String(data.buildingId || ''));
      if (!turret || Number(turret.type) !== 7 || (turret.hp ?? 0) <= 0 || turret.ownerId !== socket.id) return;
      sourceX = Number(turret.x) || 0;
      sourceY = Number(turret.y) || 0;
      range = turretRange(turret);
    }
    // The client renders a short interpolation behind the authoritative mob.
    // Compensate only for the attacker's recent state age, with a strict cap.
    const stateAgeMs = Math.max(0, Math.min(250, now - (Number(attacker.stateAt) || now)));
    const lagScale = stateAgeMs / 100;
    const validationMobX = mob.x + (mob.vx || 0) * lagScale;
    const validationMobY = mob.y + (mob.vy || 0) * lagScale;
    const distance = Math.hypot(sourceX - validationMobX, sourceY - validationMobY);
    const rangeSlack = turret ? Math.max(24, Number(mob.radius) || 0) : (Number(mob.radius) || 0) + 16;
    if (distance > range + rangeSlack) return;
    if (!turret) {
      const swingId = Number(data.swingId);
      if (!Number.isFinite(swingId) || swingId !== attacker.lastSwingId || now - (attacker.lastSwingAt || 0) > 350) return;
      const hitIds = attacker.lastMobHitIds || (attacker.lastMobHitIds = new Set());
      if (hitIds.has(mobId)) return;
      hitIds.add(mobId);
    }
    const weapon = Number(attacker.weapon) === 2 ? 2 : 1;
    let dmg;
    if (turret) {
      dmg = turretProjectileDamage(turret);
    } else {
      const tier = Math.max(0, Math.min(11, Number(weapon === 2 ? attacker.swordTier : attacker.axeTier) || 0));
      const isScythe = weapon === 2 && Boolean(attacker.scytheId || (attacker.swordSkin && String(attacker.swordSkin).startsWith('scythe_')));
      const dmgMult = Math.max(0.5, Math.min(3.0, Number(attacker.damageMultiplier) || 1.0));
      dmg = calculateMeleeDamage(weapon, tier, { isScythe, damageMultiplier: dmgMult });

      // Seviye farkı ve Melee statı etkisi
      const aLvl = calculatePlayerLevel(attacker);
      const mobLvl = mob.level || 1;
      const lvlFactor = calculateLevelGapMultiplier(aLvl, mobLvl);
      const meleeLvl = Math.max(1, Number(attacker.meleeLevel || 1));
      const meleeBonus = 1 + Math.min(0.75, (meleeLvl - 1) * 0.022);
      dmg = Math.max(1, Math.round(dmg * lvlFactor * meleeBonus));

      // Draconic Crit (Ejderha Barbar)
      if (attacker.critChance && Math.random() < attacker.critChance) {
        dmg = Math.round(dmg * (attacker.critMultiplier || 1.75));
        socket.emit('combat_crit', { mobId: mob.id, dmg });
      }

      // Necromancer Lifesteal (Ruh Necromancer)
      if (attacker.lifesteal && attacker.lifesteal > 0 && (attacker.hp ?? 0) < (attacker.maxHp || 250)) {
        const heal = Math.max(1, Math.round(dmg * attacker.lifesteal));
        attacker.hp = Math.min(attacker.maxHp || 250, attacker.hp + heal);
        attacker.hpSeq = (attacker.hpSeq || 0) + 1;
        attacker.hpAt = now;
        socket.emit('self_state', { hp: attacker.hp, hpSeq: attacker.hpSeq, hpAt: attacker.hpAt });
      }

      // Oyuncuya Melee XP kazandır!
      const meleeXpGain = Math.max(5, Math.round(dmg * 0.45));
      awardCombatXp(attacker, 'melee', meleeXpGain, { hitId: mob.id, targetLvl: mobLvl });
    }

    if (mob.isBoss) dmg = Math.min(dmg, Math.max(1, Math.ceil((Number(mob.maxHp) || 1) / 18)));
    mob.hp = Math.max(0, mob.hp - dmg);
    setMobTarget(mob, socket.id, now);

    // Mob knockback / Geri itme
    const pushAngle = Number.isFinite(Number(data.angle)) ? Number(data.angle) : Math.atan2(mob.y - sourceY, mob.x - sourceX);
    const pushForce = isScythe ? 18 : 13;
    mob.vx = (mob.vx || 0) + Math.cos(pushAngle) * pushForce;
    mob.vy = (mob.vy || 0) + Math.sin(pushAngle) * pushForce;
    mob.x += Math.cos(pushAngle) * (pushForce * 0.7);
    mob.y += Math.sin(pushAngle) * (pushForce * 0.7);
    mob.angle = Math.atan2(sourceY - mob.y, sourceX - mob.x);

    mob.stateSeq = (mob.stateSeq || 0) + 1;
    broadcastMobEventNear(mob, 'mob_update', {
      id: mob.id, seq: mob.stateSeq, ts: now, x: mob.x, y: mob.y,
      vx: mob.vx, vy: mob.vy, angle: mob.angle,
      hp: mob.hp, maxHp: mob.maxHp, hitFlash: 8, targetId: socket.id
    });

    if (mob.hp <= 0) {
      mobs.delete(mob.id);
      broadcastMobEventNear(mob, 'mob_dead', { id: mob.id, killerId: socket.id });

      // Necromancer kill heal
      if (attacker.itemStats?.helmet?.killHeal && (attacker.hp ?? 0) < (attacker.maxHp || 250)) {
        attacker.hp = Math.min(attacker.maxHp || 250, attacker.hp + attacker.itemStats.helmet.killHeal);
        socket.emit('self_state', { hp: attacker.hp });
      }

      const rewardGold = Math.max(1, Math.floor((mob.goldReward || 10) * 0.65));
      const rewardXp = Math.max(1, Math.round((mob.xpReward || 35) * Math.max(0.1, Number(adminConfig.xpRate) || 1)));
      const rewardScore = Math.round(rewardXp * 0.75 + rewardGold * 3);
      attacker.gold = (attacker.gold || 0) + rewardGold;
      attacker.xp = (attacker.xp || 0) + rewardXp;
      attacker.score = (attacker.score || 0) + rewardScore;
      attacker.kills = (attacker.kills || 0) + 1;
      applyLoadoutStats(attacker);
      attacker.hpSeq = (attacker.hpSeq || 0) + 1;
      attacker.hpAt = Date.now();
      const mobQuestKey = questMobKey(mob);
      recordServerQuestProgress(attacker, { kills: 1, ...(mobQuestKey ? { [mobQuestKey]: 1 } : {}), gold: rewardGold });
      if (attacker._authUser) {
        attacker._authUser.xp = (attacker._authUser.xp || 0) + rewardXp;
        attacker._authUser.rankId = rankInfo(attacker._authUser.xp).rankId;
      }
      persistPlayerScore(attacker);
      socket.emit('self_state', {
        hp: attacker.hp, maxHp: attacker.maxHp, baseMaxHp: attacker._loadoutBaseMaxHp,
        hpSeq: attacker.hpSeq, hpAt: attacker.hpAt,
        g: attacker.gold, xp: attacker.xp, sc: attacker.score, k: attacker.kills,
        matchKills: Math.max(0, attacker.kills - (attacker.matchStartKills || 0))
      });
      socket.emit('mob_kill_reward', {
        xp: rewardXp,
        gold: rewardGold,
        score: rewardScore,
        typeName: mob.typeName
      });
      awardLoot(attacker, mob.level || mob.lvl || 1, Boolean(mob.isBoss));
      setTimeout(() => {
        if (players.size > 0) ensureMobs();
      }, 4000 + Math.random() * 2000);
    }
  });

  socket.on('world_boss_hit_req', (data = {}) => {
    if (socketEventRateLimited(socket, 'world_boss_hit_req')) return;
    const attacker = players.get(socket.id);
    const bossId = String(data.bossId || '');
    const bossDef = WORLD_BOSS_DEFS.find(def => def.id === bossId);
    const boss = worldBossStates.get(bossId);
    if (!attacker || !bossDef || !boss || !boss.alive || (attacker.hp ?? 0) <= 0 || attacker._dead) return;

    const now = Date.now();
    const swingId = Number(data.swingId);
    if (!Number.isFinite(swingId) || swingId !== attacker.lastSwingId || now - (attacker.lastSwingAt || 0) > 400) return;
    const hitIds = attacker.lastBossHitIds || (attacker.lastBossHitIds = new Set());
    if (hitIds.has(bossId)) return;

    const weapon = Number(attacker.weapon) === 2 ? 2 : Number(attacker.weapon) === 1 ? 1 : 0;
    if (!weapon) return;
    const isScythe = weapon === 2 && Boolean(attacker.scytheId || (attacker.swordSkin && String(attacker.swordSkin).startsWith('scythe_')));
    const attackAngle = Number(attacker.lastAttackAngle);
    if (!Number.isFinite(attackAngle)) return;
    const dx = boss.x - (Number(attacker.x) || 0);
    const dy = boss.y - (Number(attacker.y) || 0);
    const weaponRange = isScythe ? 168 : (weapon === 2 ? 140 : 128);
    const attackerRadius = Math.max(16, Math.min(64, Number(attacker.radius) || 24));
    if (Math.hypot(dx, dy) > weaponRange + bossDef.radius + attackerRadius + 16) return;

    let angleDiff = Math.atan2(dy, dx) - attackAngle;
    while (angleDiff > Math.PI) angleDiff -= Math.PI * 2;
    while (angleDiff < -Math.PI) angleDiff += Math.PI * 2;
    const spread = isScythe ? Math.PI / 2.6 : (weapon === 2 ? Math.PI / 3.25 : Math.PI / 2.57);
    if (Math.abs(angleDiff) > spread) return;
    hitIds.add(bossId);

    const tier = Math.max(0, Math.min(11, Number(weapon === 2 ? attacker.swordTier : attacker.axeTier) || 0));
    let damage = calculateMeleeDamage(weapon, tier, {
      isScythe,
      damageMultiplier: Math.max(0.5, Math.min(3, Number(attacker.damageMultiplier) || 1))
    });

    // Seviye farkı ve Melee statı etkisi
    const aLvl = calculatePlayerLevel(attacker);
    const bossLvl = bossDef.level || 50;
    const lvlFactor = calculateLevelGapMultiplier(aLvl, bossLvl);
    const meleeLvl = Math.max(1, Number(attacker.meleeLevel || 1));
    const meleeBonus = 1 + Math.min(0.75, (meleeLvl - 1) * 0.022);
    damage = Math.min(420, Math.max(1, Math.round(damage * lvlFactor * meleeBonus)));

    // Melee XP
    awardCombatXp(attacker, 'melee', Math.max(10, Math.round(damage * 0.5)), { bossId });

    const appliedDamage = Math.min(damage, boss.hp);
    recordWorldBossContribution(boss, attacker, appliedDamage);
    boss.hp = Math.max(0, boss.hp - appliedDamage);
    boss.hitFlashUntil = now + 140;
    boss.aggroed = true;
    boss.targetId = attacker.id;
    boss.state = 'hit';
    boss.attackUntil = Math.max(boss.attackUntil, now + 180);
    broadcastWorldBossStates();

    if (boss.hp <= 0) {
      defeatWorldBoss(bossDef, boss, attacker, now);
    } else {
      io.emit('world_boss_hit', {
        id: bossId, x: boss.x, y: boss.y, hp: boss.hp, maxHp: boss.maxHp,
        dmg: appliedDamage, attackerId: attacker.id, attackerName: attacker.name || 'Oyuncu'
      });
    }
  });

  socket.on('world_boss_turret_hit_req', (data = {}) => {
    if (socketEventRateLimited(socket, 'world_boss_turret_hit_req')) return;
    const attacker = players.get(socket.id);
    const bossId = String(data.bossId || '');
    const bossDef = WORLD_BOSS_DEFS.find(def => def.id === bossId);
    const boss = worldBossStates.get(bossId);
    const turret = buildings.get(String(data.buildingId || ''));
    if (!attacker || (attacker.hp ?? 0) <= 0 || attacker._dead ||
        !bossDef || !boss || !boss.alive ||
        !turret || Number(turret.type) !== 7 || (turret.hp ?? 0) <= 0 || turret.ownerId !== socket.id) return;
    if (Math.hypot(turret.x - boss.x, turret.y - boss.y) > turretRange(turret) + bossDef.radius + 16) return;

    const now = Date.now();
    const shotCooldownMs = 1000;
    if (now - (turret.lastBossHitAt || 0) < shotCooldownMs) return;
    turret.lastBossHitAt = now;
    const damage = Math.min(120, turretProjectileDamage(turret));
    const appliedDamage = Math.min(damage, boss.hp);
    recordWorldBossContribution(boss, attacker, appliedDamage);
    boss.hp = Math.max(0, boss.hp - appliedDamage);
    boss.hitFlashUntil = now + 140;
    boss.aggroed = true;
    boss.targetId = attacker.id;
    boss.state = 'hit';
    boss.attackUntil = Math.max(boss.attackUntil, now + 180);
    broadcastWorldBossStates();

    if (boss.hp <= 0) {
      defeatWorldBoss(bossDef, boss, attacker, now);
    } else {
      io.emit('world_boss_hit', {
        id: bossId, x: boss.x, y: boss.y, hp: boss.hp, maxHp: boss.maxHp,
        dmg: appliedDamage, attackerId: attacker.id, attackerName: attacker.name || 'Oyuncu'
      });
    }
  });

  socket.on('spike_mob_hit', (data = {}) => {
    if (socketEventRateLimited(socket, 'mob_hit_req')) return;
    const attacker = players.get(socket.id);
    const mob = mobs.get(String(data.mobId || ''));
    const spike = buildings.get(String(data.bId || ''));
    if (!attacker || (attacker.hp ?? 0) <= 0 || !mob || mob.hp <= 0 || !spike || Number(spike.type) !== 3 || (spike.hp ?? 0) <= 0) return;
    if (spike.ownerId !== socket.id) return;
    const spikeDistance = Math.hypot((Number(attacker.x) || 0) - spike.x, (Number(attacker.y) || 0) - spike.y);
    const mobDistance = Math.hypot((Number(mob.x) || 0) - spike.x, (Number(mob.y) || 0) - spike.y);
    if (spikeDistance > 280 || mobDistance > (Number(spike.radius) || 34) + (Number(mob.radius) || 36) + 24) return;
    applySpikeDamageToMob(mob, spike, attacker);
  });

  function normalizeBuilding(data, owner, id) {
    const type = Number(data.type);
    const x = Number(data.x), y = Number(data.y), angle = Number(data.angle) || 0;
    if (!Number.isInteger(type) || !SERVER_BUILD_LIMITS[type] || !Number.isFinite(x) || !Number.isFinite(y)) return null;
    if (Math.abs(x) > 6480 || Math.abs(y) > 6480) return null;
    if (!owner || owner.hp <= 0 || Math.hypot(x - (Number(owner.x) || 0), y - (Number(owner.y) || 0)) > 380) return null;
    const tier = Math.max(0, Math.min(5, Number(data.tier) || 0));
    const maxHp = getBuildingMaxHp(type, tier);
    return {
      id, type, x, y, angle: Number.isFinite(angle) ? angle : 0,
      radius: BUILD_RADII[type], hp: maxHp, maxHp,
      tier,
      ownerId: owner.id, ownerClanId: owner.clanId || ''
    };
  }

  socket.on('place_building', (data = {}) => {
    const bType = Number(data.type);
    if (!Number.isInteger(bType) || !SERVER_BUILD_LIMITS[bType]) return;
    if (socketEventRateLimited(socket, 'place_building')) {
      socket.emit('build_limit_reached', { type: bType, count: 0, limit: SERVER_BUILD_LIMITS[bType] || 25, clientId: data.id });
      return;
    }
    const owner = players.get(socket.id);
    if (!owner) return;
    const now = Date.now();
    const limit = SERVER_BUILD_LIMITS[bType] || 25;
    let ownedCount = 0;
    for (const b of buildings.values()) {
      if (b.ownerId === socket.id && Number(b.type) === bType && (b.hp === undefined || b.hp > 0)) {
        ownedCount++;
      }
    }
    if (now - (owner.lastBuildAt || 0) < BUILD_ACTION_COOLDOWN) {
      socket.emit('build_limit_reached', { type: bType, count: ownedCount, limit, clientId: data.id });
      socket.emit('self_state', { g: owner.gold, wood: owner.wood, stone: owner.stone, apples: owner.apples });
      return;
    }
    if (ownedCount >= limit) {
      socket.emit('build_limit_reached', { type: bType, count: ownedCount, limit, clientId: data.id });
      socket.emit('self_state', { g: owner.gold, wood: owner.wood, stone: owner.stone, apples: owner.apples });
      return;
    }

    const id = `${socket.id}-${crypto.randomBytes(6).toString('hex')}`;
    const building = normalizeBuilding({ ...data, type: bType }, { ...owner, id: socket.id }, id);
    if (!building) {
      socket.emit('build_limit_reached', { type: bType, count: ownedCount, limit, clientId: data.id });
      socket.emit('self_state', { g: owner.gold, wood: owner.wood, stone: owner.stone, apples: owner.apples });
      return;
    }
    const overlapRadius = BUILD_OVERLAP_RADII[bType] || 30;
    const nearby = nearbyBuildings(building.x, building.y, overlapRadius + 60);
    if (nearby.some(existing => buildingsOverlap(building, existing))) {
      socket.emit('build_limit_reached', {
        type: bType,
        count: ownedCount,
        limit,
        clientId: data.id,
        reason: 'overlap'
      });
      socket.emit('self_state', { g: owner.gold, wood: owner.wood, stone: owner.stone, apples: owner.apples });
      return;
    }
    const [wood, stone, gold] = BUILD_COSTS[bType] || [20, 5, 0];
    if ((owner.wood || 0) < wood || (owner.stone || 0) < stone || (owner.gold || 0) < gold) {
      socket.emit('build_limit_reached', { type: bType, count: ownedCount, limit, clientId: data.id });
      socket.emit('self_state', { g: owner.gold, wood: owner.wood, stone: owner.stone, apples: owner.apples });
      return;
    }
    owner.wood -= wood; owner.stone -= stone; owner.gold -= gold;
    owner.lastBuildAt = now;
    owner.weapon = bType;
    owner.isAttacking = true;
    owner.attackUntil = now + 240;
    owner.lastSwingAt = now;
    buildings.set(id, building);
    recordServerQuestProgress(owner, { buildings: 1 });
    scheduleBuildingGridRebuild();
    socket.emit('self_state', { g: owner.gold, wood: owner.wood, stone: owner.stone, apples: owner.apples });
    socket.emit('build_ack', { clientId: data.id, serverId: id });
    triggerSpikeContacts(building, now);
    broadcastPlayerEventNear(owner, 'player_attack', {
      id: socket.id,
      weapon: bType,
      angle: owner.angle,
      at: now,
      durationMs: 240
    });
    io.emit('build', { id, building: { ...building } });
  });
  socket.on('build', (data = {}) => {
    // Legacy client event intentionally ignored; place_building is authoritative.
  });
  socket.on('build_destroy', ({ id } = {}) => {
    const building = buildings.get(id);
    if (!building) return;
    const player = players.get(socket.id);
    const isOwner = building.ownerId === socket.id;
    const isClanOwner = player?.clanId && building.ownerClanId === player.clanId && clans.get(player.clanId)?.ownerId === socket.id;
    if (!isOwner && !isClanOwner) return;
    if (Number(building.type) === 6) releaseTrapVictims(id);
    buildings.delete(id);
    scheduleBuildingGridRebuild();
    io.emit('build_destroy', { id });
    io.emit('trap_freed', { buildingId: id });
  });
  socket.on('building_hit', (data = {}) => {
    if (socketEventRateLimited(socket, 'building_hit')) return;
    const { id } = data;
    const building = buildings.get(id) || buildings.get(String(id));
    const attacker = players.get(socket.id);
    if (!building || !attacker || attacker.hp <= 0) return;
    const swingId = Number(data.swingId);
    const now = Date.now();
    if (!Number.isFinite(swingId) || swingId !== attacker.lastSwingId || now - (attacker.lastSwingAt || 0) > 350) return;
    const weapon = Number(attacker.weapon);
    if (weapon !== 1 && weapon !== 2) return;
    if (building.ownerClanId && attacker.clanId && building.ownerClanId === attacker.clanId) return;
    const isScythe = weapon === 2 && Boolean(attacker.scytheId || (attacker.swordSkin && String(attacker.swordSkin).startsWith('scythe_')));
    const attackAngle = Number(attacker.lastAttackAngle);
    if (!Number.isFinite(attackAngle)) return;
    const dx = Number(building.x) - (Number(attacker.x) || 0);
    const dy = Number(building.y) - (Number(attacker.y) || 0);
    const distance = Math.hypot(dx, dy);
    const buildingRadius = buildingCollisionRadius(building);
    const attackerRadius = Math.max(16, Math.min(64, Number(attacker.radius) || 24));
    const weaponRange = isScythe ? 168 : weapon === 2 ? 140 : 128;
    if (distance > attackerRadius * 0.5 + weaponRange + buildingRadius) return;
    const pointBlank = distance <= attackerRadius + buildingRadius + 20;
    if (!pointBlank && attacker.trappedBy !== building.id) {
      let angleDiff = Math.atan2(dy, dx) - attackAngle;
      while (angleDiff > Math.PI) angleDiff -= Math.PI * 2;
      while (angleDiff < -Math.PI) angleDiff += Math.PI * 2;
      const spread = isScythe ? Math.PI / 2.5 : weapon === 2 ? Math.PI / 3.25 : Math.PI / 2.57;
      if (Math.abs(angleDiff) > spread) return;
    }
    const hitIds = attacker.lastBuildingHitIds || (attacker.lastBuildingHitIds = new Set());
    const buildingId = String(building.id || id);
    if (hitIds.has(buildingId)) return;
    // Removed: if (building.ownerId === socket.id) return; (Players should be able to break their own builds)
    const lastHitAt = attacker.lastBuildingHitAt || (attacker.lastBuildingHitAt = new Map());
    if (now - (lastHitAt.get(buildingId) || 0) < BUILDING_HIT_COOLDOWN_MS) return;
    hitIds.add(buildingId);
    lastHitAt.set(buildingId, now);
    if (lastHitAt.size > 256) {
      for (const [hitBuildingId, hitAt] of lastHitAt) {
        if (now - hitAt > 10000) lastHitAt.delete(hitBuildingId);
      }
    }
    const tier = Math.max(0, Math.min(5, Number(weapon === 2 ? attacker.swordTier : attacker.axeTier) || 0));
    const hitDmg = calculateMeleeDamage(weapon, tier, { isScythe, maxDamage: 120, buildingDamageMultiplier: BUILDING_MELEE_DAMAGE_MULTIPLIER });
    building.hp = Math.max(0, (building.hp ?? building.maxHp ?? 100) - hitDmg);
    io.emit('build_hp_update', { id, hp: building.hp });
    if (building.hp <= 0) {
      if (Number(building.type) === 6) releaseTrapVictims(id);
      buildings.delete(id);
      scheduleBuildingGridRebuild();
      io.emit('build_destroy', { id });
      io.emit('trap_freed', { buildingId: id });
    }
  });
  socket.on('build_hp_update', (data = {}) => {
    if (socketEventRateLimited(socket, 'build_hp_update')) return;
    const id = String(data.id || '');
    const hp = Number(data.hp);
    const building = buildings.get(id);
    if (!building || !Number.isFinite(hp)) return;
    const player = players.get(socket.id);
    const isOwner = building.ownerId === socket.id;
    const isClanOwner = player?.clanId && building.ownerClanId === player.clanId;
    if (!isOwner && !isClanOwner) return; // Only owner or clan member can update building HP directly!
    if (hp >= (building.hp ?? building.maxHp ?? 100)) return;
    building.hp = Math.max(0, Math.min(building.hp ?? building.maxHp ?? 100, hp));
    io.emit('build_hp_update', { id, hp: building.hp });
    if (building.hp <= 0) {
      if (Number(building.type) === 6) releaseTrapVictims(id);
      buildings.delete(id);
      scheduleBuildingGridRebuild();
      io.emit('build_destroy', { id });
      io.emit('trap_freed', { buildingId: id });
    }
  });

  socket.on('build_repair', ({ id } = {}) => {
    const building = buildings.get(String(id || ''));
    const player = players.get(socket.id);
    const sendResult = (ok, reason = '') => socket.emit('build_repair_result', { id: String(id || ''), ok, reason });
    if (socketEventRateLimited(socket, 'build_repair')) return sendResult(false, 'rate_limited');
    if (!building || !player || building.ownerId !== socket.id || building.hp >= building.maxHp) return sendResult(false, 'invalid_building');
    if (Math.hypot((Number(player.x) || 0) - building.x, (Number(player.y) || 0) - building.y) > 290) return sendResult(false, 'too_far');
    const repairCost = Math.max(1, Math.ceil((building.maxHp - building.hp) / building.maxHp * 15));
    if ((player.wood || 0) < repairCost) return sendResult(false, 'insufficient_wood');
    player.wood -= repairCost;
    building.hp = building.maxHp;
    io.emit('build_hp_update', { id: building.id, hp: building.hp });
    socket.emit('self_state', { g: player.gold, wood: player.wood, stone: player.stone, apples: player.apples });
    sendResult(true);
  });

  socket.on('build_tier_update', (data = {}) => {
    const id = String(data.id || '');
    const building = buildings.get(id);
    const player = players.get(socket.id);
    const rejectUpgrade = () => socket.emit('build_tier_rejected', {
      id,
      tier: building?.tier || 0,
      maxHp: building?.maxHp || 0,
      hp: building?.hp || 0,
      score: player?.score || 0
    });
    if (socketEventRateLimited(socket, 'build_tier_update')) return rejectUpgrade();
    if (!building || building.ownerId !== socket.id) return rejectUpgrade();
    const newTier = Math.min(5, Math.max(0, Number(data.tier) || 0));
    const UPGRADE_SCORE = [400, 1000, 2500, 6000, 15000];
    const prevTier = building.tier || 0;
    if (newTier !== prevTier + 1) return rejectUpgrade();
    const cost = UPGRADE_SCORE[prevTier] || 0;
    if (!player || (player.score || 0) < cost) return rejectUpgrade();
    player.score -= cost;
    syncLivePlayerProgress(player);
    const hpRatio = building.maxHp > 0 ? Math.max(0, Math.min(1, building.hp / building.maxHp)) : 1;
    building.tier = newTier;
    building.maxHp = getBuildingMaxHp(building.type, newTier);
    building.hp = Math.max(1, Math.round(building.maxHp * hpRatio));
    io.emit('build_tier_update', { id, tier: building.tier, maxHp: building.maxHp, hp: building.hp });
    if (player) {
      persistPlayerScore(player);
      socket.emit('self_state', { sc: player.score, g: player.gold });
    }
  });

  socket.on('buildings_sync', () => socket.emit('buildings_sync', { buildings: Object.fromEntries(buildings) }));

  socket.on('clan_list_get', () => {
    socket.emit('clan_list', getPublicClanList());
  });

  socket.on('clan_create', ({ name, tag, playerName } = {}) => {
    const player = players.get(socket.id) || { name: String(playerName || 'Oyuncu').trim() };
    if (!player || player.clanId || socket.data.clanId) return socket.emit('clan_error', { msg: 'Önce mevcut klanından ayrılmalısın.' });
    const cleanName = String(name || '').trim().replace(/[^a-zA-Z0-9çÇğĞıİöÖşŞüÜ _-]/g, '').slice(0, 20);
    const cleanTag = String(tag || '').trim().toUpperCase().replace(/[^A-Z0-9ÇĞİÖŞÜ]/g, '').slice(0, 4);
    if (cleanName.length < 3 || cleanTag.length < 2) return socket.emit('clan_error', { msg: 'Klan adı en az 3, etiket en az 2 karakter olmalı (özel karakterler hariç).' });
    const cleanOwnerName = String(player.name || 'Oyuncu').trim().replace(/[^a-zA-Z0-9çÇğĞıİöÖşŞüÜ _-]/g, '').slice(0, 20) || 'Oyuncu';
    const id = crypto.randomBytes(4).toString('hex');
    const clan = { id, name: cleanName, tag: cleanTag, ownerId: socket.id, ownerName: cleanOwnerName, members: [{ id: socket.id, name: cleanOwnerName }] };
    clans.set(id, clan); saveAccountData(); player.clanId = id; player.clanTag = cleanTag; socket.join(`clan:${id}`);
    socket.data.clanId = id; socket.data.clanName = cleanOwnerName;
    socket.emit('clan_joined', publicClan(clan));
    broadcastClanList();
  });
  socket.on('clan_join', ({ id, playerName } = {}) => {
    const player = players.get(socket.id) || { name: String(playerName || 'Oyuncu').trim() };
    const targetId = String(id || '').trim().toLowerCase();
    const clan = clans.get(targetId) || Array.from(clans.values()).find(c => c.id.toLowerCase() === targetId || c.tag.toLowerCase() === targetId || c.name.toLowerCase() === targetId);
    if (!player || !clan) return socket.emit('clan_error', { msg: 'Klan bulunamadı.' });
    if (player.clanId || socket.data.clanId) return socket.emit('clan_error', { msg: 'Zaten bir klandasın.' });
    if (clan.members.length >= 20) return socket.emit('clan_error', { msg: 'Klan dolu.' });
    clan.members.push({ id: socket.id, name: player.name }); player.clanId = clan.id; player.clanTag = clan.tag; socket.join(`clan:${clan.id}`);
    socket.data.clanId = clan.id; socket.data.clanName = player.name;
    saveAccountData(); emitClanUpdate(clan); socket.emit('clan_joined', publicClan(clan));
    broadcastClanList();
  });
  socket.on('clan_kick', ({ memberId } = {}) => {
    const player = players.get(socket.id); const clan = clans.get(player?.clanId);
    if (!clan || (clan.ownerId !== socket.id && clan.ownerName !== player.name) || !clan.members.some(member => member.id === memberId)) return;
    const target = players.get(memberId); if (target) { target.clanId = ''; target.clanTag = ''; io.sockets.sockets.get(memberId)?.leave(`clan:${clan.id}`); io.to(memberId).emit('clan_kicked'); }
    clan.members = clan.members.filter(member => member.id !== memberId); saveAccountData(); emitClanUpdate(clan);
    broadcastClanList();
  });
  socket.on('clan_leave', () => leaveClan(socket));
  socket.on('clan_get', () => {
    const clan = clans.get(players.get(socket.id)?.clanId || socket.data.clanId);
    if (clan) socket.emit('clan_joined', publicClan(clan));
    socket.emit('clan_list', getPublicClanList());
  });

  socket.on('party_create', ({ name } = {}) => {
    const code = Math.random().toString(36).slice(2, 7).toUpperCase();
    parties.set(code, { code, members: [{ id: socket.id, name: name || 'Oyuncu' }], owner: socket.id });
    socket.join(`party:${code}`);
    socket.emit('party_created', parties.get(code));
  });
  socket.on('party_join', ({ code, name } = {}) => {
    const party = parties.get(String(code || '').toUpperCase());
    if (!party || party.members.length >= 8) return socket.emit('party_error', { msg: 'Parti bulunamadı veya dolu.' });
    if (party.members.some(member => member.id === socket.id)) return socket.emit('party_joined', party);
    party.members.push({ id: socket.id, name: name || 'Oyuncu' });
    socket.join(`party:${party.code}`);
    io.to(`party:${party.code}`).emit('party_update', party);
    socket.emit('party_joined', party);
  });
  socket.on('party_start', () => { for (const room of socket.rooms) if (room.startsWith('party:')) io.to(room).emit('party_game_start', { partyCode: room.slice(6) }); });
  socket.on('party_leave', () => {
    for (const room of socket.rooms) if (room.startsWith('party:')) {
      const party = parties.get(room.slice(6));
      if (party) {
        party.members = party.members.filter(member => member.id !== socket.id);
        if (party.owner === socket.id) party.owner = party.members[0]?.id || null;
        if (!party.members.length) parties.delete(party.code);
        else io.to(room).emit('party_update', party);
      }
      socket.leave(room);
    }
    socket.emit('party_left');
  });

  socket.on('disconnect', () => {
    for (const key of mobHitCooldowns.keys()) if (key.startsWith(`${socket.id}:`)) mobHitCooldowns.delete(key);
    for (const resource of serverResources) {
      resource.lastHitBy.delete(socket.id);
      resource.lastHitSwingBy.delete(socket.id);
    }
    const player = players.get(socket.id);
    const guestId = String(player?._guestId || '').slice(0, 80);
    if (player && guestId && player.hp > 0 && !player._dead) {
      const {
        visibleMobIds,
        visiblePlayerIds,
        _lastAoiBatch,
        _lastSpectatorBatch,
        _lastSelfStateKey,
        _lastSelfStateAt,
        ...reconnectState
      } = player;
      reconnectSessions.set(guestId, {
        savedAt: Date.now(),
        socketId: socket.id,
        clientIp: requestClientKey(socket.request || { headers: {}, socket: socket.conn?.transport?.socket }),
        authUser: player._authUser,
        reconnectSecret: player._reconnectSecret,
        state: reconnectState
      });
    } else if (player) {
      onPlayerDeath(socket.id);
      if (guestId) reconnectSessions.delete(guestId);
    }
    if (player && (player.score > 0 || player.gold > 0 || player.kills > 0 || player._authUser)) {
      syncLivePlayerProgress(player);
      persistPlayerScore(player);
      saveAccountData(true);
    }
    // Note: Do not leaveClan on disconnect so clans & leadership persist across reconnections/refreshes
    if (player?.roomId && rooms.has(player.roomId)) {
      const roomSet = rooms.get(player.roomId);
      roomSet.delete(socket.id);
      if (roomSet.size === 0) rooms.delete(player.roomId);
    }
    players.delete(socket.id);
    for (const [code, party] of parties) {
      const hadMember = party.members.some(member => member.id === socket.id);
      if (!hadMember) continue;
      party.members = party.members.filter(member => member.id !== socket.id);
      if (party.owner === socket.id) party.owner = party.members[0]?.id || null;
      if (!party.members.length) parties.delete(code);
      else io.to(`party:${code}`).emit('party_update', party);
    }
    socket.broadcast.emit('player_left', { id: socket.id, name: player?.name || 'Oyuncu' });
    broadcastOnlineCount();
  });
});

server.on('clientError', (err, socket) => {
  if (err.code === 'ECONNRESET' || !socket.writable) return;
  socket.end('HTTP/1.1 400 Bad Request\r\n\r\n');
});

process.on('uncaughtException', (err) => {
  if (err && (err.code === 'ECONNRESET' || err.code === 'EPIPE')) return;
  console.error('[Process] Uncaught exception:', err);
});

process.on('unhandledRejection', (reason) => {
  console.warn('[Process] Unhandled rejection:', reason);
});

server.on('error', (error) => {
  console.error(`[Server] Failed to listen on port ${PORT}:`, error.message);
  process.exitCode = 1;
});

server.listen(PORT, '0.0.0.0', () => {
  const address = server.address();
  const boundPort = address && typeof address === 'object' ? address.port : PORT;
  ensureMobs();
  rebuildMobGrid();
  console.log(`ForestBrawl multiplayer server listening on 0.0.0.0:${boundPort} (Initial mobs: ${mobs.size})`);
});