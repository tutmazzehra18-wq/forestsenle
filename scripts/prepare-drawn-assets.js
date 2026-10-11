'use strict';

const fs = require('node:fs/promises');
const path = require('node:path');
const { pathToFileURL } = require('node:url');
const { chromium } = require('playwright');
const sharp = require('sharp');

const projectRoot = path.resolve(__dirname, '..');
const gameFile = path.join(projectRoot, 'game', 'play.html');
const sourceRoot = path.join(projectRoot, 'game', 'procedural-assets', '4k');
const runtimeRoot = path.join(projectRoot, 'game', 'procedural-assets', 'runtime');

const mobDrawers = [
  ['wild_hare', '_drawWildHare', 55],
  ['forest_deer', '_drawForestDeer', 55],
  ['polar_bear', '_drawPolarBear', 75],
  ['frost_fox', '_drawFrostFox', 55],
  ['mammoth', '_drawMammoth', 75],
  ['rhino', '_drawMammoth', 55],
  ['sand_viper', '_drawSandViper', 55],
  ['dune_scorpion', '_drawDuneScorpion', 70],
  ['dune_lizard', '_drawDuneLizard', 55],
  ['magma_hound', '_drawMagmaHound', 55],
  ['fire_drake', '_drawFireDrake', 65],
  ['obsidian_golem', '_drawObsidianGolem', 75],
];

async function renderAtlas(page, kind, options) {
  return page.evaluate(({ kind, options }) => {
    const width = options.columns * options.cellSize;
    const height = options.rows * options.cellSize;
    const canvas = document.createElement('canvas');
    canvas.width = width;
    canvas.height = height;
    const context = canvas.getContext('2d');
    if (!context) throw new Error('Could not create the asset atlas canvas.');
    context.imageSmoothingEnabled = true;
    context.imageSmoothingQuality = 'high';

    const paint = (column, row, callback) => {
      context.save();
      context.translate(column * options.cellSize + options.offsetX, row * options.cellSize + options.offsetY);
      context.scale(options.scale, options.scale);
      callback();
      context.restore();
    };

    if (kind === 'weapon-tiers') {
      const drawWeapon = options.weapon === 'axe' ? window.drawAxeByTier : window.drawSwordByTier;
      if (typeof drawWeapon !== 'function') throw new Error(`Missing ${options.weapon} tier drawing function.`);
      const oldQuality = _qualityLevel;
      _qualityLevel = 2;
      try {
        for (let tier = 7; tier <= 11; tier++) {
          for (let frame = 0; frame < options.frames; frame++) {
            paint(frame, tier - 7, () => drawWeapon(context, tier, frame * options.frameDuration));
          }
        }
      } finally {
        _qualityLevel = oldQuality;
      }
    } else if (kind === 'weapon-skin') {
      const drawWeapon = options.weapon === 'axe' ? window.drawAxeSkin : window.drawSwordSkin;
      if (typeof drawWeapon !== 'function') throw new Error(`Missing ${options.weapon} skin drawing function.`);
      const oldQuality = _qualityLevel;
      _qualityLevel = 2;
      try {
        for (let frame = 0; frame < options.frames; frame++) {
          paint(frame, 0, () => drawWeapon(context, options.skin, frame * options.frameDuration));
        }
      } finally {
        _qualityLevel = oldQuality;
      }
    } else if (kind === 'mob') {
      const drawMob = window[options.renderer];
      if (typeof drawMob !== 'function') throw new Error(`Missing mob drawing function: ${options.renderer}`);
      const oldQuality = _qualityLevel;
      _qualityLevel = 2;
      try {
        for (let stateIndex = 0; stateIndex < options.states.length; stateIndex++) {
          const state = options.states[stateIndex];
          for (let frame = 0; frame < options.frames; frame++) {
            const phase = frame * Math.PI * 2 / options.frames;
            const mob = {
              shape: options.shape,
              color: '#8b6b4b',
              outline: '#28170d',
              eyes: '#ffcc66',
              hp: 100,
              maxHp: 100,
              id: 1,
            };
            paint(frame, stateIndex, () => drawMob(
              context,
              mob,
              options.radius,
              state === 'walk',
              state,
              phase,
              frame * options.attackDuration / options.frames,
              false,
            ));
          }
        }
      } finally {
        _qualityLevel = oldQuality;
      }
    } else {
      throw new Error(`Unsupported atlas kind: ${kind}`);
    }

    return canvas.toDataURL('image/png');
  }, { kind, options });
}

async function writeAsset(page, entry, renderKind, renderOptions, runtimeSize) {
  const dataUrl = await renderAtlas(page, renderKind, renderOptions);
  const comma = dataUrl.indexOf(',');
  if (comma < 0 || !dataUrl.startsWith('data:image/png;base64,')) {
    throw new Error(`Canvas export returned invalid image data for ${entry.name}.`);
  }
  const sourcePath = path.join(sourceRoot, entry.source);
  const runtimePath = path.join(runtimeRoot, entry.runtime);
  await fs.mkdir(path.dirname(sourcePath), { recursive: true });
  await fs.mkdir(path.dirname(runtimePath), { recursive: true });
  const source = Buffer.from(dataUrl.slice(comma + 1), 'base64');
  const metadata = await sharp(source).metadata();
  if (metadata.width !== entry.width || metadata.height !== entry.height) {
    throw new Error(`${entry.name} expected ${entry.width}x${entry.height}, got ${metadata.width}x${metadata.height}.`);
  }
  await fs.writeFile(sourcePath, source);
  await sharp(source)
    .resize(runtimeSize.width, runtimeSize.height, { fit: 'fill' })
    .webp({ quality: 90, alphaQuality: 100, effort: 5 })
    .toFile(runtimePath);
  return {
    name: entry.name,
    source: path.relative(projectRoot, sourcePath).replaceAll(path.sep, '/'),
    sourceUrl: `/game/${path.relative(path.join(projectRoot, 'game'), sourcePath).replaceAll(path.sep, '/')}`,
    runtime: path.relative(projectRoot, runtimePath).replaceAll(path.sep, '/'),
    runtimeUrl: `/game/${path.relative(path.join(projectRoot, 'game'), runtimePath).replaceAll(path.sep, '/')}`,
    sourceWidth: entry.width,
    sourceHeight: entry.height,
    runtimeWidth: runtimeSize.width,
    runtimeHeight: runtimeSize.height,
  };
}

async function main() {
  let browser;
  try {
    const launchOptions = { headless: true };
    if (process.env.PLAYWRIGHT_CHROMIUM_EXECUTABLE) {
      launchOptions.executablePath = process.env.PLAYWRIGHT_CHROMIUM_EXECUTABLE;
    }
    browser = await chromium.launch(launchOptions);
  } catch (error) {
    throw new Error(`Could not launch Playwright Chromium. Install it with "npx playwright install chromium". ${error.message}`);
  }

  try {
    const page = await browser.newPage();
    await page.goto(pathToFileURL(gameFile).href, { waitUntil: 'domcontentloaded' });
    await page.evaluate(() => {
      window._BUILDING_DRAWN_ASSETS = true;
      _qualityLevel = 2;
    });
    await page.waitForFunction(() =>
      typeof window.drawAxeByTier === 'function' &&
      typeof window.drawSwordByTier === 'function' &&
      typeof window.drawAxeSkin === 'function' &&
      typeof window.drawSwordSkin === 'function' &&
      typeof window._drawWildHare === 'function'
    );

    const manifest = [];
    const weaponAtlasOptions = {
      columns: 8,
      rows: 5,
      cellSize: 512,
      scale: 2.4,
      offsetX: 102,
      offsetY: 388,
      frames: 8,
      frameDuration: (Math.PI * 2) / (0.08 * 8),
    };

    for (const weapon of ['axe', 'sword']) {
      const entry = {
        name: `${weapon} tiers 7-11`,
        source: `weapons/${weapon}-tiers-7-11.png`,
        runtime: `weapons/${weapon}-tiers-7-11.webp`,
        width: 4096,
        height: 2560,
      };
      manifest.push(await writeAsset(
        page,
        entry,
        'weapon-tiers',
        { ...weaponAtlasOptions, weapon },
        { width: 1024, height: 640 },
      ));
      console.log(`Built ${entry.name}.`);
    }

    for (const weapon of ['axe', 'sword']) {
      const skins = await page.evaluate((weapon) => {
        const drawWeapon = weapon === 'axe' ? window.drawAxeSkin : window.drawSwordSkin;
        if (typeof drawWeapon !== 'function') throw new Error(`Missing ${weapon} skin drawing function.`);
        return [...drawWeapon.toString().matchAll(/case\s+['"]([^'"]+)['"]\s*:/g)]
          .map(match => match[1]);
      }, weapon);
      for (const skin of [...new Set(skins)]) {
        const entry = {
          name: `${weapon} skin ${skin}`,
          source: `weapon-skins/${weapon}-${skin}.png`,
          runtime: `weapon-skins/${weapon}-${skin}.webp`,
          width: 4096,
          height: 512,
        };
        manifest.push(await writeAsset(
          page,
          entry,
          'weapon-skin',
          {
            columns: 8,
            rows: 1,
            cellSize: 512,
            scale: 2.4,
            offsetX: 102,
            offsetY: 388,
            frames: 8,
            frameDuration: (Math.PI * 2) / ((weapon === 'axe' ? 0.18 : 0.15) * 8),
            weapon,
            skin,
          },
          { width: 1024, height: 128 },
        ));
      }
      console.log(`Built ${skins.length} ${weapon} skin atlases.`);
    }

    for (const [shape, renderer, attackDuration] of mobDrawers) {
      const entry = {
        name: `mob ${shape}`,
        source: `mobs/${shape}.png`,
        runtime: `mobs/${shape}.webp`,
        width: 4096,
        height: 1536,
      };
      manifest.push(await writeAsset(
        page,
        entry,
        'mob',
        {
          columns: 8,
          rows: 3,
          cellSize: 512,
          scale: 1.25,
          offsetX: 256,
          offsetY: 256,
          frames: 8,
          radius: 48,
          attackDuration,
          states: ['idle', 'walk', 'attack'],
          shape,
          renderer,
        },
        { width: 1024, height: 384 },
      ));
      console.log(`Built mob ${shape}.`);
    }

    const manifestPath = path.join(sourceRoot, 'manifest.json');
    await fs.mkdir(sourceRoot, { recursive: true });
    await fs.writeFile(manifestPath, `${JSON.stringify({
      format: 'ForestBrawl procedural sprite atlases',
      sourceResolution: '4K-wide PNG atlases for download',
      runtimeFormat: 'WebP, 4x downsampled for GPU memory and mobile performance',
      frameLayout: '8 columns; mob rows are idle, walk, attack',
      buildCommand: 'npm run build:assets',
      assets: manifest,
    }, null, 2)}\n`);
    console.log(`Wrote ${manifest.length} source and runtime assets to ${path.relative(projectRoot, sourceRoot)}.`);
  } finally {
    await browser.close();
  }
}

main().catch(error => {
  console.error('[Build drawn assets]', error.message);
  process.exitCode = 1;
});
