'use strict';

const fs = require('node:fs/promises');
const path = require('node:path');
const { pathToFileURL } = require('node:url');
const { chromium } = require('playwright');
const sharp = require('sharp');

const projectRoot = path.resolve(__dirname, '..');
const gameFile = path.join(projectRoot, 'game', 'play.html');
const sourceRoot = path.join(projectRoot, 'game', 'procedural-assets', '4k', 'missing');

const mobDrawers = [
  ['wolf', '_drawSpriteWolf', 55, '#6b4932', '#28170d', '#ffcc66'],
  ['spider', '_drawSpriteSpider', 65, '#2a1a38', '#0f0814', '#ff1100'],
  ['scorpion', '_drawSpriteScorpion', 70, '#4a2818', '#1a0d06', '#ff4400'],
  ['bear', '_drawSpriteBear', 75, '#4a2f1b', '#1a1008', '#ffaa00'],
];
const mobAtlasRenderScale = 1.25;

const accessoryGroups = [
  { category: 'wings', ids: ['w_angel', 'w_devil', 'w_dragon', 'w_fairy', 'w_bat'] },
  { category: 'hats', ids: ['h_party', 'h_cowboy', 'h_viking', 'h_santa', 'h_wizard', 'h_crown'] },
  { category: 'faces', ids: ['f_mustache', 'f_glasses', 'f_tusks', 'f_angry', 'f_mask'] },
  { category: 'accessories', ids: ['a_cape', 'a_tail', 'a_halo', 'a_backpack'] },
];

function encodeAssetName(value) {
  return value.replace(/[^a-z0-9_-]+/gi, '-').replace(/^-+|-+$/g, '').toLowerCase();
}

async function renderAtlas(page, asset) {
  return page.evaluate(({ asset }) => {
    const canvas = document.createElement('canvas');
    const cellSize = 512;
    const columns = 8;
    const rows = asset.kind === 'mob' ? 3 : 1;
    canvas.width = columns * cellSize;
    canvas.height = rows * cellSize;
    const context = canvas.getContext('2d');
    if (!context) throw new Error(`Could not create canvas for ${asset.name}.`);
    context.imageSmoothingEnabled = true;
    context.imageSmoothingQuality = 'high';

    const paint = (frame, row, scale, draw) => {
      context.save();
      context.translate(frame * cellSize + cellSize / 2, row * cellSize + cellSize / 2);
      context.scale(scale, scale);
      draw();
      context.restore();
    };

    if (asset.kind === 'mob') {
      const [, renderer, attackDuration, color, outline, eyes] = asset.definition;
      const drawMob = window[renderer];
      if (typeof drawMob !== 'function') throw new Error(`Missing mob renderer ${renderer}.`);
      for (const [row, state] of ['idle', 'walk', 'attack'].entries()) {
        for (let frame = 0; frame < columns; frame++) {
          const phase = frame * Math.PI * 2 / columns;
          const mob = { shape: asset.id, color, outline, eyes, hp: 100, maxHp: 100, id: 1 };
          paint(frame, row, mobAtlasRenderScale, () => drawMob(
            context,
            mob,
            48,
            state === 'walk',
            state,
            phase,
            frame * attackDuration / columns,
            false,
          ));
        }
      }
    } else if (asset.kind === 'mineral') {
      const drawMineral = {
        diamond: window._drawUltraDiamond,
        amethyst: window._drawUltraAmethyst,
        redite: window._drawUltraRedite,
      }[asset.id];
      if (typeof drawMineral !== 'function') throw new Error(`Missing mineral renderer ${asset.id}.`);
      for (let frame = 0; frame < columns; frame++) {
        const time = frame * Math.PI / 4;
        paint(frame, 0, 4, () => drawMineral(context, 0, 0, 42, 'forest', time));
      }
    } else if (asset.kind === 'skin') {
      for (let frame = 0; frame < columns; frame++) {
        if (typeof window.drawSkinBody !== 'function') throw new Error('Missing player skin renderer.');
        if (!GENERATED_SKIN_STYLES[asset.id]) throw new Error(`Unknown generated player skin ${asset.id}.`);
        paint(frame, 0, 4, () => drawSkinBody(context, 48, asset.id, frame * 3, false));
      }
    } else if (asset.kind === 'accessory') {
      const [category, id] = asset.id.split(':');
      const frameTime = frame => frame * 4;
      for (let frame = 0; frame < columns; frame++) {
        if (category === 'wings') {
          paint(frame, 0, 3, () => drawPlayerWings(context, id, frameTime(frame)));
        } else if (category === 'hats') {
          paint(frame, 0, 2, () => drawPlayerHat(context, id, frameTime(frame), 48));
        } else if (category === 'faces') {
          paint(frame, 0, 10, () => drawPlayerFace(context, id));
        } else {
          const renderer = {
            a_cape: drawPlayerCape,
            a_tail: drawPlayerTail,
            a_halo: drawPlayerHalo,
            a_backpack: drawPlayerBackpack,
          }[id];
          if (!renderer) throw new Error(`Missing accessory renderer ${id}.`);
          paint(frame, 0, 4, () => {
            if (id === 'a_backpack') renderer(context, 48);
            else renderer(context, frameTime(frame), 48);
          });
        }
      }
    } else if (asset.kind === 'building') {
      const previousContext = ctx;
      try {
        ctx = context;
        for (let tier = 0; tier < 6; tier++) {
          paint(tier, 0, 2, () => drawBuilding({
            x: 0,
            y: 0,
            type: 10,
            tier,
            life: tier * 8,
            hp: 100,
            maxHp: 100,
            shake: 0,
            hitTimer: 0,
          }));
        }
      } finally {
        ctx = previousContext;
      }
    } else {
      throw new Error(`Unsupported missing asset kind: ${asset.kind}`);
    }

    return canvas.toDataURL('image/png');
  }, { asset });
}

async function writeResourceIcon(source, destination) {
  const trimmed = await sharp(source)
    .trim({ background: { r: 0, g: 0, b: 0, alpha: 0 } })
    .png()
    .toBuffer();
  await sharp(trimmed)
    .resize(448, 448, { fit: 'contain' })
    .extend({
      top: 32,
      bottom: 32,
      left: 32,
      right: 32,
      background: { r: 0, g: 0, b: 0, alpha: 0 },
    })
    .png()
    .toFile(destination);
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
    const gameUrl = process.env.PLAYWRIGHT_GAME_URL || pathToFileURL(gameFile).href;
    await page.goto(gameUrl, { waitUntil: 'domcontentloaded' });
    await page.evaluate(() => {
      window._BUILDING_DRAWN_ASSETS = true;
      _qualityLevel = 2;
    });
    const mobAssetBaseUrl = new URL('mobassets/', gameUrl).href;
    await page.evaluate(baseUrl => {
      for (const [name, image] of Object.entries(_MOB_ASSETS)) {
        image.src = new URL(`${name}.png`, baseUrl).href;
      }
    }, mobAssetBaseUrl);
    await page.waitForFunction(() =>
      typeof window._drawSpriteWolf === 'function' &&
      typeof window._drawUltraDiamond === 'function' &&
      typeof window.drawSkinBody === 'function' &&
      typeof window.drawPlayerWings === 'function' &&
      typeof window.drawBuilding === 'function',
    );
    await page.waitForFunction(() =>
      ['kurt_govde', 'kurt_kafa', 'akrep_govde', 'akrep_kafa', 'bear_govde', 'bear_kafa',
        'spider_abdomen', 'spider_kafa'].every(key => {
        const image = _MOB_ASSETS[key];
        return image && image.complete && image.naturalWidth > 0;
      }),
    );

    const generatedSkins = await page.evaluate(() => Object.keys(GENERATED_SKIN_STYLES));
    const assets = [
      ...mobDrawers.map(([id, renderer, attackDuration]) => ({
        id,
        name: `Mob animasyonu: ${id}`,
        kind: 'mob',
        definition: mobDrawers.find(entry => entry[0] === id),
        relativePath: `mobs/${id}.png`,
      })),
      ...['diamond', 'amethyst', 'redite'].map(id => ({
        id,
        name: `Kaynak animasyonu: ${id}`,
        kind: 'mineral',
        relativePath: `resources/${id}.png`,
      })),
      ...generatedSkins.map(id => ({
        id,
        name: `Oyuncu görünümü: ${id}`,
        kind: 'skin',
        relativePath: `skins/${id}.png`,
      })),
      ...accessoryGroups.flatMap(group => group.ids.map(id => ({
        id: `${group.category}:${id}`,
        name: `Oyuncu aksesuarı: ${id}`,
        kind: 'accessory',
        relativePath: `${group.category}/${encodeAssetName(id)}.png`,
      }))),
      {
        id: 'resource-machine',
        name: 'Yapı görseli: kaynak makinesi',
        kind: 'building',
        relativePath: 'buildings/resource-machine.png',
      },
    ];

    await fs.mkdir(sourceRoot, { recursive: true });
    const resourceIconRoot = path.join(projectRoot, 'game', 'asset', 'resource-icons');
    await fs.mkdir(resourceIconRoot, { recursive: true });
    for (const [id, filename] of [
      ['wood', 'tree-forest.png'],
      ['stone', 'rock-forest.png'],
      ['gold', 'gold.png'],
    ]) {
      await writeResourceIcon(
        path.join(projectRoot, 'game', 'asset', filename),
        path.join(resourceIconRoot, `${id}.png`),
      );
    }

    const manifest = [];
    for (const asset of assets) {
      const dataUrl = await renderAtlas(page, asset);
      const comma = dataUrl.indexOf(',');
      if (comma < 0 || !dataUrl.startsWith('data:image/png;base64,')) {
        throw new Error(`Canvas export returned invalid image data for ${asset.name}.`);
      }
      const source = Buffer.from(dataUrl.slice(comma + 1), 'base64');
      const metadata = await sharp(source).metadata();
      const expectedHeight = asset.kind === 'mob' ? 1536 : 512;
      if (metadata.width !== 4096 || metadata.height !== expectedHeight) {
        throw new Error(`${asset.name} expected 4096x${expectedHeight}, got ${metadata.width}x${metadata.height}.`);
      }
      const outputPath = path.join(sourceRoot, asset.relativePath);
      await fs.mkdir(path.dirname(outputPath), { recursive: true });
      await fs.writeFile(outputPath, source);
      if (asset.kind === 'mineral') {
        const iconSource = await sharp(source)
          .extract({ left: 88, top: 88, width: 336, height: 336 })
          .png()
          .toBuffer();
        await writeResourceIcon(iconSource, path.join(resourceIconRoot, `${asset.id}.png`));
      }
      manifest.push({
        name: asset.name,
        category: asset.kind,
        source: `game/procedural-assets/4k/missing/${asset.relativePath.replaceAll(path.sep, '/')}`,
        sourceUrl: `/game/procedural-assets/4k/missing/${asset.relativePath.replaceAll(path.sep, '/')}`,
        sourceWidth: metadata.width,
        sourceHeight: metadata.height,
        frames: asset.kind === 'building' ? 6 : 8,
        frameLayout: asset.kind === 'mob' ? '8 columns: idle, walk, attack rows' :
          asset.kind === 'building' ? '6 columns: building tiers 1-6' : '8 animation frames',
      });
      console.log(`Built missing art atlas: ${asset.name}.`);
    }

    await fs.writeFile(path.join(sourceRoot, 'manifest.json'), `${JSON.stringify({
      format: 'ForestBrawl missing Canvas-drawn gameplay art',
      sourceResolution: '4096px-wide transparent PNG sprite atlases',
      included: 'Active mob animation atlases without a dedicated atlas, special minerals, generated player skins, Canvas-drawn player accessories, and the resource machine building.',
      excluded: 'Existing image-backed game art, interface graphics, and transient particle/VFX rendering.',
      frameLayout: '8 columns; mob rows are idle, walk, attack',
      buildCommand: 'npm run build:missing-assets',
      assets: manifest,
    }, null, 2)}\n`);
    console.log(`Wrote ${manifest.length} missing-art atlases to ${path.relative(projectRoot, sourceRoot)}.`);
  } finally {
    await browser.close();
  }
}

main().catch(error => {
  console.error('[Build missing art assets]', error.message);
  process.exitCode = 1;
});
