(function(root) {
  'use strict';

  const RARITIES = Object.freeze({
    common: Object.freeze({ name: 'Yaygın', color: '#a8b0bd', level: 1 }),
    rare: Object.freeze({ name: 'Nadir', color: '#50a7ff', level: 15 }),
    epic: Object.freeze({ name: 'Destansi', color: '#c084fc', level: 32 }),
    legendary: Object.freeze({ name: 'Efsanevi', color: '#ffb84d', level: 50 })
  });

  const EQUIPMENT_SLOTS = Object.freeze([
    { key: 'head', slot: 'head', icon: 'head', name: 'Başlık', names: ['Yırtıcı Kurt Başlığı', 'Donmuş Gözlemci Başlığı', 'Kum Kâşifi Başlığı', 'Kadim Ejder Tacı'] },
    { key: 'amulet', slot: 'amulet', icon: 'amulet', name: 'Muska', names: ['Dikenli Orman Muskası', 'Buzul Kalbi Muskası', 'Çöl Fırtınası Muskası', 'Kadim Yıldız Muskası'] },
    { key: 'gloves', slot: 'gloves', icon: 'gloves', name: 'Eldiven', names: ['Avcı Pati Sargıları', 'Buz Demir Eldivenleri', 'Akrep Kralı Eldivenleri', 'Titanın Çelik Elleri'] },
    { key: 'chest', slot: 'chest', icon: 'chest', name: 'Göğüslük', names: ['Kabuklu Orman Zırhı', 'Buzul Muhafız Zırhı', 'Kara Kum Zırhı', 'Dünya Çekirdeği Zırhı'] },
    { key: 'ring1', slot: 'ring', preferredRing: 'ring1', icon: 'ring', name: 'Yüzük', names: ['Yosunlu Avcı Yüzüğü', 'Kristal Ayaz Yüzüğü', 'Güneş Taşı Yüzüğü', 'Boşluk Tacının Yüzüğü'] },
    { key: 'mainhand', slot: 'mainhand', icon: 'weapon', name: 'Ana Silah', names: ['Kurt Dişi Kılıcı', 'Ayaz Yarığı', 'Akrep İğnesi', 'Son Işık Bıçağı'] },
    { key: 'pants', slot: 'pants', icon: 'pants', name: 'Pantolon', names: ['Gezgin Deri Pantolon', 'Buzul Gezgin Pantolonu', 'Kum Gölgesi Pantolonu', 'Kadim Muhafız Taytı'] },
    { key: 'offhand', slot: 'offhand', icon: 'shield', name: 'Yan El', names: ['Eski Kabuk Kalkanı', 'Donmuş Kaya Kalkanı', 'Obsidyen Kalkan', 'Goliath’ın Son Duvarı'] },
    { key: 'boots', slot: 'boots', icon: 'boots', name: 'Çizme', names: ['Tilki Adımı Çizmeleri', 'Kar Fırtınası Çizmeleri', 'Kum Avcısı Çizmeleri', 'Gökyüzü Yarığı Çizmeleri'] },
    { key: 'ring2', slot: 'ring', preferredRing: 'ring2', icon: 'ring', name: 'İkinci Yüzük', names: ['Orman Nöbetçisi Yüzüğü', 'Kutup Yıldızı Yüzüğü', 'Kızıl Vaha Yüzüğü', 'Scorpius’un Kara Yüzüğü'] }
  ]);

  const TIER_STATS = Object.freeze([
    { damage: 0.012, armor: 0.012, maxHp: 8, speed: 0.004, critChance: 0.002 },
    { damage: 0.025, armor: 0.024, maxHp: 20, speed: 0.008, critChance: 0.004 },
    { damage: 0.042, armor: 0.04, maxHp: 38, speed: 0.012, critChance: 0.007 },
    { damage: 0.065, armor: 0.062, maxHp: 64, speed: 0.018, critChance: 0.012 }
  ]);
  const SLOT_STAT_KEYS = Object.freeze({
    head: 'maxHp',
    amulet: 'maxHp',
    gloves: 'damage',
    chest: 'armor',
    ring1: 'critChance',
    ring2: 'damage',
    mainhand: 'damage',
    pants: 'armor',
    offhand: 'armor',
    boots: 'speed'
  });

  const ITEMS = Object.freeze(EQUIPMENT_SLOTS.flatMap(slot =>
    Object.keys(RARITIES).map((rarity, tierIndex) => {
      const stats = TIER_STATS[tierIndex];
      const primary = SLOT_STAT_KEYS[slot.key];
      const itemStats = {
        damage: primary === 'damage' ? stats.damage : Math.round(stats.damage * 0.35 * 1000) / 1000,
        armor: primary === 'armor' ? stats.armor : Math.round(stats.armor * 0.35 * 1000) / 1000,
        maxHp: primary === 'maxHp' ? stats.maxHp : Math.round(stats.maxHp * 0.35),
        speed: primary === 'speed' ? stats.speed : Math.round(stats.speed * 0.35 * 1000) / 1000,
        critChance: primary === 'critChance' ? stats.critChance : Math.round(stats.critChance * 0.35 * 1000) / 1000
      };
      return Object.freeze({
        id: `${rarity}_${slot.key}`,
        name: slot.names[tierIndex],
        slot: slot.slot,
        preferredRing: slot.preferredRing || null,
        icon: slot.icon,
        rarity,
        minLevel: RARITIES[rarity].level,
        bossOnly: rarity === 'legendary',
        stats: Object.freeze(itemStats)
      });
    })
  ));

  const ITEM_BY_ID = Object.freeze(Object.fromEntries(ITEMS.map(item => [item.id, item])));
  const DROP_CHANCES = Object.freeze({ mob: 0.1, boss: 0.35 });
  const RARITY_WEIGHTS = Object.freeze({
    mob: Object.freeze({ common: 0.91, rare: 0.075, epic: 0.015 }),
    boss: Object.freeze({ rare: 0.62, epic: 0.32, legendary: 0.06 })
  });

  function rollLoot(level, isBoss, random = Math.random) {
    if (typeof random !== 'function') throw new TypeError('random must be a function');
    const mobLevel = Math.max(1, Math.floor(Number(level) || 1));
    if (random() >= (isBoss ? DROP_CHANCES.boss : DROP_CHANCES.mob)) return null;

    const weights = RARITY_WEIGHTS[isBoss ? 'boss' : 'mob'];
    const eligibleByRarity = Object.keys(weights).map(rarity => ({
      rarity,
      weight: weights[rarity],
      items: ITEMS.filter(item => item.rarity === rarity && item.minLevel <= mobLevel && (isBoss || !item.bossOnly))
    })).filter(entry => entry.items.length > 0);
    const totalWeight = eligibleByRarity.reduce((sum, entry) => sum + entry.weight, 0);
    if (totalWeight <= 0) return null;

    let rarityRoll = random() * totalWeight;
    let selected = eligibleByRarity[eligibleByRarity.length - 1];
    for (const entry of eligibleByRarity) {
      rarityRoll -= entry.weight;
      if (rarityRoll < 0) {
        selected = entry;
        break;
      }
    }
    const itemIndex = Math.min(selected.items.length - 1, Math.floor(random() * selected.items.length));
    return selected.items[itemIndex];
  }

  const catalog = Object.freeze({ ITEMS, ITEM_BY_ID, RARITIES, EQUIPMENT_SLOTS, DROP_CHANCES, RARITY_WEIGHTS, rollLoot });
  if (typeof module !== 'undefined' && module.exports) module.exports = catalog;
  root.FB_LOOT_CATALOG = catalog;
})(typeof window !== 'undefined' ? window : globalThis);
