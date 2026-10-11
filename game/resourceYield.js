(function(root) {
  'use strict';

  function calculateResourceYield(type, tool, tier) {
    const safeTier = Math.max(0, Math.min(2, Math.floor(Number(tier) || 0)));
    const baseAmount = (tool === 'axe' ? 2 : 1) * (2 ** safeTier);
    const resources = { wood: 0, stone: 0, gold: 0, diamond: 0, amethyst: 0, redite: 0 };

    switch (type) {
      case 'wood':
      case 'apple':
      case 'bush':
        resources.wood = baseAmount;
        break;
      case 'stone':
        resources.stone = baseAmount;
        break;
      case 'gold':
      case 'mushroom':
      case 'hive':
        resources.gold = baseAmount;
        resources.stone = baseAmount;
        break;
      case 'diamond':
        if (tool === 'axe') resources.diamond = 1;
        break;
      case 'amethyst':
        if (tool === 'axe') resources.amethyst = 1;
        break;
      case 'redite':
        if (tool === 'axe') resources.redite = 1;
        break;
      default:
        resources.wood = baseAmount;
        break;
    }
    return resources;
  }

  const api = Object.freeze({ calculateResourceYield });
  if (typeof module !== 'undefined' && module.exports) module.exports = api;
  root.FB_RESOURCE_YIELD = api;
})(typeof window !== 'undefined' ? window : globalThis);
