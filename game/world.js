/* ===========================================================================
   WORLD — grid, tiles, devices, power graph, gas diffusion, Blackboard.
   =========================================================================== */
window.SOP = window.SOP || {};

SOP.World = (() => {
  const W = SOP.GRID_W, H = SOP.GRID_H;
  let tiles = [];          // tiles[y][x]
  let devices = [];        // all placed devices (incl. wall segments? no — walls are tiles)
  let inmates = [];
  let nextDevId = 1;

  const res = Object.assign({}, SOP.RES); // live resource counts

  /* ---------------- THE BLACKBOARD (Cognitive layer) ---------------- */
  const Blackboard = {
    digMarks: [],          // {x, y} tiles ordered for excavation
    hazards: [],           // {x, y, kind:'gas'}
    electricalNodes: [],   // mirrors devices
    registerNode(dev) { this.electricalNodes.push(dev); },
    postDigMark(x, y) {
      if (!this.digMarks.some(m => m.x === x && m.y === y)) this.digMarks.push({ x, y });
    },
    removeDigMark(x, y) {
      this.digMarks = this.digMarks.filter(m => !(m.x === x && m.y === y));
    },
  };

  /* ---------------- WORLD GENERATION ---------------- */
  function makeTile(t) {
    return { t, obj: null, o2: t === 'empty' ? 96 : 0, gas: 0, mark: false, lit: false, pocket: false };
  }

  function generate() {
    tiles = [];
    for (let y = 0; y < H; y++) {
      const row = [];
      for (let x = 0; x < W; x++) {
        let t = 'dirt';
        if (y < SOP.DIG_TOP || y === H - 1 || x === 0 || x === W - 1) t = 'bedrock';
        row.push(makeTile(t));
      }
      tiles.push(row);
    }

    // HAB block
    carve(3, 6, 15, 12);
    // corridor
    carve(16, 9, 20, 10);
    // TECHNIK block
    carve(21, 7, 29, 13);

    // hidden gas pockets in the dirt (revealed by digging)
    let pockets = 0;
    for (let tries = 0; tries < 400 && pockets < 14; tries++) {
      const x = 2 + Math.floor(Math.random() * (W - 4));
      const y = SOP.DIG_TOP + 1 + Math.floor(Math.random() * (H - SOP.DIG_TOP - 3));
      if (tiles[y][x].t === 'dirt') { tiles[y][x].pocket = true; pockets++; }
    }

    devices = [];
    Blackboard.digMarks = [];
    Blackboard.hazards = [];
    Blackboard.electricalNodes = [];
    nextDevId = 1;

    // starting devices
    const d = placeDevice('dynamo', 5, 7);
    const l1 = placeDevice('lamp', 8, 7);
    const l2 = placeDevice('lamp', 13, 10);
    const b1 = placeDevice('bed', 4, 11);
    const b2 = placeDevice('bed', 6, 11);
    const disp = placeDevice('dispenser', 11, 7);
    const scr = placeDevice('scrubber', 27, 11);
    const gen = placeDevice('generator', 24, 8);
    const vent = placeDevice('gas_vent', 28, 12);
    Blackboard.hazards.push({ x: 28, y: 12, kind: 'gas' });

    // pre-wired starter grid (the lesson)
    addLink(d, l1); addLink(l1, disp); addLink(disp, l2);
    addLink(gen, scr);

    // standing excavation orders so the shift starts moving
    [[14, 13], [15, 13], [16, 13], [22, 14], [23, 14]].forEach(([x, y]) => orderDig(x, y));
  }

  function carve(x1, y1, x2, y2) {
    for (let y = y1; y <= y2; y++)
      for (let x = x1; x <= x2; x++)
        tiles[y][x] = makeTile('empty');
  }

  /* ---------------- DEVICES ---------------- */
  function placeDevice(kind, x, y) {
    const dev = {
      id: nextDevId++, kind, x, y,
      links: [],            // device ids
      powered: false, broken: false, enabled: true, compDeficit: 0, hold: 0,
      operatedBy: null,     // inmate id (dynamo)
      fuelTimer: 0, fueled: true, // generator: starts with one free tank
      charge: 0,              // battery
      growth: 0,              // farm
      open: false,          // door
      triggered: false,     // sensor
      digProgress: 0, repairProgress: 0,
    };
    devices.push(dev);
    tiles[y][x].obj = dev;
    Blackboard.registerNode(dev);
    return dev;
  }

  function removeDevice(dev) {
    const i = devices.indexOf(dev);
    if (i >= 0) devices.splice(i, 1);
    devices.forEach(d => { d.links = d.links.filter(id => id !== dev.id); });
    if (tiles[dev.y][dev.x].obj === dev) tiles[dev.y][dev.x].obj = null;
  }

  function addLink(a, b) {
    if (!a || !b || a === b) return false;
    const dist = Math.abs(a.x - b.x) + Math.abs(a.y - b.y);
    if (dist > SOP.LINK_RANGE) return false;
    if (!a.links.includes(b.id)) a.links.push(b.id);
    if (!b.links.includes(a.id)) b.links.push(a.id);
    return true;
  }

  function removeLink(a, b) {
    a.links = a.links.filter(id => id !== b.id);
    b.links = b.links.filter(id => id !== a.id);
  }

  function linksPairs() {
    const seen = new Set(), pairs = [];
    for (const d of devices) for (const id of d.links) {
      const key = Math.min(d.id, id) + ':' + Math.max(d.id, id);
      if (seen.has(key)) continue;
      seen.add(key);
      const other = devices.find(o => o.id === id);
      if (other) pairs.push([d, other]);
    }
    return pairs;
  }

  /* Build / order actions used by the UI. Returns error string or null. */
  function canBuildAt(kind, x, y) {
    if (!inGrid(x, y)) return 'AUSSERHALB SEKTOR';
    const tl = tiles[y][x];
    if (kind === 'airlock') {
      if (y !== SOP.DIG_TOP - 1) return 'SCHLEUSE NUR AN DER DECKE (REIHE ' + (SOP.DIG_TOP - 1) + ')';
      if (tl.obj) return 'BEREITS BELEGT';
      if (devices.some(d => d.kind === 'airlock')) return 'NUR EINE SCHLEUSE PRO SEKTOR';
      const below = inGrid(x, y + 1) ? tiles[y + 1][x] : null;
      if (!below || below.t !== 'empty') return 'KEIN ZUGANG UNTER DER SCHLEUSE (FELD DARUNTER FREIGRABEN)';
      if (below.obj) return 'ZUGANG BLOCKIERT';
      return null;
    }
    if (tl.t !== 'empty') return 'NUR IN HOHLRÄUMEN';
    if (tl.obj) return 'BEREITS BELEGT';
    if (inmates.some(i => !i.dead && i.tx === x && i.ty === y)) return 'SUBJEKT IM WEG';
    return null;
  }

  function tryBuild(kind, x, y) {
    const err = canBuildAt(kind, x, y);
    if (err) return { ok: false, err };
    const cost = SOP.OBJ[kind].cost || {};
    for (const k in cost) if ((res[k] || 0) < cost[k]) return { ok: false, err: 'MATERIAL FEHLT: ' + k.toUpperCase() };
    for (const k in cost) res[k] -= cost[k];
    placeDevice(kind, x, y);
    return { ok: true };
  }

  function tryBuildWall(x, y) {
    if (!inGrid(x, y)) return { ok: false, err: 'AUSSERHALB SEKTOR' };
    const tl = tiles[y][x];
    if (tl.t !== 'empty') return { ok: false, err: 'NUR IN HOHLRÄUMEN' };
    if (tl.obj) return { ok: false, err: 'BEREITS BELEGT' };
    if (inmates.some(i => !i.dead && i.tx === x && i.ty === y)) return { ok: false, err: 'SUBJEKT IM WEG' };
    if ((res.beton || 0) < SOP.WALL_COST.beton) return { ok: false, err: 'BETON FEHLT' };
    res.beton -= SOP.WALL_COST.beton;
    tl.t = 'wall';
    return { ok: true };
  }

  function orderDig(x, y) {
    if (!inGrid(x, y) || tiles[y][x].t !== 'dirt') return false;
    Blackboard.postDigMark(x, y);
    tiles[y][x].mark = true;
    return true;
  }

  /* Complete one tile of excavation (called by AI). */
  function completeDig(x, y, digger) {
    const tl = tiles[y][x];
    tl.t = 'empty'; tl.mark = false; tl.o2 = 60;
    Blackboard.removeDigMark(x, y);
    let event = null;
    if (tl.pocket) {
      // trapped gas pocket: one violent burst, then it dissipates
      tl.gas = 70;
      tl.pocket = false;
      Blackboard.hazards.push({ x, y, kind: 'gas' });
      event = { type: 'gas', x, y };
    } else if (Math.random() < SOP.DIG_CACHE_CHANCE) {
      const totalW = SOP.CACHES.reduce((a, c) => a + c.weight, 0);
      let roll = Math.random() * totalW, c = SOP.CACHES[0];
      for (const cand of SOP.CACHES) { roll -= cand.weight; if (roll <= 0) { c = cand; break; } }
      const n = c.n[0] + Math.floor(Math.random() * (c.n[1] - c.n[0] + 1));
      res[c.res] = (res[c.res] || 0) + n;
      event = { type: 'cache', label: c.label, n, res: c.res };
    }
    return event;
  }

  /* ---------------- POWER EVALUATION ---------------- */
  let powerState = { gen: 0, draw: 0, stored: 0, components: 0, deficit: 0 };

  function evalPower() {
    // union-find over links
    const parent = new Map();
    devices.forEach(d => parent.set(d.id, d.id));
    const find = (a) => { while (parent.get(a) !== a) { parent.set(a, parent.get(parent.get(a))); a = parent.get(a); } return a; };
    for (const d of devices) for (const id of d.links) {
      if (!parent.has(id)) continue;
      const ra = find(d.id), rb = find(id);
      if (ra !== rb) parent.set(ra, rb);
    }
    const comps = new Map();
    for (const d of devices) {
      const r = find(d.id);
      if (!comps.has(r)) comps.set(r, []);
      comps.get(r).push(d);
    }

    let gen = 0, draw = 0, stored = 0;
    for (const [, members] of comps) {
      let cGen = 0, cDraw = 0;
      const batteries = [];
      for (const d of members) {
        if (d.kind === 'battery') {
          if (d.enabled !== false && !d.broken) batteries.push(d);
          continue;
        }
        if (d.broken || d.enabled === false) continue;
        const w = SOP.OBJ[d.kind].watts || 0;
        if (w < 0) {
          if (d.kind === 'dynamo') {
            if (d.operatedBy != null) cGen += -w;
          } else {
            if (d.kind === 'generator' && d.fueled === false) { /* out of rations */ }
            else cGen += -w;
          }
        } else if (w > 0) {
          cDraw += w;
        }
      }
      const need = cDraw - cGen;
      let ok;
      if (need <= 0) {
        ok = true;
        let surplus = -need;                     // charge the pack
        for (const b of batteries) {
          const room = SOP.BATTERY_CAP - b.charge;
          const c = Math.min(room, surplus);
          b.charge += c; surplus -= c;
          if (surplus <= 0) break;
        }
      } else {
        let avail = 0;                           // discharge to cover the gap
        for (const b of batteries) {
          const c = Math.min(b.charge, need - avail);
          b.charge -= c; avail += c;
          if (avail >= need) break;
        }
        ok = avail >= need;
      }
      const compDeficit = Math.max(0, cDraw - cGen);
      for (const d of members) {
        // relay hold: consumers ride through brief generation gaps (20 ticks)
        let effOk = ok;
        if (effOk) d.hold = 20;
        else if (d.hold > 0) { d.hold--; effOk = true; }
        d.powered = effOk && !d.broken && d.enabled !== false;
        d.compDeficit = compDeficit;   // per-grid shortfall, drives the crank urge
      }
      for (const b of batteries) stored += b.charge;
      gen += cGen;
      draw += cDraw;
    }
    powerState = { gen, draw, stored, components: comps.size, deficit: Math.max(0, draw - gen) };
    return powerState;
  }

  /* ---------------- GAS / O2 DIFFUSION ---------------- */
  function diffuse() {
    const k = 0.20;
    const nO2 = [], nGas = [];
    for (let y = 0; y < H; y++) { nO2.push(new Array(W).fill(0)); nGas.push(new Array(W).fill(0)); }
    for (let y = 0; y < H; y++) {
      for (let x = 0; x < W; x++) {
        const tl = tiles[y][x];
        if (tl.t !== 'empty') continue;
        let o2 = tl.o2, gas = tl.gas, cnt = 0;
        let accO = 0, accG = 0;
        for (const [dx, dy] of [[1,0],[-1,0],[0,1],[0,-1]]) {
          const nx = x + dx, ny = y + dy;
          if (nx < 0 || ny < 0 || nx >= W || ny >= H) continue;
          const nb = tiles[ny][nx];
          if (nb.t !== 'empty') continue;
          accO += (nb.o2 - o2); accG += (nb.gas - gas); cnt++;
        }
        // proportional blend toward neighborhood average
        if (cnt > 0) { o2 = tl.o2 + k * accO / cnt; gas = tl.gas + k * accG / cnt; }
        nO2[y][x] = o2; nGas[y][x] = gas;
      }
    }
    for (let y = 0; y < H; y++) for (let x = 0; x < W; x++) {
      if (tiles[y][x].t !== 'empty') continue;
      tiles[y][x].o2 = clamp(nO2[y][x], 0, 100);
      tiles[y][x].gas = clamp(nGas[y][x], 0, 100);
    }
  }

  /* ---------------- TICK ---------------- */
  function tick(onEvent) {
    // devices act
    for (const d of devices) {
      if (d.kind === 'gas_vent' && !d.broken) {
        tiles[d.y][d.x].gas = Math.min(100, tiles[d.y][d.x].gas + 4);
      }
      if (d.kind === 'scrubber' && d.powered && !d.broken && d.enabled !== false) {
        for (let dy = -1; dy <= 1; dy++) for (let dx = -1; dx <= 1; dx++) {
          const x = d.x + dx, y = d.y + dy;
          if (!inGrid(x, y) || tiles[y][x].t !== 'empty') continue;
          tiles[y][x].gas = Math.max(0, tiles[y][x].gas - 5);
          tiles[y][x].o2 = Math.min(100, tiles[y][x].o2 + 1.2);
        }
      }
      if (d.kind === 'generator' && !d.broken && d.enabled !== false) {
        d.fuelTimer = (d.fuelTimer || 0) + 1;
        if (d.fuelTimer >= 140) {           // burns 1 ÖL every 140 ticks (35 s)
          if (res.oel > 0) {
            res.oel--; d.fuelTimer = 0; d.fueled = true;
            onEvent({ type: 'burn', dev: d });
          } else {
            d.fueled = false;
          }
        }
      }
      if (d.kind === 'sensor' && d.powered && !d.broken && d.enabled !== false) {
        d.triggered = inmates.some(i => !i.dead && Math.abs(i.tx - d.x) + Math.abs(i.ty - d.y) <= 2);
        // coupled doors open while triggered
        for (const id of d.links) {
          const o = devices.find(x => x.id === id);
          if (o && o.kind === 'door') o.open = d.triggered;
        }
      }
      if (d.kind === 'farm' && d.powered && !d.broken && d.enabled !== false) {
        d.growth = (d.growth || 0) + 1;
        if (d.growth >= SOP.FARM_TICKS) {
          d.growth = 0;
          res.rationen++;
          onEvent({ type: 'harvest', dev: d });
        }
      }
      if (d.kind === 'door' && d.enabled === false) { d.open = false; continue; }
      if (d.kind === 'door' && d.powered) d.open = true;
      else if (d.kind === 'door' && !d.powered) {
        const sensorHolds = d.links.some(id => {
          const s = devices.find(x => x.id === id);
          return s && s.kind === 'sensor' && s.triggered;
        });
        if (!sensorHolds) d.open = false;
      }
    }

    evalPower();

    // inmates breathe their tile
    for (const inm of inmates) {
      if (inm.dead) continue;
      const tl = tiles[inm.ty][inm.tx];
      tl.o2 = Math.max(0, tl.o2 - 0.35);
    }

    diffuse();
    updateLighting();
  }

  function updateLighting() {
    for (let y = 0; y < H; y++) for (let x = 0; x < W; x++) tiles[y][x].lit = false;
    for (const d of devices) {
      if (d.kind !== 'lamp' || !d.powered || d.broken || d.enabled === false) continue;
      for (let y = d.y - 4; y <= d.y + 4; y++) for (let x = d.x - 4; x <= d.x + 4; x++) {
        if (!inGrid(x, y) || tiles[y][x].t !== 'empty') continue;
        if (Math.abs(x - d.x) + Math.abs(y - d.y) <= 5) tiles[y][x].lit = true;
      }
    }
  }

  /* ---------------- PATHFINDING ---------------- */
  function walkable(x, y) {
    if (!inGrid(x, y)) return false;
    const tl = tiles[y][x];
    if (tl.t !== 'empty') return false;
    if (tl.obj && tl.obj.kind === 'door' && !tl.obj.open) return false;
    if (tl.obj && tl.obj.kind !== 'lamp' && tl.obj.kind !== 'sensor') return false;
    return true;
  }

  function findPath(sx, sy, tx, ty) {
    if (!inGrid(tx, ty)) return null;
    if (sx === tx && sy === ty) return [];
    // target tile itself may be an object tile -> allow if adjacent goal
    const key = (x, y) => y * W + x;
    const prev = new Map();
    const q = [[sx, sy]];
    prev.set(key(sx, sy), null);
    while (q.length) {
      const [x, y] = q.shift();
      if (x === tx && y === ty) {
        const path = [];
        let cur = [x, y];
        while (cur) { path.unshift(cur); cur = prev.get(key(cur[0], cur[1])); }
        path.shift();
        return path;
      }
      for (const [dx, dy] of [[1,0],[-1,0],[0,1],[0,-1]]) {
        const nx = x + dx, ny = y + dy;
        if (prev.has(key(nx, ny))) continue;
        if (nx === tx && ny === ty) {
          // allow stepping onto the goal even if occupied by an object
          prev.set(key(nx, ny), [x, y]);
          q.push([nx, ny]);
          continue;
        }
        if (!walkable(nx, ny)) continue;
        prev.set(key(nx, ny), [x, y]);
        q.push([nx, ny]);
      }
    }
    return null;
  }

  /* Nearest lit tile to (x,y). */
  function nearestLit(x, y) {
    let best = null, bd = Infinity;
    for (let yy = 0; yy < H; yy++) for (let xx = 0; xx < W; xx++) {
      const tl = tiles[yy][xx];
      if (tl.t !== 'empty' || !tl.lit) continue;
      const d = Math.abs(xx - x) + Math.abs(yy - y);
      if (d < bd) { bd = d; best = { x: xx, y: yy }; }
    }
    return best;
  }

  /* ---------------- SAVE / LOAD ---------------- */
  function serialize() {
    return {
      res: Object.assign({}, res),
      nextDevId,
      tiles: tiles.map(row => row.map(tl => ({
        t: tl.t, o2: Math.round(tl.o2), gas: Math.round(tl.gas),
        m: tl.mark ? 1 : 0, p: tl.pocket ? 1 : 0,
      }))),
      devices: devices.map(d => ({
        id: d.id, kind: d.kind, x: d.x, y: d.y,
        links: d.links.slice(), broken: d.broken, enabled: d.enabled,
        charge: Math.round(d.charge || 0), growth: d.growth || 0,
        fuelTimer: d.fuelTimer || 0, fueled: d.fueled !== false,
        open: !!d.open, operatedBy: d.operatedBy,
      })),
      digMarks: Blackboard.digMarks.map(m => ({ x: m.x, y: m.y })),
    };
  }

  function loadFrom(data) {
    tiles = data.tiles.map(row => row.map(o => {
      const tl = makeTile(o.t);
      tl.o2 = o.o2; tl.gas = o.gas; tl.mark = !!o.m; tl.pocket = !!o.p;
      return tl;
    }));
    devices = [];
    Blackboard.digMarks = [];
    Blackboard.hazards = [];
    Blackboard.electricalNodes = [];
    nextDevId = data.nextDevId || 1;
    for (const o of data.devices) {
      const dev = {
        links: [], powered: false, broken: false, enabled: true,
        compDeficit: 0, hold: 0, operatedBy: null,
        fuelTimer: 0, fueled: true, charge: 0, growth: 0,
        open: false, triggered: false, digProgress: 0, repairProgress: 0,
      };
      Object.assign(dev, o);
      devices.push(dev);
      if (inGrid(dev.x, dev.y)) tiles[dev.y][dev.x].obj = dev;
      Blackboard.registerNode(dev);
      if (dev.kind === 'gas_vent') Blackboard.hazards.push({ x: dev.x, y: dev.y, kind: 'gas' });
    }
    for (const k in res) delete res[k];
    Object.assign(res, data.res);
    for (const m of data.digMarks || []) {
      if (inGrid(m.x, m.y) && tiles[m.y][m.x].t === 'dirt') {
        Blackboard.postDigMark(m.x, m.y);
        tiles[m.y][m.x].mark = true;
      }
    }
    evalPower();
    updateLighting();
  }

  /* ---------------- helpers / API ---------------- */
  function inGrid(x, y) { return x >= 0 && y >= 0 && x < W && y < H; }
  function clamp(v, a, b) { return Math.max(a, Math.min(b, v)); }

  return {
    get tiles() { return tiles; },
    get devices() { return devices; },
    get inmates() { return inmates; },
    set inmates(v) { inmates = v; },
    get res() { return res; },
    get power() { return powerState; },
    Blackboard,
    generate, placeDevice, removeDevice, addLink, removeLink, linksPairs,
    tryBuild, tryBuildWall, canBuildAt, orderDig, completeDig,
    tick, evalPower, walkable, findPath, nearestLit, inGrid,
    serialize, loadFrom,
    W, H,
  };
})();
