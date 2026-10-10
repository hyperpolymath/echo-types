/* Headless smoke test: runs the real simulation (world + AI) without a DOM.
   Usage: node game/tools/smoke.js [ticks] */
global.window = global;
require('../config.js');
require('../world.js');
require('../ai.js');

const world = SOP.World;
const ticks = parseInt(process.argv[2] || '4000', 10);

world.generate();
const traits = ['Pyromane', 'Paranoid', 'Befehlsfixiert'];
const spots = [[7, 9], [10, 8], [13, 11]];
world.inmates = spots.map((s, i) => new SOP.InmateAI('SUBJEKT-' + (400 + i), traits[i], s[0], s[1]));

const events = {};
const count = t => { events[t] = (events[t] || 0) + 1; };
const smokeState = {};

const actHist = {};
let nextQuakeTick = 600;
function quake(t) {
  const fragile = world.devices.filter(d => d.kind !== 'gas_vent' && !d.broken);
  const hits = 1 + (Math.random() < 0.4 ? 1 : 0);
  for (let i = 0; i < hits && fragile.length; i++) {
    const idx = Math.floor(Math.random() * fragile.length);
    const d = fragile.splice(idx, 1)[0];
    d.broken = true;
    console.log(`[t=${t}] QUAKE breaks ${d.kind} @ (${d.x},${d.y})`);
  }
  world.inmates.forEach(i => {
    if (i.dead) return;
    i.affective.stress = Math.min(100, i.affective.stress + 12);
    i.affective.paranoia = Math.min(100, i.affective.paranoia + (i.trait === 'Paranoid' ? 22 : 8));
    i.sleeping = false;
  });
}
for (let t = 0; t < ticks; t++) {
  if (t >= nextQuakeTick) { quake(t); nextQuakeTick = t + 380 + Math.floor(Math.random() * 260); }
  if (t % 1000 === 0) {
    const stale = world.Blackboard.digMarks.filter(m => {
      if (world.tiles[m.y][m.x].t !== 'dirt') return true;
      return ![[1,0],[-1,0],[0,1],[0,-1]].some(([dx,dy]) => world.walkable(m.x+dx, m.y+dy));
    }).length;
    const emptyNow = world.tiles.flat().filter(x => x.t === 'empty').length;
    console.log(`  [dig t=${t}] marks=${world.Blackboard.digMarks.length} stale=${stale} empty=${emptyNow}`);
    const alive = world.inmates.filter(i => !i.dead);
    const habGas = world.tiles[9][9].gas.toFixed(1), techGas = world.tiles[10][25].gas.toFixed(1);
    const vents = world.devices.filter(d => d.kind === 'gas_vent').map(v => `${v.x},${v.y}`).join(' ');
    console.log(`[t=${t}] marks=${world.Blackboard.digMarks.length} alive=${alive.length} ` +
      alive.map(i => `${i.name.split('-')[1]}:${i.currentAction.name}`).join(' ') +
      ` habGas=${habGas} techGas=${techGas} vents=[${vents}]`);
  }
  world.tick(e => { count('world:' + e.type); if (e.type === 'harvest') smokeState.harvests = (smokeState.harvests || 0) + 1; });
  for (const inm of world.inmates) {
    if (inm.dead) continue;
    if (t % 4 === 0) {
      inm.evaluateDrives(world);
      actHist[inm.currentAction.name] = (actHist[inm.currentAction.name] || 0) + 1;
    }
    const wasDead = inm.dead;
    inm.tick(world, e => {
      count(e.type);
      // bursts are transient; no countermove needed beyond avoiding the tile
      if (e.type === 'gasburst') console.log('[autopilot] gas burst @', t, e.x, e.y);
    });
    if (!wasDead && inm.dead) console.log(`[t=${t}] DEATH ${inm.name} (${inm.deadCause}) h=${inm.affective.hunger.toFixed(0)} xh=${inm.affective.exhaustion.toFixed(0)} o2=${inm.affective.o2.toFixed(0)} pos=${inm.tx},${inm.ty}`);
  }
  // player simulation: keep 10 frontier dig marks adjacent to open space
  if (t % 60 === 0) {
    const marks = world.Blackboard.digMarks.length;
    let need = 10 - marks;
    const frontier = [];
    for (let y = SOP.DIG_TOP; y < world.H - 1 && need > 0; y++) for (let x = 1; x < world.W - 1; x++) {
      if (world.tiles[y][x].t !== 'dirt') continue;
      if ([[1,0],[-1,0],[0,1],[0,-1]].some(([dx, dy]) => world.tiles[y + dy][x + dx].t === 'empty' && !world.tiles[y + dy][x + dx].obj)) {
        frontier.push([x, y]);
      }
    }
    while (need-- > 0 && frontier.length) {
      const i = Math.floor(Math.random() * frontier.length);
      const [x, y] = frontier.splice(i, 1)[0];
      world.orderDig(x, y);
    }
  }
  // redundancy: a second Ausgabe so one quake can't cut off all food
  if (t === 2000 && !smokeState.disp2) {
    for (const [x, y] of [[14, 8], [13, 8], [14, 9], [12, 10]]) {
      if (world.tryBuild('dispenser', x, y).ok) {
        const dp = world.devices.find(d => d.kind === 'dispenser' && d.x === x && d.y === y);
        const l1 = world.devices.find(d => d.kind === 'lamp' && d.x === 8);
        world.addLink(dp, l1);
        smokeState.disp2 = true;
        console.log('[autopilot] dispenser-2 built+wired @', t);
        break;
      }
    }
  }

  // ===== autopilot build order (a competent Schichtleiter) =====
  const linkAnchor = () => world.devices.find(d => d.kind === 'lamp' && d.x === 8); // HAB Lampe 1
  const buildAndWire = (kind, spots, tag) => {
    for (const [x, y] of spots) {
      if (world.tryBuild(kind, x, y).ok) {
        const dev = world.devices.find(d => d.kind === kind && d.x === x && d.y === y);
        world.addLink(dev, linkAnchor());
        console.log(`[autopilot] ${tag} @ (${x},${y}) t=${t}`);
        return true;
      }
    }
    return false;
  };

  // 1) food: farm one
  if (!smokeState.farm1 && t > 240 && t % 25 === 0) {
    if (buildAndWire('farm', [[9, 6], [12, 6], [14, 6], [10, 8], [9, 8], [7, 6]], 'FARM-1')) smokeState.farm1 = true;
  }
  // 2) baseload power: an ÖL generator inside HAB; retire the TECHNIK pair
  if (!smokeState.habGen && t > 400 && t % 25 === 0) {
    if (buildAndWire('generator', [[10, 6], [9, 9], [12, 8], [14, 8], [7, 8]], 'GENERATOR (HAB)')) {
      smokeState.habGen = true;
      for (const d of world.devices) {
        if (d.x > 20 && (d.kind === 'generator' || d.kind === 'scrubber')) d.enabled = false;
      }
      console.log('[autopilot] TECHNIK grid retired (spart Öl)');
    }
  }
  // 3) air: HAB washer
  if (smokeState.habGen && !smokeState.habScr && t % 25 === 0) {
    if (buildAndWire('scrubber', [[10, 9], [9, 10], [12, 10], [8, 10], [10, 10]], 'WÄSCHER (HAB)')) {
      smokeState.habScr = true;
      smokeState.wallsWanted = smokeState.wallsWanted || [[16, 9], [16, 10], [20, 9], [20, 10]];
    }
  }
  // 4) food scale: farm two
  if (smokeState.habScr && !smokeState.farm2 && t % 25 === 0) {
    if (buildAndWire('farm', [[12, 9], [13, 8], [14, 9], [13, 6], [7, 10]], 'FARM-2')) smokeState.farm2 = true;
  }
  // 5) buffer battery against quake knock-outs
  if (t > 300 && !smokeState.battery) {
    const dyn = world.devices.find(d => d.kind === 'dynamo');
    for (const [dx, dy] of [[1,0],[-1,0],[0,1],[0,-1],[1,1],[-1,1],[2,0],[0,2]]) {
      const r = world.tryBuild('battery', dyn.x + dx, dyn.y + dy);
      if (r.ok) {
        const bat = world.devices.find(d => d.kind === 'battery');
        world.addLink(bat, linkAnchor());
        smokeState.battery = true;
        console.log('[autopilot] AKKU built+wired @', t);
        break;
      }
    }
  }

  // retry corridor walls until sealed (subjects may stand in the way)
  if (smokeState.wallsWanted && smokeState.wallsWanted.length && t % 10 === 0) {
    smokeState.wallsWanted = smokeState.wallsWanted.filter(([x, y]) => {
      if (world.tiles[y][x].t === 'wall') return false;
      const r = world.tryBuildWall(x, y);
      if (r.ok) console.log('[autopilot] wall sealed', x, y, '@', t);
      return !r.ok;
    });
  }
}

// report
const empty = world.tiles.flat().filter(t => t.t === 'empty').length;
const avgO2 = world.tiles.flat().filter(t => t.t === 'empty').reduce((a, t) => a + t.o2, 0) / Math.max(1, empty);
const avgGas = world.tiles.flat().filter(t => t.t === 'empty').reduce((a, t) => a + t.gas, 0) / Math.max(1, empty);

console.log('=== SMOKE REPORT ===');
console.log('ticks:', ticks);
console.log('inmates:', world.inmates.map(i => `${i.name} ${i.dead ? 'DEAD(' + i.deadCause + ')' : 'alive'} hunger=${i.affective.hunger.toFixed(0)} stress=${i.affective.stress.toFixed(0)} o2need=${i.affective.o2.toFixed(0)} act=${i.currentAction.name}`).join('\n  '));
console.log('power:', JSON.stringify(world.power));
console.log('res:', JSON.stringify(world.res));
console.log('empty tiles:', empty, '| avg O2:', avgO2.toFixed(1), '| avg gas:', avgGas.toFixed(2));
console.log('dig marks left:', world.Blackboard.digMarks.length);
console.log('devices:', world.devices.length, '| links:', world.linksPairs().length);
console.log('events:', JSON.stringify(events));
console.log('action histogram:', JSON.stringify(actHist));
console.log('actions seen:', [...new Set(world.inmates.map(i => i.currentAction.name))].join(', '));
console.log('=== SMOKE OK (no exceptions) ===');
