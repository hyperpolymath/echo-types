/* ===========================================================================
   CONATIVE UTILITY AI — inmates score every possible action against their
   Affective state (needs/emotions) and pick the highest-scoring directive.
   Movement is grid path-following; interaction happens on arrival.
   =========================================================================== */
window.SOP = window.SOP || {};

SOP.InmateAI = class InmateAI {
  constructor(name, trait, x, y) {
    this.name = name;
    this.trait = trait;
    // desynchronized metabolisms so the crew never all drop the cranks at once
    this.hungerRate = 0.20 + Math.random() * 0.05;
    this.affective = {
      stress: 15 + Math.random() * 15,
      paranoia: 5 + Math.random() * 15,
      hunger: 30 + Math.random() * 35,
      exhaustion: 5 + Math.random() * 20,
      o2: 0,
    };
    this.hp = 100;
    this.tx = x; this.ty = y;        // tile position
    this.px = x; this.py = y;        // pixel-lerp position (float tiles)
    this.path = [];
    this.currentAction = { name: 'IDLE', score: 0 };
    this.goal = null;                 // {kind:'device'|'tile', ...}
    this.progress = 0;
    this.dead = false;
    this.deadCause = '';
    this.sleeping = false;
    this.nextEval = 0;
    this.sayCooldown = 0;
    this.thought = '—';
    this.walkPhase = Math.random() * 6.28;
    this.id = name;
  }

  /* ---------------- UTILITY EVALUATOR ---------------- */
  evaluateDrives(world) {
    if (this.dead) return;
    const A = this.affective;
    const cand = [];
    const push = (name, score, goal) => { if (score > 0) cand.push({ name, score, goal }); };

    // broken infrastructure survey (drives both repair and crank decisions)
    const brokenAll = world.devices.filter(d => d.broken && d.kind !== 'gas_vent');
    const gridBroken = brokenAll.some(d => this.onDispenserGrid(world, d));

    // --- EAT ---
    let eatScore = A.hunger > 70 ? A.hunger * 1.5 : A.hunger;
    const dispenser = this.nearestDevice(world, d => d.kind === 'dispenser' && !d.broken && d.powered);
    const dispenserAny = dispenser || this.nearestDevice(world, d => d.kind === 'dispenser' && !d.broken);
    if (world.res.rationen <= 0 || !dispenser) eatScore = 0;
    push('ESSEN FASSEN', eatScore, dispenser ? { kind: 'device', dev: dispenser, act: 'eat' } : null);

    // --- SLEEP ---
    let sleepScore = A.exhaustion > 75 ? A.exhaustion * 1.3 : A.exhaustion * 0.7;
    const bed = this.nearestDevice(world, d => d.kind === 'bed' && !d.broken &&
      !world.inmates.some(i => i !== this && !i.dead && i.goal && i.goal.dev === d && i.sleeping));
    if (bed) push('SCHLAFEN', sleepScore, { kind: 'device', dev: bed, act: 'sleep' });
    else if (A.exhaustion > 60) push('SCHLAFEN (BODEN)', sleepScore * 0.8, { kind: 'tile', x: this.tx, y: this.ty, act: 'sleep' });

    // --- CRANK DYNAMO (sticky: hold the cranks until exhausted) ---
    const p = world.power;
    if (this.goal && this.goal.act === 'crank' && this.goal.dev &&
        !this.goal.dev.broken && this.goal.dev.operatedBy === this.id &&
        A.exhaustion < 85) {
      push('KURBELN', 95, this.goal);
    } else if (A.exhaustion < 80 || A.hunger > 85) {
      // hunger > 85: desperate cranking — starvation overrides exhaustion
      const dyn = this.nearestDevice(world, d => d.kind === 'dynamo' && !d.broken && d.operatedBy == null && d.compDeficit > 0);
      if (dyn) {
        let crankScore = 62 + Math.min(30, dyn.compDeficit * 0.4) - A.exhaustion * 0.4;
        // a hungry inmate powers the dispenser before trying to eat —
        // but if the food grid is broken, repairing beats cranking
        if (dispenserAny && dispenserAny.compDeficit > 0 && !gridBroken) {
          if (A.hunger > 85) crankScore += 120;     // starving override — beats sleep
          else if (A.hunger > 55) crankScore += 40;
        }
        push('KURBELN', crankScore, { kind: 'device', dev: dyn, act: 'crank' });
      }
    }

    // --- DIG (Standard Operating Procedure) ---
    let workScore = 72 - A.stress * 0.35 - A.exhaustion * 0.6;
    if (this.trait === 'Befehlsfixiert') workScore += 25;
    // Blackboard work directive: low stocks order everyone underground
    if (world.res.oel < 100 || world.res.rationen < 60 || world.res.metall < 10) workScore += 35;
    const mark = this.nearestDigMark(world);
    if (mark) {
      // dig momentum: a tile already being excavated gets finished
      if (this.goal && this.goal.act === 'dig' && this.progress > 0) workScore += 40;
      push('GRABEN', workScore, { kind: 'dig', x: mark.x, y: mark.y, act: 'dig' });
    }

    // --- REPAIR ---
    // prioritize broken nodes on the food/power grid over cosmetic fixes
    let broken = null;
    if (brokenAll.length) {
      const crit = brokenAll.filter(d => this.onDispenserGrid(world, d));
      const pool = crit.length ? crit : brokenAll;
      broken = pool.reduce((a, b) =>
        (Math.abs(a.x - this.tx) + Math.abs(a.y - this.ty)) <= (Math.abs(b.x - this.tx) + Math.abs(b.y - this.ty)) ? a : b);
    }
    if (broken) {
      let repairScore = 60 - A.exhaustion * 0.3;
      if (this.onDispenserGrid(world, broken)) repairScore = 210;   // must beat desperate cranking
      push('REPARIEREN', repairScore, { kind: 'device', dev: broken, act: 'repair' });
    }

    // --- FLEE DARKNESS (Paranoia) — capped so hunger can still win ---
    const here = world.tiles[this.ty][this.tx];
    if (!here.lit && here.t === 'empty' && !this.sleeping) {
      let flee = A.paranoia * 1.2;
      if (this.trait === 'Paranoid') flee *= 1.6;
      if (this.trait === 'Befehlsfixiert') flee *= 0.3;
      flee = Math.min(flee, 115);
      const lit = world.nearestLit(this.tx, this.ty);
      if (lit) push('LICHT SUCHEN', flee, { kind: 'tile', x: lit.x, y: lit.y, act: 'flee' });
    }

    // --- AVOID GAS ---
    if (here.gas > 12) {
      const clear = this.nearestClearAir(world);
      if (clear) push('GAS MEIDEN', 92 + here.gas * 0.1, { kind: 'tile', x: clear.x, y: clear.y, act: 'flee' });
    }

    // --- SABOTAGE / PSYCHOTIC BREAK (trait-specific conative override) ---
    if (A.stress >= 85 && this.trait === 'Pyromane') {
      push(`PSYCHOTISCHER SCHUB (${this.trait})`, 100, this.pickSabotageTarget(world));
    }
    if (A.stress >= 92 && this.trait === 'Paranoid') {
      const lit = world.nearestLit(this.tx, this.ty);
      if (lit) push('IN ECKE VERKRIECHEN', 96, { kind: 'tile', x: lit.x, y: lit.y, act: 'hide' });
    }

    // --- WANDER baseline ---
    push('UMHERIRREN', 25, this.randomWanderGoal(world));

    let best = cand[0] || { name: 'IDLE', score: 0, goal: null };
    for (const c of cand) if (c.score > best.score) best = c;

    // commit
    if (best.name !== this.currentAction.name || !this.goal) {
      this.currentAction = { name: best.name, score: best.score };
      this.goal = best.goal;
      this.sleeping = false;
      this.progress = 0;
      this.path = [];
      this.waitTicks = 0;
      this.thought = this.thoughtFor(best.name);
    }
    this.logConativeState(best);
  }

  /* Is this device on the same wired component as any dispenser? */
  onDispenserGrid(world, dev) {
    const starts = world.devices.filter(d => d.kind === 'dispenser');
    if (!starts.length) return false;
    const seen = new Set(starts.map(d => d.id));
    const q = [...starts];
    while (q.length) {
      const d = q.pop();
      for (const id of d.links) {
        if (seen.has(id)) continue;
        seen.add(id);
        const o = world.devices.find(x => x.id === id);
        if (o) q.push(o);
      }
    }
    return seen.has(dev.id);
  }

  pickSabotageTarget(world) {
    const linked = world.devices.filter(d => d.links.length > 0 && d.kind !== 'gas_vent');
    if (!linked.length) return null;
    const d = linked[Math.floor(Math.random() * linked.length)];
    return { kind: 'device', dev: d, act: 'sabotage' };
  }

  randomWanderGoal(world) {
    for (let tries = 0; tries < 20; tries++) {
      const x = Math.floor(Math.random() * world.W);
      const y = Math.floor(Math.random() * world.H);
      if (world.walkable(x, y)) return { kind: 'tile', x, y, act: 'wander' };
    }
    return null;
  }

  nearestDevice(world, pred) {
    let best = null, bd = Infinity;
    for (const d of world.devices) {
      if (!pred(d)) continue;
      const dist = Math.abs(d.x - this.tx) + Math.abs(d.y - this.ty);
      if (dist < bd) { bd = dist; best = d; }
    }
    return best;
  }

  nearestDigMark(world) {
    const taken = new Set();
    for (const o of world.inmates) {
      if (o !== this && !o.dead && o.goal && o.goal.act === 'dig') taken.add(o.goal.x + ',' + o.goal.y);
    }
    let best = null, bd = Infinity, bestTaken = null, bdt = Infinity;
    for (const m of world.Blackboard.digMarks) {
      if (world.tiles[m.y][m.x].t !== 'dirt') continue;
      // must be reachable: at least one adjacent walkable tile
      const reach = [[1,0],[-1,0],[0,1],[0,-1]].some(([dx, dy]) => world.walkable(m.x + dx, m.y + dy));
      if (!reach) continue;
      const dist = Math.abs(m.x - this.tx) + Math.abs(m.y - this.ty);
      if (taken.has(m.x + ',' + m.y)) {
        if (dist < bdt) { bdt = dist; bestTaken = m; }
      } else if (dist < bd) { bd = dist; best = m; }
    }
    return best || bestTaken;
  }

  nearestClearAir(world) {
    let best = null, bd = Infinity;
    for (let y = 0; y < world.H; y++) for (let x = 0; x < world.W; x++) {
      const tl = world.tiles[y][x];
      if (tl.t !== 'empty' || tl.gas > 10 || tl.o2 < 30) continue;
      const d = Math.abs(x - this.tx) + Math.abs(y - this.ty);
      if (d < bd) { bd = d; best = { x, y }; }
    }
    return best;
  }

  thoughtFor(action) {
    const T = {
      'ESSEN FASSEN': 'Ausgabe. Jetzt.',
      'SCHLAFEN': 'Die Pritsche ruft.',
      'SCHLAFEN (BODEN)': 'Boden genügt. Boden ist sicher.',
      'KURBELN': 'Strom durch Muskel. SOP.',
      'GRABEN': 'Die Erde gibt nicht freiwillig.',
      'REPARIEREN': 'Es knackt. Es muss ganz.',
      'LICHT SUCHEN': 'Nicht im Dunkeln. Nie wieder dunkel.',
      'GAS MEIDEN': 'Es schmeckt nach Kupfer.',
      'IN ECKE VERKRIECHEN': 'Wände beobachten.',
      'UMHERIRREN': 'Schritte zählen hilft.',
      'EXPEDITION': 'Raus. Nur kurz. Nur mit Maske.',
      'IDLE': '—',
    };
    return T[action] || '—';
  }

  releaseCrank(world) {
    for (const d of world.devices) if (d.operatedBy === this.id) d.operatedBy = null;
  }

  /* ---------------- PER-TICK EXECUTION ---------------- */
  tick(world, onEvent) {
    if (this.dead) return;
    // dynamo ownership sanity: a cranker who switched goals frees the cranks
    if (!this.goal || this.goal.act !== 'crank') this.releaseCrank(world);
    const A = this.affective;
    const tl = world.tiles[this.ty][this.tx];

    // ---- affective drift ----
    A.hunger = Math.min(100, A.hunger + this.hungerRate);
    if (!this.sleeping) A.exhaustion = Math.min(100, A.exhaustion + 0.18);
    if (!tl.lit && tl.t === 'empty' && !this.sleeping) {
      A.stress = Math.min(100, A.stress + 0.15);
      A.paranoia = Math.min(100, A.paranoia + (this.trait === 'Paranoid' ? 0.5 : 0.22));
    } else {
      A.paranoia = Math.max(0, A.paranoia - 0.35);
      A.stress = Math.max(0, A.stress - 0.15);
    }
    // breathing
    if (tl.o2 < 14 || tl.gas > 12) {
      A.o2 = Math.min(100, A.o2 + (tl.gas > 12 ? 2.4 : 1.1));
    } else {
      A.o2 = Math.max(0, A.o2 - 1.4);
    }
    if (A.o2 >= 100) { this.hp -= 2.5; if (this.hp <= 0) return this.die('ERSTICKT'); }
    if (A.hunger >= 100) { this.hp -= 0.8; if (this.hp <= 0) return this.die('AUSGEZEHRT'); }

    // ---- sleep is its own loop (recovery happens HERE, not in execute) ----
    if (this.sleeping) {
      const bed = this.goal && this.goal.dev && this.goal.dev.kind === 'bed' ? this.goal.dev : null;
      A.exhaustion = Math.max(0, A.exhaustion - (bed ? 1.5 : 0.9));
      A.stress = Math.max(0, A.stress - 0.3);
      if (A.exhaustion <= 3 || A.o2 > 60 || tl.gas > 12 || A.hunger >= 85) {
        this.sleeping = false;
        this.goal = null;
      }
      if (this.sayCooldown > 0) this.sayCooldown--;
      return;
    }

    // ---- movement along path (one tile every other tick) ----
    this.moveGate = !this.moveGate;
    if (this.moveGate && this.path.length && !this.executingHere) {
      const [nx, ny] = this.path[0];
      if (world.walkable(nx, ny) || (this.path.length === 1 && this.isGoalTile(nx, ny))) {
        this.tx = nx; this.ty = ny;
        this.path.shift();
        this.walkPhase += 1;
      } else {
        this.repath(world);
      }
    }

    // ---- goal arrival / execution ----
    if (this.goal) this.execute(world, onEvent);

    this.executingHere = false;
    if (this.sayCooldown > 0) this.sayCooldown--;
  }

  isGoalTile(x, y) {
    const g = this.goal;
    if (!g) return false;
    // fleeing to light/gas-free air only counts ON the target tile
    if ((g.act === 'flee' || g.act === 'hide') && g.kind === 'tile') return g.x === x && g.y === y;
    if (g.kind === 'tile' || g.kind === 'dig') return (Math.abs(g.x - x) + Math.abs(g.y - y)) <= 1;
    if (g.kind === 'device') return (Math.abs(g.dev.x - x) + Math.abs(g.dev.y - y)) <= 1;
    return false;
  }

  repath(world) {
    const g = this.goal;
    if (!g) { this.path = []; return; }
    let tx, ty;
    if (g.kind === 'tile') { tx = g.x; ty = g.y; }
    else if (g.kind === 'dig') {
      const spot = this.adjacentStand(world, g.x, g.y);
      if (!spot) { this.goal = null; return; }
      tx = spot.x; ty = spot.y;
    } else {
      // stand adjacent to the device, not on top of it
      const spot = this.adjacentStand(world, g.dev.x, g.dev.y);
      if (!spot) { this.goal = null; return; }
      tx = spot.x; ty = spot.y;
    }
    const p = world.findPath(this.tx, this.ty, tx, ty);
    this.path = p || [];
    if (!p) this.goal = null; // unreachable — re-evaluate next round
  }

  adjacentStand(world, x, y) {
    for (const [dx, dy] of [[1,0],[-1,0],[0,1],[0,-1]]) {
      if (world.walkable(x + dx, y + dy)) return { x: x + dx, y: y + dy };
    }
    return null;
  }

  execute(world, onEvent) {
    const g = this.goal;
    if (!g) return;

    // en route?
    if (g.kind === 'tile' && !this.isGoalTile(this.tx, this.ty)) {
      if (!this.path.length) this.repath(world);
      return;
    }
    if (g.kind === 'device' && !this.isGoalTile(this.tx, this.ty)) {
      if (!this.path.length) this.repath(world);
      return;
    }
    if (g.kind === 'dig' && !this.isGoalTile(this.tx, this.ty)) {
      if (!this.path.length) this.repath(world);
      return;
    }

    this.executingHere = true;
    const A = this.affective;

    switch (g.act) {
      case 'eat': {
        if (world.res.rationen <= 0 || g.dev.broken) { this.goal = null; return; }
        if (!g.dev.powered) {
          // stand at the Ausgabe and wait for the grid (someone is cranking…)
          this.waitTicks = (this.waitTicks || 0) + 1;
          if (this.waitTicks > 40) { this.waitTicks = 0; this.goal = null; }
          return;
        }
        this.waitTicks = 0;
        world.res.rationen--;
        A.hunger = Math.max(0, A.hunger - 45);
        A.stress = Math.max(0, A.stress - 4);
        onEvent({ type: 'meal', inmate: this });
        this.goal = null;
        break;
      }
      case 'sleep': {
        // the sleep loop itself lives in tick(); getting here just commits
        this.sleeping = true;
        break;
      }
      case 'crank': {
        if (!g.dev || g.dev.broken) { this.goal = null; return; }
        if (g.dev.operatedBy != null && g.dev.operatedBy !== this.id) { this.goal = null; return; }
        g.dev.operatedBy = this.id;
        A.exhaustion = Math.min(100, A.exhaustion + 0.35);
        A.hunger = Math.min(100, A.hunger + 0.10);
        A.stress = Math.min(100, A.stress + 0.05);
        if (A.exhaustion > 85) { g.dev.operatedBy = null; this.goal = null; }
        break;
      }
      case 'dig': {
        if (world.tiles[g.y][g.x].t !== 'dirt') { world.Blackboard.removeDigMark(g.x, g.y); this.goal = null; return; }
        this.progress++;
        A.stress = Math.min(100, A.stress + 0.10);
        A.exhaustion = Math.min(100, A.exhaustion + 0.15);
        if (this.progress >= SOP.DIG_TICKS) {
          const ev = world.completeDig(g.x, g.y, this);
          if (ev && ev.type === 'gas') onEvent({ type: 'gasburst', x: g.x, y: g.y });
          if (ev && ev.type === 'cache') onEvent({ type: 'cache', inmate: this, label: ev.label, n: ev.n, res: ev.res });
          this.progress = 0;
          this.goal = null;
        }
        break;
      }
      case 'repair': {
        if (!g.dev || !g.dev.broken) { this.goal = null; return; }
        this.progress++;
        if (this.progress >= 6) { g.dev.broken = false; this.progress = 0; onEvent({ type: 'repair', dev: g.dev, inmate: this }); this.goal = null; }
        break;
      }
      case 'sabotage': {
        if (!g.dev || g.dev.links.length === 0) { this.goal = null; A.stress = Math.max(0, A.stress - 25); return; }
        const other = world.devices.find(d => d.id === g.dev.links[0]);
        if (other) {
          world.removeLink(g.dev, other);
          onEvent({ type: 'sabotage', inmate: this, dev: g.dev });
        }
        A.stress = Math.max(0, A.stress - 30);
        this.goal = null;
        break;
      }
      case 'flee':
      case 'hide':
      case 'wander': {
        this.goal = null; // arrived; next evaluation picks something new
        break;
      }
      case 'expedition': {
        // reached the airlock — hand control back to the Schichtleitung
        onEvent({ type: 'board', inmate: this, dev: g.dev });
        this.goal = null;
        break;
      }
    }
  }

  die(cause) {
    this.dead = true;
    this.deadCause = cause;
    this.sleeping = false;
    // release any device I operate
    for (const d of SOP.World.devices) if (d.operatedBy === this.id) d.operatedBy = null;
  }

  /* ---------------- SAVE / LOAD ---------------- */
  serialize() {
    return {
      id: this.id, name: this.name, trait: this.trait,
      tx: this.tx, ty: this.ty, hp: Math.round(this.hp),
      hungerRate: this.hungerRate,
      affective: Object.assign({}, this.affective),
      dead: this.dead, deadCause: this.deadCause,
      away: this.away ? Object.assign({}, this.away) : null,
    };
  }

  static fromData(d) {
    const i = new SOP.InmateAI(d.name, d.trait, d.tx, d.ty);
    i.id = d.id || d.name;
    Object.assign(i.affective, d.affective);
    i.hp = d.hp;
    i.hungerRate = d.hungerRate || i.hungerRate;
    i.dead = !!d.dead;
    i.deadCause = d.deadCause || '';
    i.away = d.away || null;
    return i;
  }

  logConativeState(action) {
    this.lastScored = action;
  }
};
