/* ===========================================================================
   MAIN — orchestration: game loop, input, events, day cycle, save/load,
   surface expeditions, and colony growth.
   =========================================================================== */
window.SOP = window.SOP || {};

SOP.Main = (() => {
  const world = SOP.World;
  const UI = SOP.UI;
  const R = SOP.Render;

  const SAVE_KEY = 'sop-sektor4-akte';

  let ticks = 0;
  let started = false, paused = false, gameOver = false;
  let simInterval = null;
  let state = {
    selected: null,        // selected inmate
    selDevice: null,       // selected device (crosslink)
    buildKind: null,       // 'wall' | object kind | 'dig' | null
    linkFrom: null,        // device id while wiring
    ghost: null,           // {x, y, kind}
  };
  let nextQuakeTick = 260;
  let nextArrivalTick = 2200;
  let stats = { caches: 0, meals: 0, repairs: 0, sabotages: 0, quakes: 0, expeditions: 0, arrivals: 0 };

  function day() { return SOP.START_DAY + Math.floor(ticks / SOP.DAY_TICKS); }

  /* ---------------- SETUP ---------------- */
  function setup() {
    world.generate();

    // the cast
    const traits = ['Pyromane', 'Paranoid', 'Befehlsfixiert'];
    const spots = [[7, 9], [10, 8], [13, 11]];
    const pool = SOP.NAMES.filter(n => n !== 'SUBJEKT-402').sort(() => Math.random() - 0.5);
    const inmates = spots.map((s, i) =>
      new SOP.InmateAI(i === 0 ? 'SUBJEKT-402' : pool[i - 1], traits[i], s[0], s[1]));
    world.inmates = inmates;

    UI.initBuildMenu(kind => { state.buildKind = kind; state.linkFrom = null; });
    UI.setTicker();
    UI.log('SCHICHT ERÖFFNET. DREI SUBJEKTE REGISTRIERT.', 'ok');
    UI.log('AUFTRAGSLAGE: GRABUNG LÄUFT. STROM HANDGEMACHT.', 'dim');

    bindInput();
    UI.showIntro(() => {
      beginShift();
      UI.log('DURCHSAGE: DIE SCHICHT BEGINNT.', 'ok');
    });

    requestAnimationFrame(frame);
  }

  function beginShift(opts) {
    started = true;
    if (SOP.Audio && SOP.Audio.toggle) SOP.Audio.toggle(); // motorik loop (user gesture)
    if (!opts || opts.interval !== false) {
      if (!simInterval) simInterval = setInterval(simTick, SOP.TICK_MS);
    }
  }

  /* ---------------- SIMULATION TICK ---------------- */
  function simTick() {
    if (!started || paused || gameOver) return;
    ticks++;

    world.tick(handleWorldEvent);

    // expedition returns
    for (const inm of world.inmates) {
      if (!inm.dead && inm.away && ticks >= inm.away.returnTick) returnFromExpedition(inm);
    }

    for (const inm of world.inmates) {
      if (inm.dead || inm.away) continue;
      // boarding failsafe: path impossible → abandon the expedition
      if (inm.boarding && !inm.goal) {
        inm.boarding = false;
        UI.log('EXPEDITION ABGEBROCHEN: SCHLEUSE NICHT ERREICHBAR.', 'alert');
        continue;
      }
      if (ticks % 4 === 0 && !inm.boarding) inm.evaluateDrives(world);  // 4 ticks = 1 s
      inm.tick(world, handleInmateEvent);
    }

    // newcomer at the airlock
    if (ticks >= nextArrivalTick) {
      const arrived = tryArrival();
      if (arrived) {
        scheduleNextArrival();
      } else {
        // stand blocked or colony full — peek again soon
        const full = world.inmates.filter(i => !i.dead).length >= SOP.MAX_INMATES;
        nextArrivalTick = ticks + (full ? 2400 : 120 + Math.floor(Math.random() * 180));
      }
    }

    // random seismic event
    if (ticks >= nextQuakeTick) {
      quake();
      nextQuakeTick = ticks + 380 + Math.floor(Math.random() * 260);
    }

    // autosave every ~5 minutes of sim time
    if (ticks % 1200 === 0 && !gameOver) saveGame(true);

    // game over check
    if (world.inmates.every(i => i.dead)) endGame();
  }

  function handleWorldEvent(ev) {
    if (ev.type === 'burn') UI.log('NOTSTROMAGGREGAT VERFEUERT 1 ÖL.', 'dim');
    if (ev.type === 'harvest') UI.log('PILZFARM: 1 RATION GEERNTET.', 'dim');
  }

  function handleInmateEvent(ev) {
    switch (ev.type) {
      case 'meal':
        stats.meals++;
        break;
      case 'cache':
        stats.caches++;
        UI.log(`${ev.inmate.name} BIRGT ${ev.label} (+${ev.n})`, 'ok');
        break;
      case 'gasburst':
        UI.alert(`GAS-SCHLOT FREIGELEGT BEI ${ev.x}/${ev.y}. LUFT WASCHEN ODER MAUERN.`);
        R.shake(400);
        world.inmates.forEach(i => { if (!i.dead && !i.away) { i.affective.stress = Math.min(100, i.affective.stress + 8); i.affective.paranoia = Math.min(100, i.affective.paranoia + 10); } });
        break;
      case 'sabotage':
        stats.sabotages++;
        UI.alert(`${ev.inmate.name}: PSYCHOTISCHER SCHUB. LEITUNG GEKAPPT (${SOP.OBJ[ev.dev.kind].label}).`);
        R.shake(300);
        world.inmates.forEach(i => { if (!i.dead && !i.away && i !== ev.inmate) i.affective.stress = Math.min(100, i.affective.stress + 12); });
        break;
      case 'repair':
        stats.repairs++;
        UI.log(`${ev.inmate.name} REPARIERT ${SOP.OBJ[ev.dev.kind].label}.`, 'ok');
        break;
      case 'board': {
        const inm = ev.inmate;
        inm.boarding = false;
        inm.goal = null;
        inm.path = [];
        const dur = SOP.EXPEDITION_TICKS[0] +
          Math.floor(Math.random() * (SOP.EXPEDITION_TICKS[1] - SOP.EXPEDITION_TICKS[0]));
        inm.away = { returnTick: ticks + dur, started: ticks };
        inm.currentAction = { name: 'AUSSERHAUS', score: 0 };
        UI.log(`${inm.name} IST AUSSERHAUS. RÜCKKEHR IN ~${Math.round(dur * SOP.TICK_MS / 1000)} S.`, 'wire');
        break;
      }
    }
  }

  /* ---------------- EXPEDITIONS ---------------- */
  function adjacentStand(dev, ignoreInmates) {
    for (const [dx, dy] of [[0, 1], [1, 0], [-1, 0], [0, -1]]) {
      const x = dev.x + dx, y = dev.y + dy;
      if (!world.walkable(x, y)) continue;
      if (!ignoreInmates && world.inmates.some(i => !i.dead && !i.away && i.tx === x && i.ty === y)) continue;
      return { x, y };
    }
    return null;
  }

  function startExpedition(name) {
    if (gameOver || !started) return;
    const air = world.devices.find(d => d.kind === 'airlock');
    if (!air) { UI.log('KEINE LUFTSCHLEUSE VORHANDEN.', 'alert'); return; }
    const inm = world.inmates.find(i => i.name === name && !i.dead && !i.away && !i.boarding);
    if (!inm) return;
    if (!adjacentStand(air)) { UI.log('SCHLEUSE NICHT ERREICHBAR — ZUGANG FREIMACHEN.', 'alert'); return; }
    inm.sleeping = false;
    inm.boarding = true;
    inm.path = [];
    inm.goal = { kind: 'device', dev: air, act: 'expedition' };
    inm.currentAction = { name: 'EXPEDITION', score: 999 };
    inm.thought = 'Raus. Nur kurz. Nur mit Maske.';
    UI.log(`${inm.name}: GANG ZUR OBERFLÄCHE. MASKE SITZT.`, 'wire');
  }

  function rollLoot() {
    const totalW = SOP.LOOT.reduce((a, c) => a + c.weight, 0);
    const n = 2 + (Math.random() < 0.4 ? 1 : 0);
    const out = [];
    for (let i = 0; i < n; i++) {
      let roll = Math.random() * totalW, c = SOP.LOOT[0];
      for (const cand of SOP.LOOT) { roll -= cand.weight; if (roll <= 0) { c = cand; break; } }
      out.push({ res: c.res, label: c.label, n: c.n[0] + Math.floor(Math.random() * (c.n[1] - c.n[0] + 1)) });
    }
    return out;
  }

  function returnFromExpedition(inm) {
    stats.expeditions++;
    const air = world.devices.find(d => d.kind === 'airlock');
    const spot = air ? adjacentStand(air) : null;
    if (spot) { inm.tx = spot.x; inm.ty = spot.y; inm.px = spot.x; inm.py = spot.y; }
    inm.away = null;
    const gains = rollLoot();
    for (const g of gains) world.res[g.res] = (world.res[g.res] || 0) + g.n;
    UI.log(`${inm.name} ZURÜCK VON DER OBERFLÄCHE: ${gains.map(g => '+' + g.n + ' ' + g.label).join(', ')}.`, 'ok');
    if (Math.random() < SOP.EXPEDITION_INJURY_CHANCE) {
      inm.hp = Math.max(5, inm.hp - 35);
      inm.affective.stress = Math.min(100, inm.affective.stress + 25);
      UI.alert(`${inm.name}: VERLETZUNG AUF DER OBERFLÄCHE. REVIER NOTWENDIG.`);
    } else {
      inm.affective.stress = Math.min(100, inm.affective.stress + 8);
    }
    inm.affective.o2 = Math.min(100, inm.affective.o2 + 12); // thin air up there
    inm.affective.exhaustion = Math.min(100, inm.affective.exhaustion + 15);
  }

  /* ---------------- COLONY GROWTH ---------------- */
  function tryArrival() {
    if (gameOver) return false;
    const air = world.devices.find(d => d.kind === 'airlock');
    if (!air) return false;
    const present = world.inmates.filter(i => !i.dead);
    if (present.length >= SOP.MAX_INMATES) return false;
    const spot = adjacentStand(air, true); // a brief overlap at the gate is fine
    if (!spot) return false;
    const used = new Set(world.inmates.map(i => i.name));
    const pool = SOP.NAMES.filter(n => !used.has(n));
    const name = pool.length
      ? pool[Math.floor(Math.random() * pool.length)]
      : 'SUBJEKT-' + Math.floor(100 + Math.random() * 900);
    const traitKeys = Object.keys(SOP.TRAITS);
    const trait = traitKeys[Math.floor(Math.random() * traitKeys.length)];
    const nu = new SOP.InmateAI(name, trait, spot.x, spot.y);
    nu.affective.hunger = 55 + Math.random() * 25;   // arrived hungry
    nu.affective.stress = 30 + Math.random() * 20;   // the surface does that
    world.inmates.push(nu);
    stats.arrivals++;
    UI.log(`NEUZUGANG AN DER SCHLEUSE: ${name} (${trait.toUpperCase()}). AKTE ERÖFFNET.`, 'ok');
    UI.setTicker(`AKTUELLE DURCHSAGE: ${name} IST DEM SEKTOR 4 ZUGETEILT WORDEN`);
    return true;
  }

  function scheduleNextArrival() {
    const radio = world.devices.find(d =>
      d.kind === 'radio' && d.powered && !d.broken && d.enabled !== false);
    const range = radio ? SOP.ARRIVAL_RADIO : SOP.ARRIVAL_BASE;
    nextArrivalTick = ticks + range[0] + Math.floor(Math.random() * (range[1] - range[0]));
  }

  /* ---------------- SAVE / LOAD ---------------- */
  function storage() { try { return window.localStorage; } catch (e) { return null; } }

  function buildSaveData() {
    return {
      v: 1,
      savedAt: Date.now(),
      ticks, nextQuakeTick, nextArrivalTick,
      stats: Object.assign({}, stats),
      world: world.serialize(),
      inmates: world.inmates.map(i => i.serialize()),
    };
  }

  function saveGame(silent) {
    const st = storage();
    if (!st) { if (!silent) UI.log('STORAGE BLOCKIERT. NUTZE EXPORT.', 'alert'); return false; }
    try {
      st.setItem(SAVE_KEY, JSON.stringify(buildSaveData()));
      if (!silent) UI.log('AKTE GESICHERT (LOKAL).', 'dim');
      return true;
    } catch (e) {
      if (!silent) UI.log('SICHERUNG FEHLGESCHLAGEN. NUTZE EXPORT.', 'alert');
      return false;
    }
  }

  function loadGame(data) {
    try {
      if (!data || data.v !== 1) { UI.log('AKTE UNLESBAR (FALSCHES FORMAT).', 'alert'); return false; }
      world.loadFrom(data.world);
      const inmates = data.inmates.map(d => SOP.InmateAI.fromData(d));
      const ids = new Set(inmates.map(i => i.id));
      for (const d of world.devices) {
        if (d.operatedBy != null && !ids.has(d.operatedBy)) d.operatedBy = null;
      }
      world.inmates = inmates;
      ticks = data.ticks;
      nextQuakeTick = data.nextQuakeTick;
      nextArrivalTick = data.nextArrivalTick;
      Object.assign(stats, data.stats);
      state.selected = null; state.selDevice = null;
      state.buildKind = null; state.linkFrom = null; state.ghost = null;
      UI.clearBuildSelection();
      gameOver = false;
      document.getElementById('overlay-over').classList.remove('show');
      document.getElementById('overlay-intro').classList.remove('show');
      paused = false;
      const pb = document.getElementById('btn-pause');
      pb.classList.remove('pause-on'); pb.textContent = '❚❚ PAUSE';
      if (!started) beginShift();
      UI.log(`AKTE GELADEN — TAG ${day()}. DIE SCHICHT GEHT WEITER.`, 'ok');
      return true;
    } catch (e) {
      if (typeof console !== 'undefined') console.error('LOAD ERROR:', e);
      UI.log('LADEN FEHLGESCHLAGEN.', 'alert');
      return false;
    }
  }

  function exportSave() {
    try {
      const blob = new Blob([JSON.stringify(buildSaveData())], { type: 'application/json' });
      const a = document.createElement('a');
      a.href = URL.createObjectURL(blob);
      a.download = 'sop-sektor4-akte.json';
      document.body.appendChild(a);
      a.click();
      a.remove();
      setTimeout(() => URL.revokeObjectURL(a.href), 2000);
      UI.log('AKTE EXPORTIERT.', 'dim');
    } catch (e) {
      UI.log('EXPORT FEHLGESCHLAGEN.', 'alert');
    }
  }

  function importSave(file) {
    const r = new FileReader();
    r.onload = () => {
      try { loadGame(JSON.parse(r.result)); }
      catch (e) { UI.log('AKTE UNLESBAR.', 'alert'); }
    };
    r.readAsText(file);
  }

  /* ---------------- EVENTS ---------------- */
  function quake() {
    const name = SOP.QUAKE_NAMES[Math.floor(Math.random() * SOP.QUAKE_NAMES.length)];
    stats.quakes++;
    R.shake(800);
    UI.alert(`${name} — STRUKTURSCHADEN IM SEKTOR.`);
    UI.setTicker(`AKUTMELDUNG: ${name} ERSCHÜTTERT SEKTOR 4`);
    // damage 1–2 random devices
    const fragile = world.devices.filter(d => d.kind !== 'gas_vent' && !d.broken);
    const hits = 1 + (Math.random() < 0.4 ? 1 : 0);
    for (let i = 0; i < hits && fragile.length; i++) {
      const idx = Math.floor(Math.random() * fragile.length);
      const d = fragile.splice(idx, 1)[0];
      d.broken = true;
      UI.log(`DEFEKT: ${SOP.OBJ[d.kind].label} BEI ${d.x}/${d.y}.`, 'alert');
    }
    world.inmates.forEach(i => {
      if (i.dead || i.away) return;
      i.affective.stress = Math.min(100, i.affective.stress + 12);
      i.affective.paranoia = Math.min(100, i.affective.paranoia + (i.trait === 'Paranoid' ? 22 : 8));
      i.sleeping = false;
    });
    if (SOP.Audio && SOP.Audio.on) SOP.Audio.alarm();
  }

  function endGame() {
    gameOver = true;
    const daysWorked = Math.floor(ticks / SOP.DAY_TICKS);
    UI.showGameOver(`
      <div class="kv"><span class="k">TAGE IM BETRIEB</span><span>${daysWorked}</span></div>
      <div class="kv"><span class="k">MAHLZEITEN</span><span>${stats.meals}</span></div>
      <div class="kv"><span class="k">CACHES GEBORGEN</span><span>${stats.caches}</span></div>
      <div class="kv"><span class="k">EXPEDITIONEN</span><span>${stats.expeditions}</span></div>
      <div class="kv"><span class="k">NEUZUGÄNGE</span><span>${stats.arrivals}</span></div>
      <div class="kv"><span class="k">REPARATUREN</span><span>${stats.repairs}</span></div>
      <div class="kv"><span class="k">PSYCHOTISCHE SCHÜBE</span><span>${stats.sabotages}</span></div>
      <div class="kv"><span class="k">ERDBEBEN ÜBERSTANDEN</span><span>${stats.quakes}</span></div>
      <div class="kv"><span class="k">ENDSTAND AKTE</span><span>GESCHLOSSEN</span></div>`,
      () => location.reload());
  }

  /* ---------------- RENDER LOOP ---------------- */
  let uiFrame = 0;
  function frame() {
    R.draw({
      world,
      selected: state.selected,
      ghost: state.ghost,
      linkFrom: state.linkFrom,
    });
    if (++uiFrame % 4 === 0 && !gameOver) {
      UI.updateSystem(world, day());
      UI.updateInspector(world, state.selected);
    }
    if (uiFrame % 10 === 0 && !gameOver) {
      UI.updateDevicePanel(world, state.selDevice, R.getView(), ticks);
    }
    requestAnimationFrame(frame);
  }

  /* ---------------- INPUT ---------------- */
  function bindInput() {
    const canvas = document.getElementById('gameCanvas');

    canvas.addEventListener('contextmenu', e => e.preventDefault());

    canvas.addEventListener('mousemove', e => {
      const r = canvas.getBoundingClientRect();
      const t = R.toTile(e.clientX - r.left, e.clientY - r.top);
      if (state.buildKind && state.buildKind !== 'dig') {
        state.ghost = { x: t.x, y: t.y, kind: state.buildKind };
      } else {
        state.ghost = null;
      }
    });

    canvas.addEventListener('mousedown', e => {
      if (!started || gameOver) return;
      const r = canvas.getBoundingClientRect();
      const t = R.toTile(e.clientX - r.left, e.clientY - r.top);
      const { x, y } = t;
      if (!world.inGrid(x, y)) return;

      if (e.button === 2) { // right click cancels
        state.buildKind = null; state.linkFrom = null;
        UI.clearBuildSelection();
        return;
      }

      if (R.getView() === 'CROSSLINK') { crosslinkClick(x, y); return; }

      // ---- PHYSICAL MODE ----
      if (state.buildKind === 'dig') {
        if (world.orderDig(x, y)) UI.log(`GRABUNGSAUFTRAG ${x}/${y} ERTEILT.`, 'dim');
        return;
      }
      if (state.buildKind === 'wall') {
        const r2 = world.tryBuildWall(x, y);
        if (!r2.ok) UI.log('BAU ABGELEHNT: ' + r2.err, 'alert');
        else UI.log('WAND GEZOGEN.', 'dim');
        return;
      }
      if (state.buildKind) {
        const r2 = world.tryBuild(state.buildKind, x, y);
        if (!r2.ok) UI.log('BAU ABGELEHNT: ' + r2.err, 'alert');
        else {
          UI.log(`${SOP.OBJ[state.buildKind].label} INSTALLIERT. VERKABELUNG IM CROSSLINK.`, 'ok');
          state.buildKind = null;
          UI.clearBuildSelection();
        }
        return;
      }

      // select inmate or device
      const inm = world.inmates.find(i => !i.dead && !i.away && i.tx === x && i.ty === y);
      if (inm) { state.selected = inm; state.selDevice = null; return; }
      const tl = world.tiles[y][x];
      if (tl.obj) { state.selDevice = tl.obj; state.selected = null; }
      else { state.selected = null; state.selDevice = null; }
    });

    function crosslinkClick(x, y) {
      const tl = world.tiles[y][x];
      const dev = tl.obj;
      if (!dev) { state.linkFrom = null; state.selDevice = null; return; }
      if (dev.kind === 'airlock') { UI.log('DIE SCHLEUSE IST KEIN KNOTEN.', 'dim'); return; }
      state.selDevice = dev;
      if (state.linkFrom == null) {
        if (dev.kind === 'gas_vent') { UI.log('GAS-SCHLOT IST KEIN KNOTEN.', 'dim'); return; }
        state.linkFrom = dev.id;
        return;
      }
      if (state.linkFrom === dev.id) { state.linkFrom = null; return; }
      const a = world.devices.find(d => d.id === state.linkFrom);
      state.linkFrom = null;
      if (!a || dev.kind === 'gas_vent') return;
      if (a.links.includes(dev.id)) {
        world.removeLink(a, dev);
        UI.wire(`LEITUNG GETRENNT: ${SOP.OBJ[a.kind].label} ↔ ${SOP.OBJ[dev.kind].label}.`);
      } else {
        if (world.addLink(a, dev)) {
          UI.wire(`LEITUNG GELEGT: ${SOP.OBJ[a.kind].label} ↔ ${SOP.OBJ[dev.kind].label}.`);
        } else {
          UI.log(`LEITUNG ZU LANG (MAX ${SOP.LINK_RANGE} FELDER).`, 'alert');
        }
      }
    }

    // header buttons
    document.getElementById('btn-physical').addEventListener('click', e => setView('PHYSICAL', e.target));
    document.getElementById('btn-crosslink').addEventListener('click', e => setView('CROSSLINK', e.target));

    document.getElementById('btn-pause').addEventListener('click', () => {
      paused = !paused;
      const b = document.getElementById('btn-pause');
      b.classList.toggle('pause-on', paused);
      b.textContent = paused ? '▶ WEITER' : '❚❚ PAUSE';
      UI.log(paused ? 'SIMULATION ANGEHALTEN.' : 'SIMULATION FORTGESETZT.', 'dim');
    });

    document.getElementById('btn-audio').addEventListener('click', () => {
      const on = SOP.Audio.toggle();
      document.getElementById('btn-audio').textContent = on ? 'TON AN' : 'TON AUS';
    });

    // Akte (save/load) panel
    document.getElementById('btn-save').addEventListener('click', () => saveGame(false));
    document.getElementById('btn-load').addEventListener('click', () => {
      const st = storage();
      const raw = st && st.getItem(SAVE_KEY);
      if (!raw) { UI.log('KEIN SPEICHERSTAND GEFUNDEN.', 'alert'); return; }
      try { loadGame(JSON.parse(raw)); } catch (e) { UI.log('SPEICHERSTAND BESCHÄDIGT.', 'alert'); }
    });
    document.getElementById('btn-export').addEventListener('click', exportSave);
    document.getElementById('btn-import').addEventListener('click', () =>
      document.getElementById('file-import').click());
    document.getElementById('file-import').addEventListener('change', e => {
      const f = e.target.files && e.target.files[0];
      if (f) importSave(f);
      e.target.value = '';
    });

    // keyboard
    window.addEventListener('keydown', e => {
      if (!started) return;
      const k = e.key.toLowerCase();
      if (k === ' ') { e.preventDefault(); document.getElementById('btn-pause').click(); return; }
      if (k === 'v') {
        const other = R.getView() === 'PHYSICAL' ? 'CROSSLINK' : 'PHYSICAL';
        document.getElementById(other === 'PHYSICAL' ? 'btn-physical' : 'btn-crosslink').click();
        return;
      }
      if (k === 'm') { document.getElementById('btn-audio').click(); return; }
      if (k === 'escape') {
        state.buildKind = null; state.linkFrom = null;
        UI.clearBuildSelection();
        return;
      }
      if (k === 'w') { clickMenuItem('wall'); return; }
      if (k === 'x') { clickMenuItem('dig'); return; }
      if (k === 'f5') { e.preventDefault(); saveGame(false); return; }
      if (k === 'e') {
        if (state.selDevice) UI.toggleDevice(state.selDevice);
        return;
      }
      for (const kind of SOP.BUILDABLE) {
        if (SOP.OBJ[kind].hotkey === e.key) { clickMenuItem(kind); return; }
      }
    });
  }

  function clickMenuItem(kind) {
    const btn = document.querySelector(`.build-item[data-kind="${kind}"]`);
    if (btn) btn.click();
  }

  function setView(v, btnEl) {
    R.setView(v);
    state.linkFrom = null;
    document.querySelectorAll('#header .btn').forEach(b => b.classList.remove('active'));
    if (btnEl) btnEl.classList.add('active');
    if (v === 'CROSSLINK') UI.wire('CROSSLINK GEÖFFNET. LEITUNGEN SICHTBAR.');
  }

  return {
    setup, day,
    startExpedition,
    step: simTick,                       // one sim tick (also used headless by tools/smoke.js)
    headlessStart: () => beginShift({ interval: false }),
    saveData: buildSaveData,
    loadData: loadGame,
    get state() { return state; },
    get ticks() { return ticks; },
    get stats() { return stats; },
  };
})();

window.addEventListener('DOMContentLoaded', () => SOP.Main.setup());
