/* ===========================================================================
   MAIN — orchestration: game loop, input, events, day cycle, game over.
   =========================================================================== */
window.SOP = window.SOP || {};

SOP.Main = (() => {
  const world = SOP.World;
  const UI = SOP.UI;
  const R = SOP.Render;

  let ticks = 0;
  let started = false, paused = false, gameOver = false;
  let state = {
    selected: null,        // selected inmate
    selDevice: null,       // selected device (crosslink)
    buildKind: null,       // 'wall' | object kind | 'dig' | null
    linkFrom: null,        // device id while wiring
    ghost: null,           // {x, y, kind}
  };
  let nextQuakeTick = 260;
  let stats = { caches: 0, meals: 0, repairs: 0, sabotages: 0, quakes: 0 };

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
      started = true;
      SOP.Audio.toggle(); // starts the motorik loop (user gesture)
      setInterval(simTick, SOP.TICK_MS);
      UI.log('DURCHSAGE: DIE SCHICHT BEGINNT.', 'ok');
    });

    requestAnimationFrame(frame);
  }

  /* ---------------- SIMULATION TICK ---------------- */
  function simTick() {
    if (!started || paused || gameOver) return;
    ticks++;

    world.tick(handleWorldEvent);

    for (const inm of world.inmates) {
      if (inm.dead) continue;
      if (ticks % 4 === 0) inm.evaluateDrives(world);  // 4 ticks = 1 s
      inm.tick(world, handleInmateEvent);
    }

    // random seismic event
    if (ticks >= nextQuakeTick) {
      quake();
      nextQuakeTick = ticks + 380 + Math.floor(Math.random() * 260);
    }

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
        world.inmates.forEach(i => { if (!i.dead) { i.affective.stress = Math.min(100, i.affective.stress + 8); i.affective.paranoia = Math.min(100, i.affective.paranoia + 10); } });
        break;
      case 'sabotage':
        stats.sabotages++;
        UI.alert(`${ev.inmate.name}: PSYCHOTISCHER SCHUB. LEITUNG GEKAPPT (${SOP.OBJ[ev.dev.kind].label}).`);
        R.shake(300);
        world.inmates.forEach(i => { if (!i.dead && i !== ev.inmate) i.affective.stress = Math.min(100, i.affective.stress + 12); });
        break;
      case 'repair':
        stats.repairs++;
        UI.log(`${ev.inmate.name} REPARIERT ${SOP.OBJ[ev.dev.kind].label}.`, 'ok');
        break;
    }
  }

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
      if (i.dead) return;
      i.affective.stress = Math.min(100, i.affective.stress + 12);
      i.affective.paranoia = Math.min(100, i.affective.paranoia + (i.trait === 'Paranoid' ? 22 : 8));
      i.sleeping = false;
    });
    if (SOP.Audio.on) SOP.Audio.alarm();
  }

  function endGame() {
    gameOver = true;
    const daysWorked = Math.floor(ticks / SOP.DAY_TICKS);
    UI.showGameOver(`
      <div class="kv"><span class="k">TAGE IM BETRIEB</span><span>${daysWorked}</span></div>
      <div class="kv"><span class="k">MAHLZEITEN</span><span>${stats.meals}</span></div>
      <div class="kv"><span class="k">CACHES GEBORGEN</span><span>${stats.caches}</span></div>
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
    if (uiFrame % 30 === 0 && !gameOver) {
      UI.updateDevicePanel(world, state.selDevice, R.getView());
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
      const inm = world.inmates.find(i => !i.dead && i.tx === x && i.ty === y);
      if (inm) { state.selected = inm; state.selDevice = null; return; }
      const tl = world.tiles[y][x];
      if (tl.obj) { state.selDevice = tl.obj; state.selected = null; }
      else { state.selected = null; state.selDevice = null; }
    });

    function crosslinkClick(x, y) {
      const tl = world.tiles[y][x];
      const dev = tl.obj;
      if (!dev) { state.linkFrom = null; state.selDevice = null; return; }
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

  return { setup, day, get state() { return state; } };
})();

window.addEventListener('DOMContentLoaded', () => SOP.Main.setup());
