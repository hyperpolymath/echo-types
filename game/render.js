/* ===========================================================================
   RENDERER — dual-state drawing:
   PHYSICAL  : Shelter-style dollhouse cross-section, monochrome amber CRT.
   CROSSLINK : Gunpoint-style wiring overlay, cyan nodes & power flow.
   NOTE: the prototype wrote ctx.fillStyle = 'var(--…)' — canvas can't
   resolve CSS variables, so real colors are used here.
   =========================================================================== */
window.SOP = window.SOP || {};

SOP.Render = (() => {
  const canvas = document.getElementById('gameCanvas');
  const ctx = canvas.getContext('2d');

  const C = {
    bg: '#0a0a0a', bgCross: '#020508',
    dirt: '#241c12', dirtHi: '#31261a',
    rock: '#151313',
    wall: '#3a3a3a', wallSeam: '#222',
    amber: '#ffb000', amberDim: '#8a5f00', amberFaint: '#3d2c00',
    alert: '#ff0033', wire: '#00ccff', wireDim: '#0a5a70', ok: '#00ff66', gas: '#9dff00',
    grid: '#161616',
  };

  let viewMode = 'PHYSICAL';
  let scale = 1, offX = 0, offY = 0;
  let shakeUntil = 0;
  let now = 0;

  function setView(v) { viewMode = v; }
  function getView() { return viewMode; }
  function shake(dur) { shakeUntil = performance.now() + dur; }

  function resize() {
    const box = document.getElementById('canvas-container');
    canvas.width = box.clientWidth;
    canvas.height = box.clientHeight;
    const s = Math.min(canvas.width / (SOP.GRID_W * SOP.TILE), canvas.height / (SOP.GRID_H * SOP.TILE));
    scale = Math.max(0.4, s);
    offX = (canvas.width - SOP.GRID_W * SOP.TILE * scale) / 2;
    offY = (canvas.height - SOP.GRID_H * SOP.TILE * scale) / 2;
  }

  function toTile(mx, my) {
    const x = Math.floor((mx - offX) / (SOP.TILE * scale));
    const y = Math.floor((my - offY) / (SOP.TILE * scale));
    return { x, y };
  }

  /* deterministic pseudo-random per tile for texture */
  function hash(x, y) {
    let h = (x * 374761393 + y * 668265263) | 0;
    h = (h ^ (h >> 13)) * 1274126177 | 0;
    return ((h ^ (h >> 16)) >>> 0) / 4294967295;
  }

  function draw(state) {
    now = performance.now();
    resizeIfNeeded();
    ctx.setTransform(1, 0, 0, 1, 0, 0);
    ctx.fillStyle = viewMode === 'PHYSICAL' ? C.bg : C.bgCross;
    ctx.fillRect(0, 0, canvas.width, canvas.height);

    ctx.save();
    // earthquake shake
    let sx = 0, sy = 0;
    if (now < shakeUntil) {
      const m = 5 * ((shakeUntil - now) / 700);
      sx = (Math.random() - 0.5) * m * 2; sy = (Math.random() - 0.5) * m * 2;
    }
    ctx.translate(offX + sx, offY + sy);
    ctx.scale(scale, scale);

    if (viewMode === 'PHYSICAL') drawPhysical(state);
    else drawCrosslink(state);

    ctx.restore();

    // overlay label
    ctx.fillStyle = viewMode === 'PHYSICAL' ? C.amberDim : C.wire;
    ctx.font = '12px "Courier New", monospace';
    const label = viewMode === 'PHYSICAL'
      ? 'PHYSISCHE EBENE — RÄUME / ERDREICH / SUBJEKTE'
      : 'CROSSLINK AKTIV — LOGIK & LEITUNGEN // KLICK A→B: VERBINDEN';
    ctx.fillText(label, 14, 22);
    ctx.fillStyle = viewMode === 'PHYSICAL' ? C.amberFaint : C.wireDim;
    ctx.fillText('SEKTOR 4 // ÜBERWACHUNGSMONITOR 07-B', 14, 38);
  }

  function resizeIfNeeded() {
    const box = document.getElementById('canvas-container');
    if (canvas.width !== box.clientWidth || canvas.height !== box.clientHeight) resize();
  }

  /* ---------------- PHYSICAL LAYER ---------------- */
  function drawPhysical(state) {
    const T = SOP.TILE, world = state.world;

    // tiles
    for (let y = 0; y < world.H; y++) {
      for (let x = 0; x < world.W; x++) {
        const tl = world.tiles[y][x];
        const px = x * T, py = y * T;
        if (tl.t === 'bedrock') {
          ctx.fillStyle = C.rock;
          ctx.fillRect(px, py, T, T);
          if (hash(x, y) > 0.7) {
            ctx.strokeStyle = '#1e1b1b';
            ctx.beginPath();
            ctx.moveTo(px + 4, py + T - 5); ctx.lineTo(px + T - 5, py + 4);
            ctx.stroke();
          }
        } else if (tl.t === 'dirt') {
          ctx.fillStyle = tl.mark ? '#3a2e1c' : C.dirt;
          ctx.fillRect(px, py, T, T);
          // speckle
          const n = Math.floor(hash(x, y) * 4);
          ctx.fillStyle = C.dirtHi;
          for (let i = 0; i < n; i++) {
            const rx = px + 3 + hash(x + i, y) * (T - 6);
            const ry = py + 3 + hash(x, y + i) * (T - 6);
            ctx.fillRect(rx, ry, 2, 2);
          }
          if (tl.mark) {
            ctx.strokeStyle = C.amber;
            ctx.setLineDash([3, 3]);
            ctx.strokeRect(px + 3.5, py + 3.5, T - 7, T - 7);
            ctx.setLineDash([]);
            ctx.fillStyle = C.amber;
            ctx.font = 'bold 13px "Courier New", monospace';
            ctx.fillText('⛏', px + T / 2 - 6, py + T / 2 + 5);
          }
        } else if (tl.t === 'wall') {
          ctx.fillStyle = C.wall;
          ctx.fillRect(px, py, T, T);
          ctx.strokeStyle = C.wallSeam;
          ctx.strokeRect(px + 0.5, py + 0.5, T - 1, T - 1);
          ctx.beginPath();
          ctx.moveTo(px, py + T / 2); ctx.lineTo(px + T, py + T / 2);
          ctx.stroke();
        } else { // empty
          ctx.fillStyle = tl.lit ? '#181307' : '#0c0c0c';
          ctx.fillRect(px, py, T, T);
          ctx.strokeStyle = C.grid;
          ctx.strokeRect(px + 0.5, py + 0.5, T - 1, T - 1);
        }
      }
    }

    // warm glow from lamps
    for (const d of world.devices) {
      if (d.kind !== 'lamp' || !d.powered || d.broken) continue;
      const g = ctx.createRadialGradient(d.x * T + T / 2, d.y * T + T / 2, 4, d.x * T + T / 2, d.y * T + T / 2, T * 4.4);
      g.addColorStop(0, 'rgba(255,176,0,0.16)');
      g.addColorStop(1, 'rgba(255,176,0,0)');
      ctx.fillStyle = g;
      ctx.fillRect((d.x - 4.5) * T, (d.y - 4.5) * T, T * 10, T * 10);
    }

    // gas haze
    for (let y = 0; y < world.H; y++) for (let x = 0; x < world.W; x++) {
      const tl = world.tiles[y][x];
      if (tl.t !== 'empty' || tl.gas <= 4) continue;
      ctx.fillStyle = `rgba(157,255,0,${Math.min(0.35, tl.gas / 260)})`;
      ctx.fillRect(x * T, y * T, T, T);
    }

    // devices
    for (const d of world.devices) drawDevice(d, T);

    // inmates
    for (const inm of world.inmates) drawInmate(inm, T, state.selected === inm);

    // ghost placement
    if (state.ghost) drawGhost(state.ghost, T, state.world);
  }

  function drawDevice(d, T) {
    const px = d.x * T, py = d.y * T;
    const def = SOP.OBJ[d.kind];
    if (d.kind === 'gas_vent') {
      ctx.fillStyle = '#1a2408';
      ctx.fillRect(px + 4, py + 4, T - 8, T - 8);
      ctx.fillStyle = C.gas;
      ctx.font = `${T * 0.55}px "Courier New", monospace`;
      ctx.fillText(def.icon, px + T / 2 - 7, py + T / 2 + 6);
      // wisps
      const t = now / 600;
      ctx.fillStyle = `rgba(157,255,0,${0.25 + 0.1 * Math.sin(t + d.id)})`;
      ctx.beginPath();
      ctx.arc(px + T / 2 + Math.sin(t * 1.7 + d.id) * 5, py - 6 - (t % 1) * 8, 3.5, 0, 7);
      ctx.fill();
      return;
    }
    // base plate
    ctx.fillStyle = d.broken ? '#2a0a10' : '#191919';
    ctx.fillRect(px + 2, py + 2, T - 4, T - 4);
    ctx.strokeStyle = d.broken ? C.alert : (d.powered ? C.amber : C.amberFaint);
    if (d.broken && Math.floor(now / 300) % 2 === 0) ctx.strokeStyle = '#7a0018';
    ctx.strokeRect(px + 2.5, py + 2.5, T - 5, T - 5);
    ctx.fillStyle = d.broken ? C.alert : (d.powered ? C.amber : C.amberDim);
    ctx.font = `${T * 0.5}px "Courier New", monospace`;
    ctx.fillText(def.icon, px + T / 2 - T * 0.24, py + T / 2 + T * 0.18);
    if (d.broken) {
      ctx.fillStyle = C.alert;
      ctx.font = 'bold 10px "Courier New", monospace';
      ctx.fillText('!', px + T - 10, py + 11);
    }
    if (d.kind === 'door') {
      ctx.fillStyle = d.open ? 'rgba(255,176,0,0.15)' : '#2c2c2c';
      ctx.fillRect(px + 3, py + 3, T - 6, T - 6);
      if (!d.open) {
        ctx.strokeStyle = '#4a4a4a';
        ctx.beginPath(); ctx.moveTo(px + 5, py + T / 2); ctx.lineTo(px + T - 5, py + T / 2); ctx.stroke();
      }
    }
    if (d.kind === 'dynamo' && d.operatedBy != null) {
      const t = now / 120;
      ctx.strokeStyle = C.amber;
      ctx.beginPath();
      ctx.arc(px + T / 2, py + T / 2, T * 0.32, t, t + 1.2);
      ctx.stroke();
    }
  }

  function drawInmate(inm, T, selected) {
    const px = inm.tx * T + T / 2, py = inm.ty * T + T / 2;
    if (inm.dead) {
      ctx.fillStyle = '#5a5a5a';
      ctx.fillRect(px - 8, py + 4, 16, 5);
      ctx.strokeStyle = '#333';
      ctx.strokeRect(px - 8.5, py + 3.5, 17, 6);
      return;
    }
    const bob = inm.sleeping ? 0 : Math.sin(inm.walkPhase * 1.4) * 1.2;
    if (inm.sleeping) {
      ctx.fillStyle = C.amberDim;
      ctx.fillRect(px - 8, py + 1, 16, 6);
      ctx.fillStyle = C.amberFaint;
      ctx.font = '9px "Courier New", monospace';
      ctx.fillText('z Z', px + 6, py - 4);
    } else {
      // body
      ctx.fillStyle = inm.affective.stress > 80 ? C.alert : C.amber;
      ctx.fillRect(px - 4, py - 6 + bob, 8, 12);
      // head
      ctx.fillRect(px - 3, py - 12 + bob, 6, 5);
    }
    if (selected) {
      ctx.strokeStyle = C.wire;
      ctx.setLineDash([2, 2]);
      ctx.strokeRect(px - 9, py - 15, 18, 24);
      ctx.setLineDash([]);
      ctx.fillStyle = C.wire;
      ctx.font = '8px "Courier New", monospace';
      ctx.fillText(inm.name, px - 24, py - 18);
    }
  }

  function drawGhost(ghost, T, world) {
    const { x, y, kind } = ghost;
    if (!world.inGrid(x, y)) return;
    const ok = kind === 'wall'
      ? world.tiles[y][x].t === 'empty' && !world.tiles[y][x].obj
      : !world.canBuildAt(kind, x, y) ? false : true;
    const err = kind === 'wall' ? null : world.canBuildAt(kind, x, y);
    const valid = kind === 'wall' ? ok : !err;
    ctx.globalAlpha = 0.55;
    ctx.fillStyle = valid ? C.amber : C.alert;
    ctx.fillRect(x * T + 3, y * T + 3, T - 6, T - 6);
    ctx.globalAlpha = 1;
    if (kind === 'lamp' && valid) {
      ctx.strokeStyle = 'rgba(255,176,0,0.35)';
      ctx.setLineDash([4, 4]);
      ctx.beginPath();
      ctx.arc(x * T + T / 2, y * T + T / 2, T * 5, 0, 7);
      ctx.stroke();
      ctx.setLineDash([]);
    }
    if (kind === 'sensor' && valid) {
      ctx.strokeStyle = 'rgba(0,204,255,0.4)';
      ctx.setLineDash([4, 4]);
      ctx.beginPath();
      ctx.arc(x * T + T / 2, y * T + T / 2, T * 2.5, 0, 7);
      ctx.stroke();
      ctx.setLineDash([]);
    }
  }

  /* ---------------- CROSSLINK LAYER ---------------- */
  function drawCrosslink(state) {
    const T = SOP.TILE, world = state.world;

    // ghost outline of the bunker
    for (let y = 0; y < world.H; y++) for (let x = 0; x < world.W; x++) {
      const tl = world.tiles[y][x];
      if (tl.t !== 'empty') continue;
      ctx.strokeStyle = '#0a1418';
      ctx.strokeRect(x * T + 0.5, y * T + 0.5, T - 1, T - 1);
    }

    // inmates as faint dots
    for (const inm of world.inmates) {
      if (inm.dead) continue;
      ctx.fillStyle = 'rgba(0,204,255,0.35)';
      ctx.beginPath();
      ctx.arc(inm.tx * T + T / 2, inm.ty * T + T / 2, 4, 0, 7);
      ctx.fill();
    }

    // links
    for (const [a, b] of world.linksPairs()) {
      const x1 = a.x * T + T / 2, y1 = a.y * T + T / 2;
      const x2 = b.x * T + T / 2, y2 = b.y * T + T / 2;
      const powered = a.powered || b.powered;
      ctx.strokeStyle = powered ? C.wire : C.wireDim;
      ctx.lineWidth = powered ? 2 : 1;
      ctx.beginPath();
      const mx = (x1 + x2) / 2, my = (y1 + y2) / 2 + 10; // cable sag
      ctx.moveTo(x1, y1);
      ctx.quadraticCurveTo(mx, my, x2, y2);
      ctx.stroke();
      // pulse dot
      if (powered) {
        const t = (now / 900 + a.id * 0.13) % 1;
        const qx = (1 - t) * (1 - t) * x1 + 2 * (1 - t) * t * mx + t * t * x2;
        const qy = (1 - t) * (1 - t) * y1 + 2 * (1 - t) * t * my + t * t * y2;
        ctx.fillStyle = '#bdf4ff';
        ctx.beginPath(); ctx.arc(qx, qy, 2.4, 0, 7); ctx.fill();
      }
    }

    // nodes
    for (const d of world.devices) {
      const px = d.x * T + T / 2, py = d.y * T + T / 2;
      const def = SOP.OBJ[d.kind];
      const col = d.broken ? C.alert : (d.powered ? C.wire : C.wireDim);
      ctx.strokeStyle = col;
      ctx.lineWidth = 1.5;
      ctx.strokeRect(px - 9, py - 9, 18, 18);
      ctx.fillStyle = col;
      ctx.font = '11px "Courier New", monospace';
      ctx.fillText(def.icon, px - 5, py + 4);
      // watts label
      const w = def.watts || 0;
      if (w !== 0) {
        ctx.fillStyle = col;
        ctx.font = '8px "Courier New", monospace';
        ctx.fillText((w < 0 ? '+' : '−') + Math.abs(w) + 'W', px - 12, py + 19);
      }
      if (d.kind === 'sensor' && d.triggered) {
        ctx.strokeStyle = 'rgba(0,255,102,0.7)';
        ctx.beginPath();
        ctx.arc(px, py, 12 + Math.sin(now / 150) * 2, 0, 7);
        ctx.stroke();
      }
      if (state.linkFrom === d.id) {
        ctx.strokeStyle = C.ok;
        ctx.setLineDash([3, 3]);
        ctx.strokeRect(px - 13, py - 13, 26, 26);
        ctx.setLineDash([]);
      }
      if (d.kind === 'gas_vent') {
        ctx.fillStyle = C.gas;
        ctx.font = '8px "Courier New", monospace';
        ctx.fillText('GAS', px - 9, py - 13);
      }
      if (d.kind === 'battery') {
        const f = d.charge / SOP.BATTERY_CAP;
        ctx.fillStyle = '#04222b';
        ctx.fillRect(px - 9, py - 16, 18, 4);
        ctx.fillStyle = f > 0.25 ? C.wire : C.alert;
        ctx.fillRect(px - 9, py - 16, 18 * f, 4);
      }
    }
  }

  window.addEventListener('resize', resize);

  return { draw, setView, getView, toTile, shake, resize };
})();
