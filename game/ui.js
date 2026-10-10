/* ===========================================================================
   UI — inspector panels, build menu, event log, overlays.
   =========================================================================== */
window.SOP = window.SOP || {};

SOP.UI = (() => {
  const $ = id => document.getElementById(id);

  const el = {
    sysPower: $('sys-power'),
    sysO2: $('sys-o2'),
    sysInmates: $('sys-inmates'),
    sysRes: $('sys-res'),
    sysDay: $('sys-day'),
    inspector: $('ai-inspector'),
    devInspector: $('device-inspector'),
    buildMenu: $('build-menu'),
    buildHint: $('build-hint'),
    log: $('event-log'),
    ticker: $('ticker'),
    overlayIntro: $('overlay-intro'),
    overlayOver: $('overlay-over'),
    overStats: $('over-stats'),
  };

  let logLines = [];

  /* ---------------- EVENT LOG ---------------- */
  function log(msg, cls) {
    const day = SOP.Main ? SOP.Main.day() : 0;
    logLines.push({ msg, cls: cls || 'ok', day });
    if (logLines.length > 70) logLines.shift();
    el.log.innerHTML = logLines.map(l =>
      `<div class="l-${l.cls}"><span class="t">T${l.day}</span> ${l.msg}</div>`
    ).reverse().join('');
  }

  function alert(msg) {
    log(msg, 'alert');
    if (SOP.Audio.on) SOP.Audio.alarm();
  }

  function wire(msg) { log(msg, 'wire'); }

  /* ---------------- TICKER ---------------- */
  function setTicker(extra) {
    const lines = extra ? [extra, ...SOP.TICKER_LINES] : SOP.TICKER_LINES;
    el.ticker.textContent = lines.join('  ///  ') + '  ///  ';
    if (extra) {
      el.ticker.style.color = 'var(--alert)';
      setTimeout(() => { el.ticker.style.color = ''; }, 6000);
    }
  }

  /* ---------------- BUILD MENU ---------------- */
  function initBuildMenu(onSelect) {
    let html = '';
    for (const kind of SOP.BUILDABLE) {
      const d = SOP.OBJ[kind];
      const w = d.watts ? `${d.watts < 0 ? '+' : '−'}${Math.abs(d.watts)}W` : '·';
      html += `<button class="build-item" data-kind="${kind}" title="${d.hint}">
        <span class="ico">${d.icon}</span>${d.label}<span class="watt">${w}</span></button>`;
    }
    html += `<button class="build-item" data-kind="wall" title="Betonwand. Blockiert Gas und Wege.">
        <span class="ico">▬</span>WAND<span class="watt">−4B</span></button>`;
    html += `<button class="build-item" data-kind="dig" title="Erde als Grabungsauftrag markieren.">
        <span class="ico">⛏</span>GRABEN<span class="watt">AUFTRAG</span></button>`;
    el.buildMenu.innerHTML = html;
    el.buildMenu.querySelectorAll('.build-item').forEach(b => {
      b.addEventListener('click', () => {
        el.buildMenu.querySelectorAll('.build-item').forEach(x => x.classList.remove('selected'));
        b.classList.add('selected');
        onSelect(b.dataset.kind);
        const kind = b.dataset.kind;
        if (kind === 'dig') el.buildHint.textContent = 'AUFTRAG: ERDFELD ANKLICKEN. SUBJEKTE GRABEN SELBST.';
        else if (kind === 'wall') el.buildHint.textContent = 'WAND: HOHLRAUM ANKLICKEN. BLOCKIERT GAS & WEGE.';
        else el.buildHint.textContent = SOP.OBJ[kind].hint + ' — ' + costText(SOP.OBJ[kind].cost);
      });
    });
    el.buildHint.textContent = 'MODUL WÄHLEN, DANN IM HOHLRAUM PLATZIEREN. ESC BRICHT AB.';
  }

  function costText(cost) {
    const parts = [];
    for (const k in cost) parts.push(cost[k] + ' ' + k.toUpperCase());
    return parts.length ? 'KOSTET ' + parts.join(', ') : 'GRATIS';
  }

  function clearBuildSelection() {
    el.buildMenu.querySelectorAll('.build-item').forEach(x => x.classList.remove('selected'));
  }

  /* ---------------- SYSTEM PANEL ---------------- */
  function updateSystem(world, day) {
    el.sysDay.textContent = day;
    const p = world.power;
    const cls = p.deficit > 0 ? 'crit' : '';
    const powerHtml = `${Math.round(p.gen)}W/${Math.round(p.draw)}W ${p.deficit > 0 ? '<b class="blink">DEFIZIT</b>' : 'OK'}`;
    el.sysPower.innerHTML = `<span class="${cls}">${powerHtml}</span>`;
    const det = $('sys-power-detail');
    if (det) det.innerHTML = `${Math.round(p.gen)} W erzeugt / ${Math.round(p.draw)} W Last · ${p.components} Netz(e) · AKKU ${Math.round(p.stored || 0)}${p.deficit > 0 ? ' · <span style="color:var(--alert)">DEFIZIT ' + Math.round(p.deficit) + ' W</span>' : ''}`;
    // average O2 over empty tiles
    let o2 = 0, n = 0, gas = 0;
    for (let y = 0; y < world.H; y++) for (let x = 0; x < world.W; x++) {
      const t = world.tiles[y][x];
      if (t.t === 'empty') { o2 += t.o2; gas += t.gas; n++; }
    }
    const avg = n ? o2 / n : 0, avgGas = n ? gas / n : 0;
    el.sysO2.innerHTML = `Ø ${avg.toFixed(1)}% ${avgGas > 3 ? `· GAS ${avgGas.toFixed(1)}` : ''}`;
    el.sysO2.className = avg < 40 ? 'crit' : '';
    el.sysInmates.textContent = world.inmates.filter(i => !i.dead).length;
    el.sysRes.innerHTML =
      `<span title="Beton">B:${world.res.beton}</span> ` +
      `<span title="Metall">M:${world.res.metall}</span> ` +
      `<span title="Rationen">R:${world.res.rationen}</span> ` +
      `<span title="Öl" style="color:${world.res.oel < 20 ? 'var(--alert)' : ''}">Ö:${world.res.oel}</span>`;
  }

  /* ---------------- SUBJECT INSPECTOR ---------------- */
  const NEED_LABEL = { stress: 'STRESS', hunger: 'HUNGER', exhaustion: 'ERSCHÖPFUNG', paranoia: 'ARGWOHN', o2: 'O₂-MANGEL' };

  function updateInspector(world, selected) {
    if (!selected || selected.dead) {
      el.inspector.innerHTML = `<div class="panel-title">SUBJEKT-INSPEKTOR</div>
        <div class="empty">Subjekt im Raster anklicken, um affektive und konative Ströme zu überwachen.</div>`;
      return;
    }
    const A = selected.affective;
    let bars = '';
    for (const k of SOP.NEEDS) {
      const v = Math.max(0, Math.min(100, A[k]));
      const warn = v > 75 ? ' warn' : '';
      bars += `<div class="needrow"><div class="lbl"><span>${NEED_LABEL[k]}</span><span>${v.toFixed(1)}%</span></div>
        <div class="bar"><div class="${warn}" style="width:${v}%"></div></div></div>`;
    }
    const act = selected.currentAction;
    el.inspector.innerHTML = `
      <div class="panel-title">SUBJEKT-INSPEKTOR</div>
      <div class="kv"><span class="k">ID</span><span>${selected.name}</span></div>
      <div class="kv"><span class="k">PROFIL</span><span>${selected.trait}</span></div>
      <div class="kv"><span class="k">VITAL</span><span>${selected.hp.toFixed(0)} / 100</span></div>
      <div style="color: var(--text-dim); margin-top:8px">// AFFEKTIVER ZUSTAND</div>
      ${bars}
      <div class="directive-line">
        <div style="color: var(--text-dim)">// KONATIVER PROZESSOR</div>
        <div>DIREKTIVE: <span class="directive"><strong>${act.name}</strong></span></div>
        <div class="kv"><span class="k">NUTZWERT</span><span>${act.score.toFixed(1)}</span></div>
        <div class="kv"><span class="k">GEDANKE</span><span>„${selected.thought}"</span></div>
      </div>`;
  }

  /* ---------------- DEVICE INSPECTOR (crosslink) ---------------- */
  function updateDevicePanel(world, dev, mode) {
    if (!dev) {
      el.devInspector.innerHTML = `<div class="panel-title">KNOTEN-INSPEKTOR</div>
        <div class="empty">${mode === 'CROSSLINK' ? 'Knoten anklicken. Zwei Knoten = Leitung.' : 'Nur im CROSSLINK-Modus.'}</div>`;
      return;
    }
    const def = SOP.OBJ[dev.kind];
    el.devInspector.innerHTML = `
      <div class="panel-title">KNOTEN-INSPEKTOR</div>
      <div class="kv"><span class="k">TYP</span><span>${def.label}</span></div>
      <div class="kv"><span class="k">LAST</span><span>${def.watts ? (def.watts < 0 ? '−' + Math.abs(def.watts) + ' W (ERZEUGER)' : '+' + def.watts + ' W') : 'PASSIV'}</span></div>
      <div class="kv"><span class="k">STATUS</span><span style="color:${dev.broken ? 'var(--alert)' : dev.powered ? 'var(--ok)' : 'var(--text-dim)'}">${dev.broken ? 'DEFEKT' : dev.powered ? 'AKTIV' : 'OHNE STROM'}</span></div>
      <div class="kv"><span class="k">SCHALTER</span><span>${dev.enabled === false ? 'AUS' : 'EIN'}</span></div>
      ${dev.kind === 'battery' ? `<div class="kv"><span class="k">LADUNG</span><span>${Math.round(dev.charge)} / ${SOP.BATTERY_CAP}</span></div>` : ''}
      ${dev.kind === 'generator' ? `<div class="kv"><span class="k">TANK</span><span>${dev.fueled === false ? 'LEER' : 'LÄUFT'}</span></div>` : ''}
      <div class="kv"><span class="k">LEITUNGEN</span><span>${dev.links.length}</span></div>
      <button class="btn" id="btn-toggle-dev" style="margin-top:8px; width:100%">
        ${dev.enabled === false ? 'EINSCHALTEN [E]' : 'ABSCHALTEN [E]'}</button>
      <div style="color: var(--text-dim); margin-top:6px; font-size:11px">ZWEITEN KNOTEN ANKLICKEN → LEITUNG LEGEN / TRENNEN (MAX ${SOP.LINK_RANGE} FELDER).</div>`;
    const tb = document.getElementById('btn-toggle-dev');
    if (tb) tb.addEventListener('click', () => SOP.UI.toggleDevice(dev));
  }

  function toggleDevice(dev) {
    dev.enabled = dev.enabled === false ? true : false;
    if (dev.kind === 'dynamo' && dev.enabled === false) dev.operatedBy = null;
    log(`${SOP.OBJ[dev.kind].label} ${dev.enabled === false ? 'ABGESCHALTET' : 'EINGESCHALTET'}.`, 'dim');
  }

  /* ---------------- OVERLAYS ---------------- */
  function showIntro(onStart) {
    el.overlayIntro.classList.add('show');
    $('btn-start').addEventListener('click', () => {
      el.overlayIntro.classList.remove('show');
      onStart();
      const ab = $('btn-audio');
      if (ab && SOP.Audio.on) ab.textContent = 'Ton aus';
    });
  }

  function showGameOver(stats, onRestart) {
    el.overStats.innerHTML = stats;
    el.overlayOver.classList.add('show');
    $('btn-restart').addEventListener('click', () => {
      el.overlayOver.classList.remove('show');
      onRestart();
    });
  }

  return {
    log, alert, wire, setTicker,
    initBuildMenu, clearBuildSelection,
    updateSystem, updateInspector, updateDevicePanel, toggleDevice,
    showIntro, showGameOver,
  };
})();
