/* DOM-level smoke test: loads index.html through jsdom, stubs the canvas 2D
   context, boots the real game (setup → intro click → sim ticks) and checks
   that nothing throws and state advances. */
const { JSDOM } = require('jsdom');
const fs = require('fs');
const path = require('path');

const root = path.join(__dirname, '..');
const html = fs.readFileSync(path.join(root, 'index.html'), 'utf8');
const dom = new JSDOM(html, { runScripts: 'outside-only', pretendToBeVisual: true });
const { window } = dom;

// ---- canvas 2D stub ----
const gradient = { addColorStop() {} };
const ctxStub = new Proxy({}, {
  get(t, key) {
    if (key === 'createRadialGradient' || key === 'createLinearGradient') return () => gradient;
    if (key === 'measureText') return () => ({ width: 10 });
    if (typeof key === 'symbol') return undefined;
    return () => {};
  },
  set() { return true; },
});
window.HTMLCanvasElement.prototype.getContext = function () { return ctxStub; };
// layout stubs
Object.defineProperty(window.HTMLElement.prototype, 'clientWidth', { get() { return 900; } });
Object.defineProperty(window.HTMLElement.prototype, 'clientHeight', { get() { return 600; } });
window.HTMLCanvasElement.prototype.getBoundingClientRect = () => ({ left: 0, top: 0, width: 900, height: 600 });

// ---- load game scripts in order ----
for (const f of ['config.js', 'audio.js', 'world.js', 'ai.js', 'render.js', 'ui.js', 'main.js']) {
  const src = fs.readFileSync(path.join(root, f), 'utf8');
  window.eval(src);
}

// ---- boot ----
window.document.dispatchEvent(new window.Event('DOMContentLoaded', { bubbles: true }));

setTimeout(() => {
  const SOP = window.SOP;
  const errs = [];
  const assert = (cond, msg) => { if (!cond) errs.push(msg); };

  assert(SOP.World.inmates.length === 3, 'three inmates registered');
  assert(SOP.World.devices.length >= 9, 'starter devices placed');

  // click through the intro
  const btn = window.document.getElementById('btn-start');
  assert(btn, 'btn-start exists');
  btn.click();

  // simulate some canvas interactions (mode toggles, build select)
  window.document.getElementById('btn-crosslink').click();
  window.document.getElementById('btn-physical').click();
  const digBtn = window.document.querySelector('.build-item[data-kind="dig"]');
  assert(digBtn, 'dig build item exists');
  digBtn.click();
  window.document.getElementById('btn-pause').click();
  window.document.getElementById('btn-pause').click();

  // let the sim run a while
  setTimeout(() => {
    const w = SOP.World;
    assert(w.inmates.some(i => i.currentAction.name !== 'IDLE'), 'inmates acting');
    assert(window.document.getElementById('event-log').children.length >= 2, 'log populated');
    assert(window.document.getElementById('ticker').textContent.length > 0, 'ticker running');
    assert(window.document.getElementById('sys-inmates').textContent === '3', 'HUD inmates');
    console.log('day:', SOP.Main.day(), '| inmates:', w.inmates.map(i => i.name + ':' + i.currentAction.name).join(' '));
    if (errs.length) { console.error('DOM TEST FAILED:\n' + errs.join('\n')); process.exit(1); }
    console.log('=== DOM TEST OK ===');
    process.exit(0);
  }, 4000);
}, 200);
