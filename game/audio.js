/* Standard Operating Psychopathy — audio.
   Minimal cold-wave sequencer: motorik kick, dry hat, steely bass.
   Starts only after a user gesture. Toggle with [M]. */
window.SOP = window.SOP || {};

SOP.Audio = (() => {
  let ctx = null, master = null, running = false, nextNote = 0, step = 0;
  const BPM = 126, LOOKAHEAD = 0.12, INTERVAL = 40;
  let timer = null;

  /* A minor, one cold riff: A1 A1 E2 A1 / C2 A1 G1 A1, straight 16ths. */
  const BASS = [55, 55, 82.4, 55, 65.4, 55, 49, 55, 55, 55, 82.4, 55, 65.4, 98, 82.4, 55];
  const HAT_PATTERN = [0,0,1,0, 0,0,1,0, 0,0,1,0, 0,0,1,1];

  function init() {
    if (ctx) return;
    const AC = window.AudioContext || window.webkitAudioContext;
    if (!AC) return;
    ctx = new AC();
    master = ctx.createGain();
    master.gain.value = 0.5;
    master.connect(ctx.destination);
  }

  function kick(t) {
    const o = ctx.createOscillator(), g = ctx.createGain();
    o.type = 'sine';
    o.frequency.setValueAtTime(120, t);
    o.frequency.exponentialRampToValueAtTime(40, t + 0.09);
    g.gain.setValueAtTime(0.55, t);
    g.gain.exponentialRampToValueAtTime(0.001, t + 0.12);
    o.connect(g); g.connect(master);
    o.start(t); o.stop(t + 0.13);
  }

  function hat(t) {
    const len = 0.03;
    const buf = ctx.createBuffer(1, ctx.sampleRate * len, ctx.sampleRate);
    const d = buf.getChannelData(0);
    for (let i = 0; i < d.length; i++) d[i] = (Math.random() * 2 - 1) * (1 - i / d.length);
    const s = ctx.createBufferSource(); s.buffer = buf;
    const f = ctx.createBiquadFilter(); f.type = 'highpass'; f.frequency.value = 6000;
    const g = ctx.createGain(); g.gain.value = 0.08;
    s.connect(f); f.connect(g); g.connect(master);
    s.start(t);
  }

  function bass(t, freq) {
    const o = ctx.createOscillator(), g = ctx.createGain(), f = ctx.createBiquadFilter();
    o.type = 'sawtooth'; o.frequency.value = freq;
    f.type = 'lowpass'; f.frequency.setValueAtTime(900, t);
    f.frequency.exponentialRampToValueAtTime(180, t + 0.14);
    g.gain.setValueAtTime(0.16, t);
    g.gain.exponentialRampToValueAtTime(0.001, t + 0.16);
    o.connect(f); f.connect(g); g.connect(master);
    o.start(t); o.stop(t + 0.18);
  }

  function schedule() {
    while (nextNote < ctx.currentTime + LOOKAHEAD) {
      const s16 = step % 16;
      if (s16 % 4 === 0) kick(nextNote);
      if (HAT_PATTERN[s16]) hat(nextNote);
      bass(nextNote, BASS[s16]);
      nextNote += (60 / BPM) / 4;
      step++;
    }
  }

  function toggle() {
    init();
    if (!ctx) return false;
    if (running) {
      clearInterval(timer); running = false;
    } else {
      if (ctx.state === 'suspended') ctx.resume();
      nextNote = ctx.currentTime + 0.05; step = 0;
      timer = setInterval(schedule, INTERVAL);
      running = true;
    }
    return running;
  }

  /* One-shot alerts */
  function alarm() {
    if (!ctx || !running) return;
    const t = ctx.currentTime;
    const o = ctx.createOscillator(), g = ctx.createGain();
    o.type = 'square'; o.frequency.value = 440;
    o.frequency.setValueAtTime(440, t);
    o.frequency.setValueAtTime(330, t + 0.12);
    g.gain.setValueAtTime(0.12, t);
    g.gain.exponentialRampToValueAtTime(0.001, t + 0.3);
    o.connect(g); g.connect(master);
    o.start(t); o.stop(t + 0.32);
  }

  return { toggle, alarm, get on() { return running; } };
})();
