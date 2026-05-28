#!/usr/bin/env node
// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
//
// build-banner.mjs — Echo Types repository banner
// 1920×480, dark theorem-proof aesthetic, no dependencies.
//
// Run:  node tools/banner/build-banner.mjs
// Writes: docs/assets/banner.svg (PNG must be re-rasterised separately).

import { writeFileSync, mkdirSync } from 'node:fs';
import { fileURLToPath } from 'node:url';
import { dirname, join } from 'node:path';

const __dirname = dirname(fileURLToPath(import.meta.url));
const repoRoot = join(__dirname, '..', '..');
const outDir   = join(repoRoot, 'docs', 'assets');
const outPath  = join(outDir, 'banner.svg');

const W = 1920, H = 480;

const C = {
  bg:        '#0d1620',
  ink:       '#ede4d0',
  inkFaint:  '#9aa39c',
  base:      '#3a4555',
  baseFaint: '#26303a',
  amber:     '#c9a96e',
  title:     '#f0e8d4',
  subtitle:  '#7d8590',
};

const baseY  = 275;   // the horizontal "base space" axis
const constY = 232;   // vertical centre of each constellation

// ---- Constellation: 4-node square graph with two diagonals ------------------
const nodes = [
  { id: 'NW', x: -22, y: -16 },
  { id: 'NE', x:  22, y: -16 },
  { id: 'SW', x: -22, y:  16 },
  { id: 'SE', x:  22, y:  16 },
];
const edges = {
  N:  ['NW', 'NE'],
  E:  ['NE', 'SE'],
  S:  ['SW', 'SE'],
  W:  ['NW', 'SW'],
  D1: ['NW', 'SE'],
  D2: ['NE', 'SW'],
};
const all = ['N', 'E', 'S', 'W', 'D1', 'D2'];
// Order of edge loss across the procession — diagonals first, then square
const removalOrder = ['D2', 'D1', 'S', 'E', 'N', 'W'];

const nodeOf = id => nodes.find(n => n.id === id);

function edgesAt(stage) {
  const removed = new Set(removalOrder.slice(0, stage));
  return all.filter(e => !removed.has(e));
}

function constellation(cx, cy, stage, rot) {
  // Identity is preserved: nodes always at full ink. Only edges change.
  let g = `\n  <g transform="translate(${cx} ${cy}) rotate(${rot})">`;
  for (const e of edgesAt(stage)) {
    const [a, b] = edges[e];
    const A = nodeOf(a), B = nodeOf(b);
    const isDiag = e === 'D1' || e === 'D2';
    const sw  = isDiag ? 0.75 : 1.05;
    const opc = isDiag ? 0.78 : 0.96;
    g += `\n    <line x1="${A.x}" y1="${A.y}" x2="${B.x}" y2="${B.y}" stroke="${C.ink}" stroke-width="${sw}" stroke-linecap="round" opacity="${opc}"/>`;
  }
  for (const n of nodes) {
    g += `\n    <circle cx="${n.x}" cy="${n.y}" r="2.85" fill="${C.ink}"/>`;
  }
  g += `\n  </g>`;
  return g;
}

// ---- Fiber: vertical line descending below the axis, with residue marks -----
function fiber(cx, stage) {
  const top = baseY + 8;
  const bot = 412;
  const slots = 7;
  const ys = Array.from({ length: slots },
    (_, i) => top + (i + 0.5) * (bot - top) / slots);

  let g = `\n  <g>`;
  g += `\n    <line x1="${cx}" y1="${top}" x2="${cx}" y2="${bot}" stroke="${C.base}" stroke-width="0.5"/>`;
  const marks = Math.min(stage, slots);
  for (let i = 0; i < marks; i++) {
    const y = ys[i];
    // newest mark (topmost) slightly larger to read as "most recent loss"
    const r = i === marks - 1 ? 2.0 : 1.55;
    g += `\n    <circle cx="${cx}" cy="${y}" r="${r}" fill="${C.amber}"/>`;
  }
  g += `\n  </g>`;
  return g;
}

// ---- Stage positions: 4 left of the title block, 4 right --------------------
const stages = [
  { stage: 0, x:  160 },
  { stage: 1, x:  330 },
  { stage: 2, x:  500 },
  { stage: 3, x:  670 },
  // title gap roughly 720..1200
  { stage: 4, x: 1250 },
  { stage: 5, x: 1420 },
  { stage: 6, x: 1590 },
  { stage: 7, x: 1760 },
];

// ---- Compose ----------------------------------------------------------------
let svg = `<svg xmlns="http://www.w3.org/2000/svg" width="${W}" height="${H}" viewBox="0 0 ${W} ${H}">`;

// Ground
svg += `\n  <rect width="${W}" height="${H}" fill="${C.bg}"/>`;

// Corner registration marks — printer's-plate / specimen-sheet aesthetic
{
  const inset = 36, arm = 14, sw = 0.7;
  const corners = [
    { x: inset,       y: inset,       dx:  1, dy:  1 },
    { x: W - inset,   y: inset,       dx: -1, dy:  1 },
    { x: inset,       y: H - inset,   dx:  1, dy: -1 },
    { x: W - inset,   y: H - inset,   dx: -1, dy: -1 },
  ];
  svg += `\n  <g stroke="${C.base}" stroke-width="${sw}" fill="none">`;
  for (const c of corners) {
    svg += `\n    <line x1="${c.x}" y1="${c.y}" x2="${c.x + arm * c.dx}" y2="${c.y}"/>`;
    svg += `\n    <line x1="${c.x}" y1="${c.y}" x2="${c.x}" y2="${c.y + arm * c.dy}"/>`;
  }
  svg += `\n  </g>`;
}

// Base axis (dashed, very quiet)
svg += `\n  <line x1="80" y1="${baseY}" x2="${W - 80}" y2="${baseY}" stroke="${C.base}" stroke-width="0.6" stroke-dasharray="1 7"/>`;

// Tick marks at each stage position (project the fibers onto the axis)
for (const s of stages) {
  svg += `\n  <line x1="${s.x}" y1="${baseY - 3}" x2="${s.x}" y2="${baseY + 3}" stroke="${C.base}" stroke-width="0.6"/>`;
}

// Procession
for (const s of stages) {
  const rot = s.stage * 1.5;             // gentle accumulating rotation
  svg += fiber(s.x, s.stage);
  svg += constellation(s.x, constY + s.stage * 0.5, s.stage, rot);
}

// ---- Title block (centre of the page) ---------------------------------------
// Small tracked-out italic field-label hovering above the title
svg += `\n  <text x="${W/2}" y="198" font-family="IBM Plex Serif" font-style="italic" font-size="14.5" fill="${C.subtitle}" text-anchor="middle" letter-spacing="7.5">Proof-Relevant Information Residues</text>`;

// Main title — IBM Plex Serif, regular, restrained letter-spacing
svg += `\n  <text x="${W/2}" y="265" font-family="IBM Plex Serif" font-size="72" font-weight="400" fill="${C.title}" text-anchor="middle" letter-spacing="2">Echo Types</text>`;

svg += `\n</svg>\n`;

mkdirSync(outDir, { recursive: true });
writeFileSync(outPath, svg);
console.log(`Wrote ${outPath} (${svg.length} bytes)`);
