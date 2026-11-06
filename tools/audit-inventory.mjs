// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
// Read-only inventory: Bun runtime filesystem/process APIs, no dependencies.
import { execFileSync } from 'node:child_process';
import { readFileSync, existsSync } from 'node:fs';
import { dirname, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';

const root = resolve(dirname(fileURLToPath(import.meta.url)), '..');
const excluded = new Set([
  'proofs/agda/EchoOrdinal.agda',
  'proofs/agda/Ordinal/OmegaMarkers.agda',
  'proofs/agda/Ordinal/Buchholz/Syntax.agda',
]);
const entrypoints = ['All', 'Smoke', 'characteristic/All', 'examples/All',
  'EchoImageFactorizationPropCubical', 'experimental/echo-additive/All', 'NarrowingSmoke'];
const git = (...args) => execFileSync('git', ['-C', root, ...args], { encoding: 'utf8', shell: false });
const paths = text => text.split('\0').filter(Boolean);
const tracked = new Set(paths(git('ls-files', '-z')));
const local = new Set([...tracked, ...paths(git('ls-files', '--others', '--exclude-standard', '-z'))]);
const agda = new Set([...local].filter(p => p.endsWith('.agda') && existsSync(resolve(root, p))));

// Nested block and line comments; preserve line boundaries for import matching.
function uncomment(text) {
  const result = [];
  let depth = 0;
  for (let i = 0; i < text.length;) {
    if (text.startsWith('{-', i)) { depth++; i += 2; }
    else if (depth && text.startsWith('-}', i)) { depth--; i += 2; }
    else if (!depth && text.startsWith('--', i)) {
      const newline = text.indexOf('\n', i);
      if (newline === -1) break;
      i = newline;
    } else { result.push(!depth || text[i] === '\n' ? text[i] : ' '); i++; }
  }
  return result.join('');
}
const edges = new Map([...agda].map(path => {
  const source = uncomment(readFileSync(resolve(root, path), 'utf8'));
  const imports = [...source.matchAll(/^\s*(?:open\s+)?import\s+([^\s;({]+)/gm)]
    .map(match => `proofs/agda/${match[1].replaceAll('.', '/')}.agda`)
    .filter(path => agda.has(path));
  return [path, imports];
}));
function closure(rootPath) {
  const seen = new Set(), pending = [rootPath];
  while (pending.length) {
    const path = pending.pop();
    if (seen.has(path) || excluded.has(path) || !agda.has(path)) continue;
    seen.add(path);
    pending.push(...edges.get(path).filter(p => !seen.has(p)));
  }
  return seen;
}
const closures = new Map(entrypoints.map(name => [name, closure(`proofs/agda/${name}.agda`)]));
const covered = new Set([...closures.values()].flatMap(set => [...set]));
const inScope = [...agda].filter(path => !excluded.has(path));
console.log(JSON.stringify({
  baseline_commit: git('rev-parse', 'HEAD').trim(),
  mode: 'working tree, including untracked unignored source files',
  tracked_files: tracked.size,
  local_unignored_files: local.size,
  agda_files: agda.size,
  in_scope_agda_files: inScope.length,
  excluded_paths: [...excluded].filter(path => agda.has(path)).sort(),
  entrypoint_closure_sizes: Object.fromEntries([...closures].map(([name, set]) => [name, set.size])),
  covered_in_scope: covered.size,
  outside_closures: inScope.filter(path => !covered.has(path)).sort(),
  method: 'static repository-local import traversal; not typechecking evidence',
}, null, 2));
