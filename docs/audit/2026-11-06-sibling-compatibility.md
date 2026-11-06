<!-- SPDX-License-Identifier: CC-BY-SA-4.0 -->
<!-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell -->

# Sibling integration compatibility — 2026-11-06

This is the executed local follow-up to the [source-only bridge inventory](2026-11-06-bridge-inventory.md).
It preserves the exact commands, source identities and warnings from the isolated
check stage. Raw WSL receipt paths below are local-only and are not usable as
remote-checkout links; this tracked report provides the distributable summary.

## Result and scope

All three requested positive integration roots passed with unchanged sibling source and their original proof profiles, using Echo's Agda 2.7.0.1 and stdlib v2.3 checkout. No contract/typechecking break was observed in this bounded import cone.

| Root | UTC start–finish | Exit | Emitted warnings |
|---|---|---:|---:|
| epistemic CanonicalEcho | 16:38:23–16:38:43 | 0 | 0, with its existing UnsupportedIndexedMatch suppression |
| residual EchoComparison | 16:38:43–16:39:08 | 0 | 33 UnsupportedIndexedMatch diagnostics, all from stdlib |
| residual EpistemicComparison | 16:39:08–16:39:10 | 0 | 0 |

These roots import Echo, EchoResidue and (transitively) EchoCharacteristic, not the new dependent-pushforward, source-preserving, CNO, or graded-comonad modules. This is current core/residue interface compatibility, not a check of every sibling module or every new Echo theorem. Negative fixtures and complete sibling CI scripts were not rerun.

## Exact sources and toolchain

Isolated directory: `/var/tmp/echo-sibling-compat-20261106`.

- epistemic-types: `a4a7a533f11996e9f57e67466566d950322b0d4f`.
- residual-evidence-types: `14c93f4e19aaacbcfeca91bf5f2368d3e7b5a4bc`.
- Compiler: `/tmp/echo-audit-20261106.xrmuUy/agda/bin/agda`, reporting exactly `Agda version 2.7.0.1`.
- Compiler binary SHA256: `6de41437c14c05c9fe576d724cc67386444c0fa9fee662a08250fefb91bee8b6`.
- `Agda_datadir=/tmp/echo-audit-20261106.xrmuUy/agda/data`.
- stdlib: `/tmp/echo-audit-20261106.xrmuUy/stdlib`, commit `8326c7475af1fa456ca04a0203c168d5d7ff842b` (v2.3); tracked source clean.
- Echo include: `/tmp/echo-audit-20261106.xrmuUy/repo/proofs/agda`. Its Git base remains `cd85288dcce55191ad477c0fa7d1d2421514a0d3` with the coordinating audit snapshot, so that Git HEAD alone does not identify the checked source.
- The complete imported in-repository Echo cone below matches the current Windows workspace byte-for-byte. Echo and EchoResidue hashes were also identical before and after the checks.

| Imported Echo source | SHA256 |
|---|---|
| Echo.agda | `a2f4f767af325f462329739a890274b151b487ef731be2ac859c69476bce47c5` |
| EchoResidue.agda | `73d615f37e8e927188961f016cdc6758a2f5073f8f126c2b7345cc7ea30fb017` |
| EchoCharacteristic.agda | `d5ee1648b3dc31d4faa7e299275e216fe4b14a91ef0fab5ed064ee29a5cb2b34` |

Both isolated sibling checkouts had no tracked changes before or after compilation. No shared snapshot was synchronized or deleted. Compiler interface caches may be generated normally; `--ignore-interfaces` prevented them substituting for these source checks.

## Baseline differences inspected first

- Epistemic's original CanonicalEcho CI uses Agda 2.6.4.3, distro stdlib 2.1-4, and Echo commit `46cd1a32d4dcf1020f01dd1aab41f816742da10e`. Its original `-W error -W noUnsupportedIndexedMatch` policy was retained, not added to force success.
- Residual's original comparison runner uses Agda 2.6.4.3 and pins Echo `9c4b72b52972c7e084c8f569635eb01caef64e7a`, epistemic `dd948fbdddbdd06282cda8425e3e644e013c11ff`, and stdlib `97bc55e47367c562b3032bf104f2a00b19716f88`. Here those include paths deliberately point to the current Echo cone, requested current epistemic clone, and Echo stdlib 2.3.
- Residual's comparison flags have no `-W error` and no warning-category suppression; that profile was retained. Their roots declare safe/without-K. CanonicalEcho additionally declares cubical-compatible/exact-split/no-sized-types/no-guardedness in unchanged source.
- `--no-libraries`, `--ignore-interfaces`, `--double-check`, safe and without-K were retained throughout. No source edits, unsafe options or permissive-meta flags were used.

## Exact checkout and checking commands

The two destinations were initially absent. For each NAME/PIN pair above:

```bash
work=/var/tmp/echo-sibling-compat-20261106
mkdir -p "$work"
git init -q "$work/$NAME"
git -C "$work/$NAME" remote add origin "https://github.com/hyperpolymath/$NAME.git"
git -C "$work/$NAME" -c credential.helper= fetch -q --depth 1 origin "$PIN"
git -C "$work/$NAME" checkout -q --detach FETCH_HEAD
test "$(git -C "$work/$NAME" rev-parse HEAD)" = "$PIN"
```

Compiler commands were run sequentially under WSL `bash --noprofile --norc`, with output redirected to the named local logs:

```bash
base=/tmp/echo-audit-20261106.xrmuUy
work=/var/tmp/echo-sibling-compat-20261106
export Agda_datadir=$base/agda/data
export LC_ALL=C.UTF-8
prover=$base/agda/bin/agda

cd "$work/epistemic-types"
"$prover" --no-libraries --safe --without-K --cubical-compatible --double-check --ignore-interfaces \
  -W error -W noUnsupportedIndexedMatch \
  -i src -i tests/integration -i "$base/repo/proofs/agda" -i "$base/stdlib/src" \
  tests/integration/CanonicalEcho.agda

cd "$work/residual-evidence-types"
"$prover" --safe --without-K --no-libraries --ignore-interfaces --double-check \
  -i src -i tests/integration -i "$base/repo/proofs/agda" -i "$base/stdlib/src" \
  tests/integration/EchoComparison.agda

"$prover" --safe --without-K --no-libraries --ignore-interfaces --double-check \
  -i src -i tests/integration -i "$work/epistemic-types/src" \
  tests/integration/EpistemicComparison.agda
```

## Warning and raw-receipt detail

EchoComparison's 33 emitted `warning: -W[no]UnsupportedIndexedMatch` headers refer to four stdlib spans in `Relation/Nullary/Decidable.agda`:

| Span | Emitted occurrences |
|---|---:|
| 63,3-27 | 9 |
| 81,1-84 | 10 |
| 91,1-60 | 10 |
| 97,1-98,36 | 4 |

Repeated imported diagnostics are not 33 distinct defects. They record the compiler's Cubical transport computation limitation; successful typechecking is not warning-free computation. CanonicalEcho's zero emitted count is conditional on its retained category suppression; no unsuppressed diagnostic run was used to claim zero underlying warnings.

Raw logs remain local WSL files in `/var/tmp/echo-sibling-compat-20261106/logs/`, not committed remote evidence:

| Log | SHA256 |
|---|---|
| CanonicalEcho.log | `047f47799ceef40c995a9cfd3e6d134f56158b1dac2322a5ad050d7810cd2543` |
| EchoComparison.log | `52f6a98e222aa2ee6570cabb5a01e9c211fe71adbef03ad68b231ec83fd8d7cc` |
| EpistemicComparison.log | `2429e1a1c3ba99fa66b0880e29406255fd4b889f18e6d69c19397ad5c3dabd33` |

The initial import-listing helper found `rg` unavailable in WSL and was rerun with `grep`; no compiler check failed for this utility issue. The original execution stage wrote only its ignored Windows-workspace summary; it changed no tracked source, created no commit or push, and made no remote sibling-repository mutation. This document promotes that summary into tracked documentation; the raw logs remain local-only.
