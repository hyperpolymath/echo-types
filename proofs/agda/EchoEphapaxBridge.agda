{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

-- Echo↔Ephapax L3 Bridge (NARROW — navigability + cross-repo cataloguing).
--
-- The ephapax programming-language project (hyperpolymath/ephapax)
-- carries a four-layer typing redesign whose L3 layer (`formal/Echo.v`,
-- 584 lines, 24 `Qed`, zero `Admitted` / zero `Axiom`) is an explicit
-- Coq port of `EchoLinear.agda` + `EchoResidue.agda` under a K-free /
-- zero-axiom discipline equivalent to `--safe --without-K`.  The Coq
-- headlines `mode_le_prop`, `weaken_collapses_distinction`,
-- `affine_canonical`, `degrade_mode_comp`, and
-- `no_section_collapse_to_residue` each carry the same theorem as the
-- Agda counterpart pinned here.
--
-- Scope (NARROW, per `/tmp/ephapax-bridge-proposal.md` §4): this
-- module is import-time documentation.  The cross-repo content
-- correspondence is already discharged by `coqc` on the ephapax side
-- (no Lane 4 CI dependency).  The two definitional `refl`-renames
-- below pin the load-bearing Agda symbols under `ephapax-`-prefixed
-- names so `MAP.adoc`'s "Directions" navigation has an ephapax row,
-- and so a silent upstream rename trips `Smoke.agda`.  A future
-- content bridge would require an Agda mirror of ephapax's
-- `formal/Echo.v` and is not foreclosed by this stub.
--
-- References:
--   * `docs/bridges/cross-repo-bridge-status.md` (when extended).
--   * `docs/echo-types/MAP.adoc` §"Directions" / "Ephapax L3".
--   * ephapax `formal/Echo.v:502-517` ↔
--     `EchoResidue.no-section-collapse-to-residue`.
--   * ephapax `formal/Echo.v` `weaken` ↔ `EchoLinear.weaken`.

module EchoEphapaxBridge where

open import EchoLinear  using (linear; affine; LEcho; weaken)
open import EchoResidue using (no-section-collapse-to-residue)

-- ephapax `formal/Echo.v` `weaken` — Coq port of this Agda symbol.
ephapax-L3-weaken : LEcho linear → LEcho affine
ephapax-L3-weaken = weaken

-- ephapax `formal/Echo.v` `no_section_collapse_to_residue`
-- (line 502-517, `Qed`, zero axioms) — Coq port of this Agda symbol.
ephapax-L3-no-section-collapse = no-section-collapse-to-residue
