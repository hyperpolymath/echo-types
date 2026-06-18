{-# OPTIONS --without-K #-}

-- hypatia: allow code_safety/agda_postulate -- order-type fidelity for the Buchholz notation (D-2026-06-14) is external mathematics; the TWO named postulates below (denotation, ordinal-upper-bound) are the explicit, documented trust boundary. The former third postulate (the whole BH structure) is now CONSTRUCTED for real in the --safe module Ordinal.Buchholz.BHTarget; only the candidate BH height remains, as an explicit module parameter (AtHeight). This module is OUTSIDE the --safe kernel cone by design, is NOT imported by All.agda/Smoke.agda, and asserts NOTHING that the --safe core depends on. See Fidelity-OPEN-postulates.md.

-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

-- Order-type fidelity SCAFFOLD for the Bachmann–Howard milestone
-- (open problem D-2026-06-14). 2026-06-14; trust boundary reduced
-- 2026-06-15 (BH target structure constructed — see BHTarget.agda).
--
-- ## What this module IS
--
-- The *typed shape* of the order-type fidelity claim. As of the
-- 2026-06-15 reduction the hard content is TWO explicitly-named
-- `postulate`s (down from three). Its job is to make the absence of
-- order-type fidelity VISIBLE and AUDITABLE — a `grep postulate` here
-- returns the complete, honest list of trust boundaries — NOT to
-- fabricate the proof.
--
-- ## Trust-boundary reduction (2026-06-15)
--
-- The target Bachmann–Howard STRUCTURE is no longer postulated. The
-- abstract interface `BHNotation` and a concrete, postulate-free
-- instance `bh-notation-from` now live in the --safe kernel module
-- `Ordinal.Buchholz.BHTarget`, which wires in the repo's real Brouwer
-- ordinal order:
--
--   𝒪 := Ord, _<𝒪_ := _<′_, wf-<𝒪 := wf-<′   (all REAL, --safe).
--
-- So the TARGET ORDER AND ITS WELL-FOUNDEDNESS are now proved, not
-- assumed. The only remaining free input is WHICH `Ord` value plays the
-- BH height — handed in as the explicit module parameter `bh-height-ord`
-- to `module AtHeight`. Its ψ₀(Ω_ω)-meaning is pinned downstream by the
-- (still-open) `denotation.pins-BH` field, not by fiat.
--
-- ## What this module is NOT (read before trusting anything here)
--
--   * It does NOT prove that `_<ᵇ²_` has order type ψ₀(Ω_ω). That
--     claim is OPEN (decision-log D-2026-06-14). Nothing here asserts
--     it as established.
--   * It does NOT touch, reuse, or "tighten" `rank2`. `rank2` is the
--     deliberately HEIGHT-COLLAPSING termination measure (monotone but
--     neither order-reflecting nor cofinal). Fidelity needs a DIFFERENT
--     object — the height-preserving denotation `⟦·⟧` postulated below —
--     which this module never conflates with `rank2`. (`bh-notation-from`
--     fixes only the order, not the embedding, so it does not prejudge
--     `denotation`.)
--   * It is OUTSIDE the `--safe` kernel cone (pragma `--without-K` only,
--     because of the two postulates). It is NOT wired into `All.agda` /
--     `Smoke.agda`. A `--safe` module may not import it; the `--safe`
--     core therefore depends on none of these postulates. (`BHTarget`,
--     by contrast, IS `--safe` and IS in `All.agda` — its content is
--     real and kernel-grade.)
--
-- ## The claim, quantified over the SOUND carrier only
--
-- Fidelity is stated over `_<ᵇ²_` restricted to well-formed terms
-- (`WfBT`) — the ordinally-sound carrier. NEVER over native `_<ᵇ_`
-- (ordinally unsound; the `<ᵇ-+Ω` counterexample) nor any global-native
-- surface.
--
-- ## The sandwich
--
--   upper half:  no well-formed term denotes ABOVE the BH height
--                (`ordinal-upper-bound`, ⟦·⟧-dependent ⇒ postulated;
--                 its grammar-level shadow `markers-≤ω` is proved for
--                 real below);
--   lower half:  the BH height IS attained, by the well-formed term
--                `BH = ψ₀(Ω_ω)` itself (`fidelity-lower`, REAL given
--                 the postulated denotation's `pins-BH` field);
--   embedding:   `preserve` + `reflect` (faithfulness, from the
--                postulated denotation).
--
-- ## Trust boundary (grep `postulate`)
--
--   * `denotation`          — the height-preserving order-embedding
--                             `⟦·⟧` + its fidelity fields (the missing
--                             object).
--   * `ordinal-upper-bound` — the ⟦·⟧-level upper bound (closable from
--                             `markers-≤ω` + a height calc through the
--                             real `⟦·⟧`, once `denotation` is real).
--
-- (The former `bh-notation` postulate is discharged — the structure is
-- now constructed in BHTarget.agda; the candidate height is the
-- `AtHeight` parameter.)
--
-- See Fidelity-OPEN-postulates.md for each postulate's owner + what
-- external mathematics discharges it.

module Ordinal.Buchholz.Fidelity where

open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Ordinal.OmegaMarkers using (OmegaIndex; fin; ω; _≤Ω_; fin≤ω; ω≤ω)
open import Ordinal.Buchholz.Syntax using (BT; bzero; bOmega; bplus; bpsi)
open import Ordinal.Buchholz.WellFormed using (WfBT; BH; BH-wf)
open import Ordinal.Buchholz.RankDoubledLadderUmbrella using (_<ᵇ²_)

open import Ordinal.Brouwer using (Ord)
open import Ordinal.Buchholz.BHTarget using (BHNotation; bh-notation-from)

----------------------------------------------------------------------
-- 1. Target-structure INTERFACE — now REAL, in Ordinal.Buchholz.BHTarget
----------------------------------------------------------------------

-- `record BHNotation` (abstract well-founded strict order + distinguished
-- element) and the postulate-free `bh-notation-from : Ord → BHNotation`
-- (the Brouwer-order instance) are imported above from the --safe kernel
-- module `BHTarget`. The target order and its well-foundedness are
-- therefore proved, not assumed; see BHTarget.agda for the construction.

----------------------------------------------------------------------
-- 2. The denotation SPEC (interface-level; ⟦·⟧ is NOT implemented)
----------------------------------------------------------------------

-- The height-preserving order-embedding the fidelity claim needs — the
-- object `rank2` is NOT (rank2 collapses heights). Stated as a record of
-- named fields over an arbitrary `BHNotation N`; its inhabitant is
-- postulated (per height) inside `AtHeight` below, not built.
record DenotesBH (N : BHNotation) : Set where
  open BHNotation N
  field
    ⟦_⟧      : BT → 𝒪
    -- order-preserving (the upper-bound-supporting half)
    preserve : ∀ {s t} → WfBT s → WfBT t → s <ᵇ² t → ⟦ s ⟧ <𝒪 ⟦ t ⟧
    -- order-reflecting (faithfulness; the lower-bound-supporting half)
    reflect  : ∀ {s t} → WfBT s → WfBT t → ⟦ s ⟧ <𝒪 ⟦ t ⟧ → s <ᵇ² t
    -- cofinality: the image is unbounded in 𝒪
    cofinal  : (o : 𝒪) → Σ BT (λ t → WfBT t × (o <𝒪 ⟦ t ⟧))
    -- the BH term denotes exactly the BH height
    pins-BH  : ⟦ BH ⟧ ≡ bh-height

----------------------------------------------------------------------
-- 3. The one thing proved FOR REAL: the grammar-level upper shadow
----------------------------------------------------------------------

-- Every Ω-marker occurring in a Buchholz term is ≤Ω ω. This follows
-- cheaply from the constructor shapes (OmegaIndex is exactly
-- `fin n | ω`, so ω is the top). It is the honest, postulate-free
-- content of "the carrier lives in the ν≤ω fragment" — the STRUCTURAL
-- PRECONDITION of `ordinal-upper-bound`, NOT that ⟦·⟧-level bound itself.
-- Height-independent, so it lives at top level.

AllMarkers≤ω : BT → Set
AllMarkers≤ω bzero       = ⊤
AllMarkers≤ω (bOmega ν)  = ν ≤Ω ω
AllMarkers≤ω (bplus x y) = AllMarkers≤ω x × AllMarkers≤ω y
AllMarkers≤ω (bpsi ν α)  = (ν ≤Ω ω) × AllMarkers≤ω α

marker-≤ω : (ν : OmegaIndex) → ν ≤Ω ω
marker-≤ω (fin n) = fin≤ω
marker-≤ω ω       = ω≤ω

markers-≤ω : (t : BT) → AllMarkers≤ω t
markers-≤ω bzero       = tt
markers-≤ω (bOmega ν)  = marker-≤ω ν
markers-≤ω (bplus x y) = markers-≤ω x , markers-≤ω y
markers-≤ω (bpsi ν α)  = marker-≤ω ν , markers-≤ω α

----------------------------------------------------------------------
-- 4. The height-parameterised fidelity assembly
----------------------------------------------------------------------

-- Parameterised by the candidate BH height `bh-height-ord : Ord` — an
-- explicit hypothesis, NOT a postulate. The target structure is the real
-- Brouwer order at that height (`bh-notation-from`); only `denotation`
-- and `ordinal-upper-bound` are assumed.
module AtHeight (bh-height-ord : Ord) where

  bh-notation : BHNotation
  bh-notation = bh-notation-from bh-height-ord

  open BHNotation bh-notation

  -- TRUST BOUNDARY #1 (of 2). The faithful, height-preserving denotation
  -- into the (real) Brouwer order is the missing object. This postulate
  -- assumes it exists; this module makes its absence typed, not filled.
  -- AXIOM: denotation — assumed; OPEN proof-debt for order-type fidelity (D-2026-06-14); see docs/proof-debt.md (d) + Fidelity-OPEN-postulates.md. NOT a permanently accepted axiom — a hole to be discharged.
  postulate
    denotation : DenotesBH bh-notation

  open DenotesBH denotation

  --------------------------------------------------------------------
  -- 4a. The lower-bound half — REAL (plumbs the postulated `pins-BH`)
  --------------------------------------------------------------------

  -- The BH height is attained by a well-formed carrier element, namely
  -- `BH = ψ₀(Ω_ω)` itself. A genuine term (no postulate of its own): it
  -- assembles `BH`, `BH-wf`, and the `pins-BH` field. It does NOT
  -- independently establish fidelity; it is the lower half CONDITIONAL
  -- on `denotation`.
  fidelity-lower : Σ BT (λ t → WfBT t × (⟦ t ⟧ ≡ bh-height))
  fidelity-lower = BH , (BH-wf , pins-BH)

  --------------------------------------------------------------------
  -- 4b. The upper-bound half — ⟦·⟧-DEPENDENT ⇒ postulated
  --------------------------------------------------------------------

  -- TRUST BOUNDARY #2 (of 2). "No well-formed carrier element denotes
  -- above the BH height." This quantifies over the postulated `⟦·⟧`, so
  -- it cannot be a real term here. Its GRAMMAR-LEVEL shadow
  -- (`markers-≤ω`, §3) is proved for real; the step from that shadow to
  -- this ⟦·⟧-level bound is the height calculation through a real `⟦·⟧`,
  -- available once `denotation` is discharged.
  -- AXIOM: ordinal-upper-bound — assumed; OPEN proof-debt for order-type fidelity (D-2026-06-14); see docs/proof-debt.md (d) + Fidelity-OPEN-postulates.md. NOT a permanently accepted axiom — a hole to be discharged.
  postulate
    ordinal-upper-bound : ∀ {t} → WfBT t → ¬ (bh-height <𝒪 ⟦ t ⟧)

  --------------------------------------------------------------------
  -- 4c. The sandwich theorem — STATED + assembled from the two halves
  --------------------------------------------------------------------

  -- "_<ᵇ²_ on well-formed terms has order type ψ₀(Ω_ω)", as a cofinal
  -- order-embedding into `bh-notation` with the BH term pinned to the
  -- height. The TYPE is mechanised and auditable; the CONTENT is the two
  -- postulates above plus the real `fidelity-lower`. `fidelity` is only
  -- as strong as its postulates; with them OPEN, this asserts the SHAPE
  -- of fidelity, not fidelity.
  record OrderTypeBH : Set where
    field
      upper           : ∀ {t} → WfBT t → ¬ (bh-height <𝒪 ⟦ t ⟧)
      lower           : Σ BT (λ t → WfBT t × (⟦ t ⟧ ≡ bh-height))
      embeds-preserve : ∀ {s t} → WfBT s → WfBT t → s <ᵇ² t → ⟦ s ⟧ <𝒪 ⟦ t ⟧
      embeds-reflect  : ∀ {s t} → WfBT s → WfBT t → ⟦ s ⟧ <𝒪 ⟦ t ⟧ → s <ᵇ² t

  fidelity : OrderTypeBH
  fidelity = record
    { upper           = ordinal-upper-bound
    ; lower           = fidelity-lower
    ; embeds-preserve = preserve
    ; embeds-reflect  = reflect
    }
