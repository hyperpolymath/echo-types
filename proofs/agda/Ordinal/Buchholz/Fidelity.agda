{-# OPTIONS --without-K #-}

-- hypatia: allow code_safety/agda_postulate -- order-type fidelity for the Buchholz notation (D-2026-06-14) is external mathematics; the three named postulates below are the explicit, documented trust boundary. This module is OUTSIDE the --safe kernel cone by design, is NOT imported by All.agda/Smoke.agda, and asserts NOTHING that the --safe core depends on. See Fidelity-OPEN-postulates.md.

-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

-- Order-type fidelity SCAFFOLD for the Bachmann–Howard milestone
-- (open problem D-2026-06-14). 2026-06-14.
--
-- ## What this module IS
--
-- The *typed shape* of the order-type fidelity claim, with the hard
-- content left as three explicitly-named `postulate`s. Its job is to
-- make the absence of order-type fidelity VISIBLE and AUDITABLE — a
-- `grep postulate` here returns the complete, honest list of trust
-- boundaries — NOT to fabricate the proof.
--
-- ## What this module is NOT (read before trusting anything here)
--
--   * It does NOT prove that `_<ᵇ²_` has order type ψ₀(Ω_ω). That
--     claim is OPEN (decision-log D-2026-06-14). Nothing here asserts
--     it as established.
--   * It does NOT touch, reuse, or "tighten" `rank2`. `rank2` is the
--     deliberately HEIGHT-COLLAPSING termination measure (it maps the
--     whole ν≤ω fragment below ω^(ω+2), is monotone but neither
--     order-reflecting nor cofinal). It is sufficient for
--     well-foundedness and USELESS for order-type fidelity. Fidelity
--     needs a DIFFERENT object — the height-preserving denotation
--     `⟦·⟧` postulated below — which this module never conflates with
--     `rank2`.
--   * It is OUTSIDE the `--safe` kernel cone (pragma `--without-K`
--     only, matching `EchoImageFactorizationPropPostulated`). It is
--     NOT wired into `All.agda` / `Smoke.agda`. A `--safe` module may
--     not import it; the `--safe` core therefore depends on none of
--     these postulates.
--
-- ## The claim, quantified over the SOUND carrier only
--
-- Fidelity is stated over `_<ᵇ²_` restricted to well-formed terms
-- (`WfBT`) — the ordinally-sound carrier. NEVER over native `_<ᵇ_`
-- (ordinally unsound; the `<ᵇ-+Ω` counterexample) nor any
-- global-native surface. The same denotation extends to the
-- congruence closures `_<ᵇʳᶠ²_` / `_<ᵇ⁺²_` (same carrier), but the
-- order-type statement is made for `_<ᵇ²_`.
--
-- ## The sandwich
--
-- "order type ψ₀(Ω_ω)" is decomposed into a cofinal order-embedding
-- of the sound carrier into a postulated Bachmann–Howard structure:
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
--   * `bh-notation`         — a CHECKED Bachmann–Howard order structure
--                             (external mathematics).
--   * `denotation`          — the height-preserving order-embedding
--                             `⟦·⟧` + its fidelity fields (the missing
--                             object).
--   * `ordinal-upper-bound` — the ⟦·⟧-level upper bound (closable from
--                             `markers-≤ω` + a height calc through the
--                             real `⟦·⟧`, once `denotation` is real).
--
-- See Fidelity-OPEN-postulates.md for each postulate's owner + what
-- external mathematics discharges it.

module Ordinal.Buchholz.Fidelity where

open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Induction.WellFounded using (WellFounded)

open import Ordinal.OmegaMarkers using (OmegaIndex; fin; ω; _≤Ω_; fin≤ω; ω≤ω)
open import Ordinal.Buchholz.Syntax using (BT; bzero; bOmega; bplus; bpsi)
open import Ordinal.Buchholz.WellFormed using (WfBT; BH; BH-wf)
open import Ordinal.Buchholz.RankDoubledLadderUmbrella using (_<ᵇ²_)

----------------------------------------------------------------------
-- 1. Target-structure INTERFACE (not an implementation)
----------------------------------------------------------------------

-- An abstract well-founded strict order with a distinguished element
-- `bh-height` standing for the order type ψ₀(Ω_ω). The CONSTRUCTION of
-- a concrete, checked instance is external mathematics — postulated
-- below as the trust boundary, never built here.
record BHNotation : Set₁ where
  field
    𝒪         : Set
    _<𝒪_      : 𝒪 → 𝒪 → Set
    wf-<𝒪     : WellFounded _<𝒪_
    bh-height : 𝒪        -- the element whose initial segment is ψ₀(Ω_ω)

----------------------------------------------------------------------
-- 2. The denotation SPEC (interface-level; ⟦·⟧ is NOT implemented)
----------------------------------------------------------------------

-- The height-preserving order-embedding the fidelity claim needs — the
-- object `rank2` is NOT (rank2 collapses heights). Stated as a record
-- of named fields; its inhabitant is postulated, not built. Defined
-- before the top-level `open BHNotation bh-notation` so the record's
-- own `open BHNotation N` is the only `𝒪` in its scope.
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

-- TRUST BOUNDARY #1. Supplying a checked Bachmann–Howard structure is
-- external mathematics (owner / external). This postulate is the
-- assumption that such a structure exists; nothing here constructs it.
postulate
  bh-notation : BHNotation

open BHNotation bh-notation

-- TRUST BOUNDARY #2. The faithful, height-preserving denotation is the
-- missing object. This postulate assumes it exists; this module makes
-- its absence typed, not filled.
postulate
  denotation : DenotesBH bh-notation

open DenotesBH denotation

----------------------------------------------------------------------
-- 3a. The lower-bound half — REAL (plumbs the postulated `pins-BH`)
----------------------------------------------------------------------

-- The BH height is attained by a well-formed carrier element, namely
-- `BH = ψ₀(Ω_ω)` itself. This is a genuine term (no postulate of its
-- own) — it assembles `BH`, `BH-wf`, and the `pins-BH` field of the
-- postulated denotation. It does NOT independently establish fidelity;
-- it is the lower half CONDITIONAL on `denotation`.
fidelity-lower : Σ BT (λ t → WfBT t × (⟦ t ⟧ ≡ bh-height))
fidelity-lower = BH , (BH-wf , pins-BH)

----------------------------------------------------------------------
-- 3b. The upper-bound half — ⟦·⟧-DEPENDENT ⇒ postulated
----------------------------------------------------------------------

-- TRUST BOUNDARY #3. "No well-formed carrier element denotes above the
-- BH height." This quantifies over the postulated `⟦·⟧`, so it cannot
-- be a real term here. Its GRAMMAR-LEVEL shadow (`markers-≤ω`, §5) is
-- proved for real; the step from that shadow to this ⟦·⟧-level bound
-- is the height calculation through a real `⟦·⟧`, available once
-- `denotation` is discharged.
postulate
  ordinal-upper-bound : ∀ {t} → WfBT t → ¬ (bh-height <𝒪 ⟦ t ⟧)

----------------------------------------------------------------------
-- 4. The sandwich theorem — STATED + assembled from the two halves
----------------------------------------------------------------------

-- "_<ᵇ²_ on well-formed terms has order type ψ₀(Ω_ω)", as a cofinal
-- order-embedding into `bh-notation` with the BH term pinned to the
-- height. The TYPE is mechanised and auditable; the CONTENT is the
-- three postulates above plus the real `fidelity-lower`.
record OrderTypeBH : Set where
  field
    upper           : ∀ {t} → WfBT t → ¬ (bh-height <𝒪 ⟦ t ⟧)
    lower           : Σ BT (λ t → WfBT t × (⟦ t ⟧ ≡ bh-height))
    embeds-preserve : ∀ {s t} → WfBT s → WfBT t → s <ᵇ² t → ⟦ s ⟧ <𝒪 ⟦ t ⟧
    embeds-reflect  : ∀ {s t} → WfBT s → WfBT t → ⟦ s ⟧ <𝒪 ⟦ t ⟧ → s <ᵇ² t

-- The assembly is honest plumbing of the (postulated) parts into the
-- conclusion type — NOT an independent proof. `fidelity` is only as
-- strong as its three postulates; with them OPEN, this asserts the
-- SHAPE of fidelity, not fidelity.
fidelity : OrderTypeBH
fidelity = record
  { upper           = ordinal-upper-bound
  ; lower           = fidelity-lower
  ; embeds-preserve = preserve
  ; embeds-reflect  = reflect
  }

----------------------------------------------------------------------
-- 5. The one thing proved FOR REAL: the grammar-level upper shadow
----------------------------------------------------------------------

-- Every Ω-marker occurring in a Buchholz term is ≤Ω ω. This follows
-- cheaply from the constructor shapes (OmegaIndex is exactly
-- `fin n | ω`, so ω is the top). It is the honest, postulate-free
-- content of "the carrier lives in the ν≤ω fragment" — i.e. the
-- notation never names a marker above Ω_ω. It is the STRUCTURAL
-- PRECONDITION of `ordinal-upper-bound`, NOT that ⟦·⟧-level bound
-- itself (which needs the postulated denotation).

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
