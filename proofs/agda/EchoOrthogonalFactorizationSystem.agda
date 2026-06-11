{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

-- EchoOrthogonalFactorizationSystem: the architectural keystone.
--
-- Every function `f : A → B` factors canonically as
--
--   A  ──≃──→  Σ B (Echo f)  ──proj₁──→  B
--      encode                   projection
--
-- The LEFT leg `encode f : A ↔ Σ B (Echo f)` is an equivalence
-- (totality completion; see `EchoTotalCompletion.A↔ΣEcho`).
-- The RIGHT leg `proj₁ : Σ B (Echo f) → B` is the canonical first-
-- projection. The composite `proj₁ ∘ encode f ≡ f` is definitional.
--
-- This is one half of the standard HoTT (equivalence, projection)
-- factorisation system on types: every function factors as an
-- equivalence onto the total space of its fibres, followed by the
-- projection out of that total space. The image factorisation
-- (the (epi, mono) factorisation on Set) arises as its
-- propositional-truncation collapse.
--
-- The repo's contribution here is NOT to introduce new categorical
-- machinery — it is to name the canonical loss-residue of the
-- factorisation by its existing name: Echo. The slogan:
--
--   *Echo is the canonical residue in the (equivalence, projection)
--    factorisation of any irreversible computation.*
--
-- Three load-bearing pieces land in this module:
--
--   1. `echo-factorisation` — the triangle commutes: `f ≡ proj₁ ∘
--      encode f` pointwise, definitionally.
--   2. `left-leg-equivalence` — the left leg IS an equivalence,
--      packaged from `EchoTotalCompletion.A↔ΣEcho`.
--   3. `projection-fibre-iso` — the fibre of the right-leg
--      projection at `y : B` is exactly `Echo f y`. Combined with
--      `EchoFiberBridge.echo↔fib` (Echo IS the fibre of `f`), this
--      identifies the residue at each visible output with the
--      semantic fibre of `f` at that output — uniformly.
--
-- Together (1) + (2) + (3) exhibit the canonical factorisation:
-- the left leg is an equivalence, the right leg is a projection,
-- the composite equals `f`, AND the right-leg's fibres realise the
-- echo at each visible output. That is the working content of the
-- factorisation system as far as `--safe --without-K` reaches
-- without funext.
--
-- Scope guardrail (honest narrowing — read before any prose claim
-- about this module).
--
-- A full orthogonal factorisation system requires, in addition to
-- factorisation existence:
--
--   * unique factorisation up to isomorphism (any other
--     (equivalence, projection) factorisation of `f` is
--     equivalent to this one);
--   * the diagonal-lifting property (every commuting square with
--     left side an equivalence and right side a projection admits
--     a unique diagonal filler).
--
-- Both of those properties need funext to state — and in some cases
-- non-trivial path algebra to prove — so they live in the
-- earn-back-gate style of `EchoPullbackUnivF4` (Pillar F4, the
-- funext-qualified strict universal property): a `funext` parameter
-- is taken as an explicit hypothesis, never as a postulate. This
-- module's headlines stand on their own without funext.
--
-- The earn-back gate for full OFS uniqueness/lifting is documented
-- in the companion remark at the end of this file.
--
-- Headlines (pinned in Smoke.agda):
--
--   * echo-factorisation               -- f x ≡ proj₁ (encode f x)
--   * left-leg-equivalence             -- A ↔ Σ B (Echo f)
--   * fibre-of-proj₁-to                -- forward map
--   * fibre-of-proj₁-from              -- backward map
--   * fibre-of-proj₁-to-from           -- round-trip
--   * fibre-of-proj₁-from-to           -- round-trip
--   * fibre-of-proj₁-iso               -- the iso, packaged
--   * projection-fibre-iso             -- specialised to Echo f
--   * ofs-witness                      -- the four-tuple packaging
--                                         the factorisation system
--                                         witness at this honesty level

module EchoOrthogonalFactorizationSystem where

open import Echo                 using (Echo)
open import EchoTotalCompletion  using (encode; decode; A↔ΣEcho;
                                        f-factors-via-projection;
                                        encode-is-section-of-proj₁)
open import EchoFiberBridge      using (fiber; echo↔fib)

open import Level                using (Level; _⊔_)
open import Data.Product.Base    using (Σ; _,_; proj₁; proj₂; _×_)
open import Function.Base        using (id; _∘_)
open import Function.Bundles     using (_↔_; mk↔ₛ′)
open import Relation.Binary.PropositionalEquality
                                 using (_≡_; refl)

private variable
  a b : Level
  A : Set a
  B : Set b

----------------------------------------------------------------------
-- (1) The factorisation triangle.
--
-- The right composite `proj₁ ∘ encode f` equals `f` pointwise,
-- definitionally. Re-stated here from `EchoTotalCompletion` so the
-- OFS module pins it under its own name.
----------------------------------------------------------------------

echo-factorisation :
  (f : A → B) (x : A) → f x ≡ proj₁ (encode f x)
echo-factorisation = f-factors-via-projection

----------------------------------------------------------------------
-- (2) The left leg is an equivalence.
--
-- Re-export of `A↔ΣEcho` under the OFS name. This is the
-- totality-completion equivalence, treated here as "the LEFT class
-- of the factorisation system contains `encode f`".
----------------------------------------------------------------------

left-leg-equivalence :
  (f : A → B) → A ↔ Σ B (Echo f)
left-leg-equivalence = A↔ΣEcho

----------------------------------------------------------------------
-- (3) The fibre of the right-leg projection at `y` is the residue
--     at `y`.
--
-- This is the generic Σ-fact "the fibre of `proj₁ : Σ B P → B` at
-- `y` is canonically `P y`", proved with one path elimination on
-- the equation `proj₁ z ≡ y`. Both round-trips are `refl` after
-- the elimination.
--
-- Stated first for arbitrary `P : B → Set` so the construction is
-- reusable, then specialised to `P := Echo f`.
----------------------------------------------------------------------

-- The helpers below are stated in the unfolded Σ-form
-- `Σ (Σ B P) (λ z → proj₁ z ≡ y)` rather than `fiber proj₁ y`
-- because Agda's first-class `proj₁` carries implicit name `B` for
-- its second argument and that name clashes with the locally-bound
-- `B`. The unfolded form is the same set (`fiber proj₁ y` reduces
-- to exactly this Σ); only the surface notation differs.

-- Forward: a fibre element `((b , p) , q)` of `proj₁` at `y` (with
-- `q : b ≡ y`) becomes a `P y` by transporting `p : P b` along `q`.
-- Pattern-matching on `q = refl` unifies `b := y`, so `p : P y`
-- directly.
fibre-of-proj₁-to :
  ∀ {p} {B : Set b} (P : B → Set p) (y : B) →
  Σ (Σ B P) (λ z → proj₁ z ≡ y) → P y
fibre-of-proj₁-to P y ((_ , p) , refl) = p

-- Backward: a `P y` becomes a fibre element by pairing with `y`
-- itself and the reflexive equation.
fibre-of-proj₁-from :
  ∀ {p} {B : Set b} (P : B → Set p) (y : B) →
  P y → Σ (Σ B P) (λ z → proj₁ z ≡ y)
fibre-of-proj₁-from P y p = (y , p) , refl

-- Round-trip on `P y`: `to ∘ from ≡ id`, definitional.
fibre-of-proj₁-to-from :
  ∀ {p} {B : Set b} (P : B → Set p) (y : B) (q : P y) →
  fibre-of-proj₁-to P y (fibre-of-proj₁-from P y q) ≡ q
fibre-of-proj₁-to-from _ _ _ = refl

-- Round-trip on the fibre: `from ∘ to ≡ id`. One path elimination
-- on the fibre equation collapses the pair to `refl` form, and the
-- result is definitional.
fibre-of-proj₁-from-to :
  ∀ {p} {B : Set b} (P : B → Set p) (y : B)
  (z : Σ (Σ B P) (λ z → proj₁ z ≡ y)) →
  fibre-of-proj₁-from P y (fibre-of-proj₁-to P y z) ≡ z
fibre-of-proj₁-from-to _ _ ((_ , _) , refl) = refl

-- The packaged iso.
fibre-of-proj₁-iso :
  ∀ {p} {B : Set b} (P : B → Set p) (y : B) →
  Σ (Σ B P) (λ z → proj₁ z ≡ y) ↔ P y
fibre-of-proj₁-iso P y =
  mk↔ₛ′
    (fibre-of-proj₁-to   P y)
    (fibre-of-proj₁-from P y)
    (fibre-of-proj₁-to-from P y)
    (fibre-of-proj₁-from-to P y)

----------------------------------------------------------------------
-- Specialisation: at the right-leg projection of `f`, the fibre is
-- `Echo f y`. Combined with `echo↔fib`, this identifies the residue
-- at each visible output with the semantic fibre of `f` itself —
-- the load-bearing identification of the OFS framing.
----------------------------------------------------------------------

projection-fibre-iso :
  (f : A → B) (y : B) →
  Σ (Σ B (Echo f)) (λ z → proj₁ z ≡ y) ↔ Echo f y
projection-fibre-iso f y = fibre-of-proj₁-iso (Echo f) y

----------------------------------------------------------------------
-- The OFS witness, packaged.
--
-- A four-tuple naming the four facts that together witness the
-- (equivalence, projection) factorisation through Echo at the
-- honesty level this module reaches:
--
--   1. the factorisation triangle commutes;
--   2. the left leg is an equivalence;
--   3. the right leg's fibre at `y` is `Echo f y` (residue
--      identification);
--   4. the right leg's fibre at `y` is also `fiber f y` (via
--      `EchoFiberBridge.echo↔fib`, the bridge through Echo).
--
-- The four are pinned as a tuple so a downstream consumer can cite
-- the OFS witness in one place. The two fibre identifications
-- (3) + (4) together say: the residue at each visible output is
-- exactly the semantic fibre of `f`. That is the precise content
-- of "Echo is the canonical residue".
----------------------------------------------------------------------

ofs-witness :
  (f : A → B) →
  ((x : A) → f x ≡ proj₁ (encode f x))                                          -- (1)
  × (A ↔ Σ B (Echo f))                                                          -- (2)
  × ((y : B) → Σ (Σ B (Echo f)) (λ z → proj₁ z ≡ y) ↔ Echo f y)                 -- (3)
  × ((y : B) → Echo f y ↔ fiber f y)                                            -- (4)
ofs-witness f =
    echo-factorisation f
  , left-leg-equivalence f
  , projection-fibre-iso f
  , echo↔fib f

----------------------------------------------------------------------
-- Companion remark on what is NOT claimed.
--
-- The four headlines above are *factorisation existence + fibre
-- identification*. A full orthogonal factorisation system also
-- requires:
--
--   * UNIQUENESS UP TO ISOMORPHISM: any other (equivalence,
--     projection) factorisation `f = m' ∘ e'` with `e' : A → X`
--     an equivalence and `m' : X → B` a projection (in a suitable
--     sense) is canonically isomorphic to the Echo factorisation.
--
--   * DIAGONAL LIFTING: every commuting square with left side an
--     equivalence and right side a projection admits a unique
--     diagonal filler.
--
-- Both of those statements need funext to formulate (uniqueness up
-- to isomorphism is a statement about FUNCTIONS being equal, and
-- the diagonal lifter's uniqueness is similar). Under `--safe
-- --without-K` without funext, the cleanest available form is the
-- factorisation-existence + fibre-identification level proved here.
--
-- The earn-back template for the full OFS (in the style of
-- `EchoPullbackUnivF4`, the Pillar F4 funext-qualified universal
-- property): take `funext` as an explicit hypothesis parameter,
-- never as a postulate; prove uniqueness up to isomorphism
-- conditional on `funext`; pin the unconditional fibre-level
-- corollaries as the funext-free part.
--
-- This narrowing is consistent with the R-2026-05-18 retraction
-- discipline: state the unconditional form (this module),
-- explicitly flag what additional hypotheses the full categorical
-- form would need, and leave the funext-qualified earn-back as a
-- documented future gate. The unconditional content above is the
-- load-bearing artefact; the full OFS is the next earn-back.
----------------------------------------------------------------------
