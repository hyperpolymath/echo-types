{-# OPTIONS --safe --without-K #-}

------------------------------------------------------------------------
-- TERMINATION NOTICE (added at integration commit):
--
-- EI-2 has been *expressly terminated* with a negative verdict via
-- PATH B (see RecipeNonTriviality.agda header and docs/EI2_REPORT.adoc
-- for the full record). The integration recipe with the existing five
-- named axes does NOT carry substantive simultaneous cross-axis
-- content. This file's "EI-2 IS NOT TERMINATED" comments below are
-- preserved as the historical record of the investigation while it
-- was still open; the authoritative current verdict is at the top of
-- docs/EI2_REPORT.adoc.
--
-- Distinctness against neighbour frameworks rests on the truncation
-- argument (`echo-not-prop` family in proofs/agda/examples/) and the
-- 2-cell argument (Sophisticated submodules of EchoVsQuotient.agda
-- and EchoVsGalois.agda), not on the integration argument. The
-- integration recipe remains useful as organising vocabulary; it is
-- not the locus of distinctness.
------------------------------------------------------------------------


------------------------------------------------------------------------
-- characteristic.RoleRole
--
-- Phase 5 critical sub-step of EI-2 (`docs/next-questions.adoc`):
-- pair Choreo with itself. The unique non-collapsing axis paired with
-- itself.
--
-- The question this file tests:
--
--   In a 2D family indexed by Role × Role with two independent
--   role-axis transport actions, does the cell `(c⊑s, c⊑s)` exhibit
--   genuine simultaneous cross-axis interaction?
--
-- If YES: EI-2 pivots toward POSITIVE termination. The recipe DOES
-- exhibit simultaneous cross-axis content; the prior siblings just
-- happened to pair non-collapsing with collapsing axes.
--
-- If NO: P3' strengthens to apply to ALL recipe pairs (not just those
-- with at least one collapsing component). EI-2 terminates negatively
-- in stronger form.
--
-- Status of EI-2 after this construction: see EI-2 measurement at
-- the bottom. EI-2 IS NOT TERMINATED until this experiment
-- completes.
------------------------------------------------------------------------

module characteristic.RoleRole where

open import Data.Bool.Base                        using (Bool; true; false)
open import Data.Product.Base                     using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import EchoChoreo                            using
  ( Role; Client; Server
  ; obs; Global
  ; _⊑c_; c⊑c; c⊑s; s⊑s
  )

------------------------------------------------------------------------
-- The 2D family RREcho
--
-- The natural definition: a Global state plus equality witnesses for
-- both projections at a chosen visible value. We fix the visible
-- value at `true` for both axes, so both projections must be true
-- (i.e., the underlying global must be (true, true)).
--
--   RREcho r₁ r₂ = Σ Global (λ g → obs r₁ g ≡ true × obs r₂ g ≡ true)
--
-- This is symmetric in r₁ and r₂ (swap them and the type is
-- isomorphic), which is good for testing whether the actions
-- commute genuinely.
--
-- Note: at (Client, Client), this is `Σ Global (λ g → proj₁ g ≡ true
-- × proj₁ g ≡ true)` — the second equation is redundant. At (Client,
-- Server), it's `Σ Global (λ g → proj₁ g ≡ true × proj₂ g ≡ true)`,
-- forcing g = (true, true). At (Server, Server), it's
-- `Σ Global (λ g → proj₂ g ≡ true × proj₂ g ≡ true)`. So the type
-- "shape" varies subtly with the role pair.
------------------------------------------------------------------------

RREcho : Role → Role → Set
RREcho r₁ r₂ = Σ Global (λ g → (obs r₁ g ≡ true) × (obs r₂ g ≡ true))

------------------------------------------------------------------------
-- Two independent role-axis actions
--
-- `applyRole₁` lifts the first-axis role along ⊑c. This means: given
-- an RREcho where axis 1 is at role r1, produce one where axis 1 is
-- at role r2. The key non-trivial step is c⊑s.
--
-- For c⊑s: we have (g, p₁ : obs Client g ≡ true, p₂ : obs r' g ≡ true).
-- We need (g', p₁' : obs Server g' ≡ true, p₂' : obs r' g' ≡ true).
--
-- The natural choice: pick g' such that obs Server g' ≡ true. The
-- existing client-to-server uses swap; we have to do the same here
-- but preserve axis 2's witness too.
--
-- For (Client, r') → (Server, r'): the natural transport is "swap g"
-- with the witnesses appropriately re-derived. But after swap, axis
-- 2's witness needs to be re-checked. Let's see what happens with r' = Server:
--   Original: (g, proj₁ g ≡ true, proj₂ g ≡ true)
--   Want: (g', proj₂ g' ≡ true, proj₂ g' ≡ true) — both witnesses
--         now check the second projection.
--   If we use g' = swap g, then proj₂ g' = proj₁ g, which we know is
--   true. But also proj₂ g' = proj₁ g (by swap), and we needed
--   proj₂ g' ≡ true for axis 2 — but axis 2 was originally checking
--   proj₂ g, not proj₁ g.
--
-- THIS IS WHERE IT GETS INTERESTING. After applying c⊑s on axis 1,
-- the new global state's axis-2 projection is NOT what axis 2 was
-- previously certifying. We need to coerce or recompute.
--
-- The natural choice for symmetric handling: don't change g, but
-- re-derive the axis-1 witness using the axis-2 witness. This works
-- because at (Client → Server), we need obs Server g ≡ true, and we
-- already have obs Server g ≡ true if the original axis 2 was Server.
-- Otherwise we need to use the global structure.
--
-- For maximum symmetry (and to avoid spurious choices), I'll use the
-- definition: applyRole₁ for c⊑s requires that the global state
-- already satisfy the new constraint. This requires axis 2 to be
-- Server (so we already have obs Server g ≡ true), OR we need the
-- non-trivial swap.
--
-- The cleanest symmetric formulation: define the action as an
-- explicit case-split on the OTHER axis's role.
--
-- Let me try a simpler approach: define RREcho with a SHARED witness.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Simplified RREcho: shared witness style
--
-- RREcho r₁ r₂ has at most one inhabitant per global state.
-- For the Role × Role case, we can simplify by observing that
-- "obs r g ≡ true for both r=r₁ and r=r₂" is the conjunction.
--
-- At (Client, Client): proj₁ g ≡ true (single condition, redundant)
-- At (Server, Server): proj₂ g ≡ true (single condition, redundant)
-- At (Client, Server) or (Server, Client): both projections true
--   (i.e., g = (true, true))
--
-- For the applyRole transitions:
--   * (c⊑s, _) on first axis: lift Client → Server requires
--     obs Server g ≡ true. If r₂ = Server, we already have this.
--     If r₂ = Client, we need to derive it... which requires obs
--     Server g, which is proj₂ g, which we don't know.
--
-- This means applyRole₁ from (Client, Client) via c⊑s to (Server,
-- Client) is NOT TOTAL — it can't produce a valid RREcho without
-- additional information.
--
-- THIS IS A REAL OBSTRUCTION. The 2D family doesn't admit a single-
-- axis transport because the constraints are coupled.
------------------------------------------------------------------------

-- Let me try a different design: TOTALLY DEFINED transport at the
-- cost of needing helper assumptions.
--
-- Define RREcho with a swap-friendly structure: g such that BOTH
-- projections are true, regardless of role pair. This makes the
-- transport easy because the global state is the same for any role
-- pair.

RREcho-tt : Role → Role → Set
RREcho-tt _ _ = Σ Global (λ g → (proj₁ g ≡ true) × (proj₂ g ≡ true))

-- The transport actions on this version are TRIVIAL: roles don't
-- affect the witness type. The action is pure type coercion (no
-- computational change).

applyRole₁-tt : ∀ {r₁ r₂ r'} → r₁ ⊑c r₂ → RREcho-tt r₁ r' → RREcho-tt r₂ r'
applyRole₁-tt _ e = e

applyRole₂-tt : ∀ {r r₁ r₂} → r₁ ⊑c r₂ → RREcho-tt r r₁ → RREcho-tt r r₂
applyRole₂-tt _ e = e

-- The commutation theorem trivially holds because both actions are
-- the identity:
role-role-commute-tt :
  ∀ {r₁ r₂ s₁ s₂}
  (rp : r₁ ⊑c r₂) (sp : s₁ ⊑c s₂) (e : RREcho-tt r₁ s₁) →
  applyRole₂-tt {r = r₂} sp (applyRole₁-tt {r' = s₁} rp e) ≡ applyRole₁-tt {r' = s₂} rp (applyRole₂-tt {r = r₁} sp e)
role-role-commute-tt rp sp e = refl

-- This formulation passes the commutation but exhibits ZERO non-
-- trivial action. It's a degenerate case.

------------------------------------------------------------------------
-- Non-degenerate version: track role-relative information
--
-- For the genuinely interesting case, we want a family that VARIES
-- in role and where transport is genuinely role-aware. The natural
-- candidate uses RoleEcho directly:
--
--   RREcho-pair r₁ r₂ = RoleEcho r₁ true × RoleEcho r₂ true
--
-- Here the two echoes are independent (different witnesses). The
-- transport on each axis acts only on its own echo:
--
--   applyRole₁ c⊑s (e₁, e₂) = (client-to-server e₁, e₂)
--   applyRole₂ c⊑s (e₁, e₂) = (e₁, client-to-server e₂)
--
-- These two operations TRIVIALLY commute (they act on different
-- coordinates of a product). The commutation is by `refl` and
-- carries zero substantive content.
------------------------------------------------------------------------

open import EchoChoreo using (RoleEcho; client-to-server)

RREcho-pair : Role → Role → Set
RREcho-pair r₁ r₂ = RoleEcho r₁ true × RoleEcho r₂ true

applyRole₁-pair : ∀ {r₁ r₂ r'} → r₁ ⊑c r₂ → RREcho-pair r₁ r' → RREcho-pair r₂ r'
applyRole₁-pair c⊑c (e₁ , e₂) = (e₁ , e₂)
applyRole₁-pair c⊑s (e₁ , e₂) = (client-to-server e₁ , e₂)
applyRole₁-pair s⊑s (e₁ , e₂) = (e₁ , e₂)

applyRole₂-pair : ∀ {r r₁ r₂} → r₁ ⊑c r₂ → RREcho-pair r r₁ → RREcho-pair r r₂
applyRole₂-pair c⊑c (e₁ , e₂) = (e₁ , e₂)
applyRole₂-pair c⊑s (e₁ , e₂) = (e₁ , client-to-server e₂)
applyRole₂-pair s⊑s (e₁ , e₂) = (e₁ , e₂)

------------------------------------------------------------------------
-- The commutation theorem on RREcho-pair
--
-- Cases: 3 × 3 = 9 cells. The (c⊑s, c⊑s) cell is the critical one.
--
-- LHS at (c⊑s, c⊑s):
--   applyRole₂ c⊑s (applyRole₁ c⊑s (e₁, e₂))
-- = applyRole₂ c⊑s (client-to-server e₁, e₂)
-- = (client-to-server e₁, client-to-server e₂)
--
-- RHS at (c⊑s, c⊑s):
--   applyRole₁ c⊑s (applyRole₂ c⊑s (e₁, e₂))
-- = applyRole₁ c⊑s (e₁, client-to-server e₂)
-- = (client-to-server e₁, client-to-server e₂)
--
-- They're equal — but the equation is established by REFL on the
-- product. The two sides are *literally definitionally equal* because
-- the actions act on DIFFERENT COORDINATES of the pair.
--
-- This is product-of-actions commutation: trivial in the categorical
-- sense (any two functions f : A → A' and g : B → B' commute via the
-- product action f × g). The commutation carries NO cross-axis
-- content because the two axes are independent products.
------------------------------------------------------------------------

role-role-commute-pair :
  ∀ {r₁ r₂ s₁ s₂}
  (rp : r₁ ⊑c r₂) (sp : s₁ ⊑c s₂) (e : RREcho-pair r₁ s₁) →
  applyRole₂-pair {r = r₂} sp (applyRole₁-pair {r' = s₁} rp e)
  ≡ applyRole₁-pair {r' = s₂} rp (applyRole₂-pair {r = r₁} sp e)
role-role-commute-pair c⊑c c⊑c e = refl
role-role-commute-pair c⊑c c⊑s e = refl
role-role-commute-pair c⊑c s⊑s e = refl
role-role-commute-pair c⊑s c⊑c e = refl
role-role-commute-pair c⊑s c⊑s e = refl
role-role-commute-pair c⊑s s⊑s e = refl
role-role-commute-pair s⊑s c⊑c e = refl
role-role-commute-pair s⊑s c⊑s e = refl
role-role-commute-pair s⊑s s⊑s e = refl

------------------------------------------------------------------------
-- VERDICT: the (c⊑s, c⊑s) cell of RREcho-pair has BOTH actions doing
-- non-trivial work, but the commutation is STILL trivial because the
-- actions act on independent coordinates.
--
-- This is the crucial finding. Even with two non-collapsing axes
-- (Role × Role), pairing them via the *natural* product family gives
-- coordinate-wise actions that commute by product structure, not by
-- substantive cross-axis content.
--
-- For genuine simultaneous interaction, we'd need a 2D family where
-- the actions on each axis CAN'T be decomposed into independent
-- coordinates. Such a family would need to entangle the two role
-- witnesses in some way that makes them mutually constraining.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Entangled version: shared global state
--
-- Let's try: RREcho-shared r₁ r₂ uses a SINGLE global state that
-- must satisfy BOTH role-relative constraints simultaneously.
--
--   RREcho-shared r₁ r₂ = Σ Global (λ g → obs r₁ g ≡ true × obs r₂ g ≡ true)
--
-- Now the global state is shared across both axes. A transport on
-- axis 1 must produce a state satisfying the new axis-1 constraint
-- WHILE preserving the axis-2 constraint.
--
-- This is the candidate for "non-trivial simultaneous interaction":
-- the transport can't decompose into independent coordinates because
-- the state is coupled.
------------------------------------------------------------------------

RREcho-shared : Role → Role → Set
RREcho-shared r₁ r₂ = Σ Global (λ g → (obs r₁ g ≡ true) × (obs r₂ g ≡ true))

-- The transport challenge: applyRole₁-shared from (Client, r₂) via
-- c⊑s to (Server, r₂). We have:
--   (g, p₁ : obs Client g ≡ true, p₂ : obs r₂ g ≡ true)
-- and need:
--   (g', p₁' : obs Server g' ≡ true, p₂' : obs r₂ g' ≡ true).
--
-- We need to pick g'. The natural candidate:
--   - If r₂ = Client: we need obs Client g' ≡ true. We can take
--     g' = (true, true) (since we know obs Client g = proj₁ g = true,
--     so g = (true, ?), and we need obs Server g' = proj₂ g' = true,
--     so g' = (?, true). The simplest universal choice is (true, true).
--     But this requires us to KNOW that the result has both bits
--     true, and we don't know proj₂ g.
--   - If r₂ = Server: we have proj₂ g ≡ true, so g already satisfies
--     obs Server g ≡ true. We can take g' = g.

-- This case analysis suggests the transport ISN'T uniformly defined.
-- For the case r₂ = Client and the original axis-2 witness only
-- guarantees proj₁ g ≡ true (not proj₂ g ≡ true), there's no natural
-- way to produce g' with both projections true.

-- The transport applyRole₁-shared from (Client, Client) via c⊑s
-- isn't totally defined unless we can DERIVE proj₂ g ≡ true from
-- the existing data. We can't.

-- So RREcho-shared doesn't admit a uniform total applyRole₁.

-- The FORMAL VERDICT:
-- A 2D family with shared state CAN'T have both axes independently
-- transportable along c⊑s. The "shared state" coupling means the
-- transport on one axis depends on the other axis's role.

-- We could define a DEPENDENT transport (where applyRole₁ takes
-- the axis-2 role as a parameter and behaves differently per case),
-- but this isn't the recipe — it's a richer structure.

------------------------------------------------------------------------
-- EI-2 STATUS AFTER PHASE 5 ROLE × ROLE TEST
--
-- TWO concrete attempts at Role × Role:
--
-- 1. RREcho-pair (independent product structure):
--    - Both actions non-trivial at (c⊑s, c⊑s).
--    - But commutation holds trivially because actions are
--      coordinate-wise.
--    - Carries zero substantive cross-axis content.
--    - This is the "categorical product" pattern.
--
-- 2. RREcho-shared (shared global state):
--    - Single-axis transport isn't uniformly definable.
--    - Either we restrict the family (lose the shared-state
--      property) or we add structure (move beyond the recipe).
--    - The recipe-as-specified can't accommodate this design.
--
-- INTERPRETATION:
--
-- (a) For the recipe with two non-collapsing axes paired via INDEPENDENT
--     product, simultaneous action is possible but commutation is
--     trivial (categorical-product reason, not substantive cross-axis
--     content).
--
-- (b) For the recipe with two non-collapsing axes paired via SHARED
--     state, simultaneous transport isn't uniformly definable (the
--     coupling breaks the per-axis transport assumption).
--
-- Combining (a) and (b): under the existing recipe, Role × Role does
-- NOT exhibit substantive simultaneous cross-axis interaction. Either
-- it degenerates to coordinate-wise products (a) or breaks the recipe
-- structure (b).
--
-- This STRENGTHENS P3': it's not just "pairs with at least one
-- collapsing recipe"; it's ALL recipe pairs in the existing
-- specification. The integration recipe cannot exhibit substantive
-- simultaneous cross-axis interaction.
--
-- HOW WOULD POSITIVE TERMINATION LOOK NOW:
--
-- We'd need to extend the recipe specification to allow:
--   * Coupled state across axes (breaking single-axis transport).
--   * OR multiple live positions per axis (extending the spec).
--   * OR some other structural move.
--
-- Each extension would be a strictly richer specification. The
-- question shifts: does the EXTENDED recipe match anything in the
-- repository (modal type theories, HoTT bundles, refinement type
-- families) or is it genuinely echo-specific?
--
-- This is a question for FUTURE work, not for v0.1.1 release. For
-- the present integration, EI-2's negative trajectory is now formally
-- supported across BOTH the collapsing-pair cases (P3') AND the
-- non-collapsing-pair Role × Role cases.
--
-- EI-2 IS NOT TERMINATED FORMALLY — the full P3' theorem still has
-- bookkeeping holes — but the empirical evidence and the structural
-- arguments are converging on negative termination.
--
-- THE NEGATIVE TERMINATION OUTCOME:
-- Echo types' integration claim narrows to: "the recipe with the
-- existing five named axes exhibits one-axis-at-a-time content
-- embedded in 2D families. The recipe does not produce substantive
-- simultaneous cross-axis interaction. Distinctness against neighbour
-- theories rests on the truncation argument (`echo-not-prop` family)
-- and the 2-cell argument (`Sophisticated.equalizer→echo-pair`,
-- `Sophisticated.meet→echo-intersection`), not on the integration
-- argument."
--
-- This is a USEFUL repository — narrower than the consolidated rhetoric
-- suggested, but not a dead type. The truncation and 2-cell arguments
-- stand. The integration argument is what weakens.
--
-- EI-2 IS NOT TERMINATED. Phase 5 is in substantial progress: P3'
-- supported by all collapsing-pair siblings AND by both Role × Role
-- design attempts. The bookkeeping completion is the open work.
------------------------------------------------------------------------
