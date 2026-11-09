{-# OPTIONS --safe --without-K --cubical-compatible --exact-split --no-sized-types --no-guardedness #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

-- EchoPartialSection: partial sections of a modality bundle, their
-- information order, resolve-parametric merge, guarded fill, and the
-- restriction fibre. The Agda source of truth for the recovery
-- invariants of hyperpolymath/squeakwell (docs/ROUTE-PLAN.adoc rungs
-- R3, R9, R12), rechecked in Rocq as verisimdb `formal/Recovery.v`.
--
-- The object. A VeriSimDB octad is a partial section of a bundle
-- `V : M → Set` over a finite index set `M` of modalities: each
-- modality carries a value or bot. Here that is
-- `PartialSection M V = (m : M) → Maybe (V m)`, with no assumption on
-- `M` (so the eight-slot octad is one instance). This is the
-- "join-semilattice of partial sections" abstraction that
-- verisimdb/formal/CROSS-REPO-MAP.adoc flagged as the missing
-- echo-types companion to Octad.v's R1–R3.
--
-- Everything is stated POINTWISE (equalities at each `m`), never as an
-- equality of functions, so the module is funext-free. Octad.v proves
-- the same laws as function equalities using Coq's
-- functional_extensionality; the pointwise forms here are the ones
-- that survive `--safe --without-K` without that axiom.
--
-- What is proved:
--
--   * Information order `_⊑_` (present-in-s ⇒ present-and-equal-in-t):
--     reflexive, transitive.
--   * `merge resolve` — the per-point merge kernel of Octad.v
--     (`mcombine`), parametric in the conflict resolver — inherits
--     exactly the algebra of `resolve`: commutative / associative /
--     idempotent WHEN `resolve` is (`merge-comm`, `merge-assoc`,
--     `merge-idem`). These are the R1–R3 twins; they are implications,
--     not unconditional CRDT laws.
--   * Guarded fill is the LEFT-BIASED merge against an oracle's
--     proposal (`fill`): it never overwrites a present value
--     (`fill-guarded`), is inflationary on `_⊑_` (`fill-inflationary`),
--     and is NOT monotone on `_⊑_` (`fill-not-monotone`, a two-modality
--     counter-model). Rung R3.
--   * Restriction to an observed mask `T` and its Echo fibre: an echo
--     of `restrict T` at an observation agrees with the observation on
--     every observed modality (`restrict-fibre-agree`) and is blind off
--     the mask (`restrict-blind`). This is the fragment-granularity
--     observation-fidelity shape of rung R12: `e : Echo (restrict T) obs`
--     says exactly "the candidate reproduces what was observed, on T".
--
-- Headlines (pinned in Smoke.agda):
--
--   * ⊑-refl, ⊑-trans
--   * merge-comm, merge-assoc, merge-idem
--   * fill-guarded, fill-inflationary, fill-not-monotone
--   * restrict-fibre-agree, restrict-blind, restrict-echo

module EchoPartialSection where

open import Level                                 using (Level; _⊔_)
open import Data.Bool.Base                        using (Bool; true; false; if_then_else_)
open import Data.Maybe.Base                       using (Maybe; just; nothing)
open import Data.Product.Base                     using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Empty                            using (⊥)
open import Relation.Nullary                      using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import Echo                                  using (Echo; echo-intro)

private
  variable
    ℓm ℓv : Level

----------------------------------------------------------------------
-- Partial sections.
----------------------------------------------------------------------

-- A partial section of the bundle `V` over `M`: a value or bot at each
-- index. An octad is the instance `M = the eight modalities`.
PartialSection : (M : Set ℓm) (V : M → Set ℓv) → Set (ℓm ⊔ ℓv)
PartialSection M V = (m : M) → Maybe (V m)

module _ {M : Set ℓm} {V : M → Set ℓv} where

  ----------------------------------------------------------------------
  -- Information order.
  ----------------------------------------------------------------------

  -- `s ⊑ t`: every value present in `s` is present, unchanged, in `t`.
  _⊑_ : PartialSection M V → PartialSection M V → Set (ℓm ⊔ ℓv)
  s ⊑ t = ∀ m (v : V m) → s m ≡ just v → t m ≡ just v

  ⊑-refl : ∀ {s} → s ⊑ s
  ⊑-refl m v p = p

  ⊑-trans : ∀ {s t u} → s ⊑ t → t ⊑ u → s ⊑ u
  ⊑-trans p q m v h = q m v (p m v h)

  ----------------------------------------------------------------------
  -- Resolve-parametric merge (Octad.v `mcombine` / `merge`).
  ----------------------------------------------------------------------

  Resolver : Set (ℓm ⊔ ℓv)
  Resolver = ∀ {m} → V m → V m → V m

  mcombine : Resolver → ∀ {m} → Maybe (V m) → Maybe (V m) → Maybe (V m)
  mcombine resolve nothing  nothing  = nothing
  mcombine resolve (just a) nothing  = just a
  mcombine resolve nothing  (just b) = just b
  mcombine resolve (just a) (just b) = just (resolve a b)

  merge : Resolver → PartialSection M V → PartialSection M V → PartialSection M V
  merge resolve s t m = mcombine resolve (s m) (t m)

  -- R1 twin: merge is commutative when resolve is.
  merge-comm :
    (resolve : Resolver) →
    (∀ {m} (a b : V m) → resolve a b ≡ resolve b a) →
    ∀ s t m → merge resolve s t m ≡ merge resolve t s m
  merge-comm resolve rc s t m with s m | t m
  ... | nothing | nothing = refl
  ... | just a  | nothing = refl
  ... | nothing | just b  = refl
  ... | just a  | just b  = cong just (rc a b)

  -- R2 twin: merge is associative when resolve is.
  merge-assoc :
    (resolve : Resolver) →
    (∀ {m} (a b c : V m) → resolve a (resolve b c) ≡ resolve (resolve a b) c) →
    ∀ s t u m →
    merge resolve (merge resolve s t) u m ≡ merge resolve s (merge resolve t u) m
  merge-assoc resolve ra s t u m with s m | t m | u m
  ... | nothing | nothing | nothing = refl
  ... | nothing | nothing | just c  = refl
  ... | nothing | just b  | nothing = refl
  ... | nothing | just b  | just c  = refl
  ... | just a  | nothing | nothing = refl
  ... | just a  | nothing | just c  = refl
  ... | just a  | just b  | nothing = refl
  ... | just a  | just b  | just c  = cong just (sym (ra a b c))

  -- R3 twin: merge is idempotent when resolve is.
  merge-idem :
    (resolve : Resolver) →
    (∀ {m} (a : V m) → resolve a a ≡ a) →
    ∀ s m → merge resolve s s m ≡ s m
  merge-idem resolve ri s m with s m
  ... | nothing = refl
  ... | just a  = cong just (ri a)

  ----------------------------------------------------------------------
  -- Guarded fill: left-biased merge against an oracle's proposal.
  ----------------------------------------------------------------------

  keep-left : Resolver
  keep-left a _ = a

  -- The oracle proposes a (partial) section from the current one; fill
  -- takes a proposal only where the current section is bot.
  fill : (propose : PartialSection M V → PartialSection M V) →
         PartialSection M V → PartialSection M V
  fill propose s = merge keep-left s (propose s)

  -- A present value is never overwritten.
  fill-guarded :
    ∀ propose s m (v : V m) → s m ≡ just v → fill propose s m ≡ just v
  fill-guarded propose s m v p with s m | propose s m
  fill-guarded propose s m v refl | just .v | nothing = refl
  fill-guarded propose s m v refl | just .v | just _  = refl

  -- Guarded fill is inflationary on the information order.
  fill-inflationary : ∀ propose s → s ⊑ fill propose s
  fill-inflationary propose s m v p = fill-guarded propose s m v p

  ----------------------------------------------------------------------
  -- Restriction to an observed mask, and its Echo fibre.
  ----------------------------------------------------------------------

  -- Keep the observed modalities, forget the rest (Octad.v `project`).
  restrict : (T : M → Bool) → PartialSection M V → PartialSection M V
  restrict T s m = if T m then s m else nothing

  -- Every section is a candidate for its own restriction.
  restrict-echo : (T : M → Bool) (s : PartialSection M V) →
                  Echo (restrict T) (restrict T s)
  restrict-echo T s = echo-intro (restrict T) s

  restrict-on : (T : M → Bool) (s : PartialSection M V) (m : M) →
                T m ≡ true → restrict T s m ≡ s m
  restrict-on T s m Tm rewrite Tm = refl

  -- R12 shape: a candidate in the fibre of `restrict T` at an observation
  -- `o` reproduces `o` on every observed modality.
  restrict-fibre-agree :
    (T : M → Bool) {o : PartialSection M V} (e : Echo (restrict T) o) →
    ∀ m → T m ≡ true → proj₁ e m ≡ o m
  restrict-fibre-agree T (s , p) m Tm =
    trans (sym (restrict-on T s m Tm)) (cong (λ f → f m) p)

  -- Off the mask, restriction forgets everything: any two sections
  -- restrict to the same (bot) value there.
  restrict-blind :
    (T : M → Bool) (s t : PartialSection M V) (m : M) →
    T m ≡ false → restrict T s m ≡ restrict T t m
  restrict-blind T s t m Tm rewrite Tm = refl

----------------------------------------------------------------------
-- Counter-model: guarded fill is NOT monotone on the information order.
--
-- Two modalities (`Bool`), Boolean values. The oracle proposes `true`
-- for modality `true` only while modality `false` is still bot. Then
-- the empty section ⊑ the section with modality `false` set, but their
-- fills are incomparable: the first gains a value at `true` that the
-- second never does.
----------------------------------------------------------------------

module FillNotMonotone where

  V₂ : Bool → Set
  V₂ _ = Bool

  is-bot : Maybe Bool → Bool
  is-bot nothing  = true
  is-bot (just _) = false

  propose₂ : PartialSection Bool V₂ → PartialSection Bool V₂
  propose₂ s true  = if is-bot (s false) then just true else nothing
  propose₂ s false = nothing

  empty₂ : PartialSection Bool V₂
  empty₂ _ = nothing

  one₂ : PartialSection Bool V₂
  one₂ false = just true
  one₂ true  = nothing

  empty⊑one : empty₂ ⊑ one₂
  empty⊑one m v ()

  -- Monotonicity would force `fill propose₂ one₂ true ≡ just true`, but
  -- it is `nothing`.
  fill-not-monotone : ¬ (_⊑_ {M = Bool} {V = V₂} (fill propose₂ empty₂) (fill propose₂ one₂))
  fill-not-monotone mono = absurd (mono true true refl)
    where
      absurd : fill propose₂ one₂ true ≡ just true → ⊥
      absurd ()

----------------------------------------------------------------------
-- Companion remark.
--
--   * `merge-*` are implications from properties of `resolve`. The only
--     kernel squeakwell can reach through verisim-api today (PUT
--     overwrite, `resolve a b = b`) is commutative only on a singleton
--     value type; Recovery.v states that negative half
--     (`put_commutative_iff_trivial`).
--   * The termination argument (lexicographic progress on
--     `(|missing|, nconflicts)`, nine-round bound) needs a FINITE index
--     set and a conflict test; it lives in Recovery.v over the concrete
--     eight-modality octad and is not restated here over an arbitrary
--     `M`.
--   * Audit modalities (provenance / temporal hash chains) move by chain
--     prefix, not by this fill; that is verisimdb/formal/Provenance.v.
----------------------------------------------------------------------
