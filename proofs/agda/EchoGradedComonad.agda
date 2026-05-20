{-# OPTIONS --safe --without-K #-}

-- RETRACTION 2026-05-18 (docs/retractions.adoc R-2026-05-18): comments
-- in this module that assert a "graded comonad", a "universal property
-- / terminal cone", "model-independence", or a "conservativity
-- metatheorem" are RETRACTED claims. The Agda is unchanged and correct;
-- read it as a loss-graded *reindexing modality* (thin-poset action;
-- no nested D_r D_s), a funext-relative *pointwise* mediator property,
-- and carrier-parametricity over a fixed grade poset. Authoritative
-- prose: docs/echo-types/paper.adoc §"Reframing note".

-- Pillar B (part 2) of docs/echo-types/establishment-plan.adoc.
--
-- REAL MODULE (thin slice landed 2026-05-17).
--
-- Goal: exhibit echo, indexed by the loss-grade lattice, as a
-- *graded comonad of structured loss* — the headline theorem family
-- that slots "echo" into the QTT / Granule (coeffect / quantitative)
-- lineage rather than leaving it a Σ-lemma cluster.
--
-- Structure (reusing `EchoGraded` wholesale):
--
--   * The loss grades `(Grade, _⊔g_, keep)` form a join-semilattice
--     with `keep` (zero loss) as bottom / monoidal unit. `GEcho` is
--     the grade-indexed object; `degrade` its functorial reindexing.
--
--   * Graded counit  `gextract`   : zero-loss echo IS the bare echo
--     (the Pillar-A definitional move, reused — `GEcho keep` *is*
--     `Echo collapse tt`).
--
--   * Graded comultiplication `gduplicate` : the join-left embedding
--     `GEcho g₁ → GEcho (g₁ ⊔g g₂)` — "duplicating" an observation
--     splits the loss budget along the lattice join.
--
-- THE LOAD-BEARING QUESTION (establishment-plan §"de-risk first"):
-- does graded *coassociativity* need path algebra beyond `≤g-prop`?
--
--   ANSWER: NO. Stated in the *common-upper-bound* idiom (the same
--   idiom the repo already uses for `EchoGraded.degrade-via-join`),
--   all three graded-comonad laws — counit-left, counit-right,
--   coassociativity — collapse to `degrade-compose` + `≤g-prop`
--   with ZERO transport. The naive grade-equality phrasing of
--   coassoc would force a `subst GEcho (⊔g-assoc …)`; the
--   common-bound phrasing eliminates it entirely, exactly because
--   the lattice join is a *universal* arrow and `_≤g_` is
--   propositional. This is a thesis-SUPPORTING result: the
--   graded-comonad standing rests cleanly on the two ingredients
--   the repo already owns, with no new path algebra. (Recorded in
--   establishment-plan.adoc per its revision policy.)

module EchoGradedComonad where

open import Echo using (Echo)
open import EchoCharacteristic using (collapse)
open import EchoGraded
  using ( Grade; keep; residue; forget
        ; _⊔g_
        ; _≤g_
        ; ≤g-trans
        ; GEcho
        ; degrade
        ; ≤g-prop
        ; ≤g-⊔g-left
        ; degrade-compose
        )
open import Data.Unit.Base using (⊤; tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; module ≡-Reasoning)

----------------------------------------------------------------------
-- Graded counit — extract at zero loss.
--
-- `keep` is the lattice bottom (`keep ⊔g g = g` definitionally) and
-- the monoidal unit of the loss grading. Observing with zero loss
-- recovers the bare echo. This is precisely the Pillar-A definitional
-- bridge reused: `GEcho keep` *is* `Echo collapse tt`, so the counit
-- is the identity coercion — no path algebra.

gextract : GEcho keep → Echo collapse tt
gextract e = e

----------------------------------------------------------------------
-- Graded comultiplication — duplicate by splitting the loss budget.
--
-- `gduplicate g₁ g₂ : GEcho g₁ → GEcho (g₁ ⊔g g₂)` re-grades an
-- observation up to the join. "Duplicating" the observation makes
-- room for an extra loss budget `g₂`; the canonical witness is the
-- join-left embedding. This is the comultiplication of the loss
-- comonad in the join-semilattice presentation.

gduplicate : ∀ g₁ g₂ → GEcho g₁ → GEcho (g₁ ⊔g g₂)
gduplicate g₁ g₂ = degrade (≤g-⊔g-left g₁ g₂)

----------------------------------------------------------------------
-- The three graded-comonad laws, in the common-upper-bound idiom.
--
-- Each law post-composes the relevant (co)multiplication with the
-- universal degrade into an ARBITRARY common bound `g'`, so every
-- statement has both sides in the *same* `GEcho g'` — no `subst`,
-- no transport. Each proof is then exactly `degrade-compose`
-- (path-independence of factored degrades) plus `≤g-prop`
-- (propositionality of the order), the two ingredients
-- `EchoGraded.degrade-via-join` already rests on.

-- Counit-left: duplicating with the trivial left budget `keep`,
-- then extracting that `keep` factor, is the identity reindexing.
-- (`keep ⊔g g = g` definitionally, so `gduplicate keep g` lands in
-- `GEcho g`; `gextract` is the identity coercion.)
gcomonad-counit-l :
  ∀ {g g'} (p : g ≤g g') (q : keep ≤g g') (e : GEcho keep) →
  degrade p (gduplicate keep g e) ≡ degrade q (gextract e)
gcomonad-counit-l {g} p q e =
  degrade-compose (≤g-⊔g-left keep g) p q e

-- Counit-right: duplicating with the trivial right budget `keep`,
-- then degrading on to any common bound, agrees with the direct
-- degrade. (`g ⊔g keep` is not definitionally `g` for a free `g`,
-- so the common-bound phrasing is what keeps this transport-free.)
gcomonad-counit-r :
  ∀ {g g'} (p : (g ⊔g keep) ≤g g') (q : g ≤g g') (e : GEcho g) →
  degrade p (gduplicate g keep e) ≡ degrade q e
gcomonad-counit-r {g} p q e =
  degrade-compose (≤g-⊔g-left g keep) p q e

-- Coassociativity: the two nested duplications associating the
-- triple budget as `(g₁ ⊔g g₂) ⊔g g₃` vs `g₁ ⊔g (g₂ ⊔g g₃)`,
-- each degraded on to a common bound `g`, agree. THE thesis bet.
--
-- The naive phrasing would compare `GEcho ((g₁⊔g₂)⊔g₃)` with
-- `GEcho (g₁⊔(g₂⊔g₃))` and force `subst GEcho (⊔g-assoc …)`. The
-- common-bound phrasing makes both sides land in `GEcho g`, so the
-- transport never appears: the proof is two `degrade-compose`
-- collapses on each side and a single `≤g-prop` between the two
-- resulting `g₁ ≤g g` witnesses. ZERO path algebra beyond `≤g-prop`.
gcomonad-coassoc :
  ∀ {g₁ g₂ g₃ g}
  (p : ((g₁ ⊔g g₂) ⊔g g₃) ≤g g)
  (q : (g₁ ⊔g (g₂ ⊔g g₃)) ≤g g)
  (e : GEcho g₁) →
  degrade p (gduplicate (g₁ ⊔g g₂) g₃ (gduplicate g₁ g₂ e))
  ≡ degrade q (gduplicate g₁ (g₂ ⊔g g₃) e)
gcomonad-coassoc {g₁} {g₂} {g₃} {g} p q e =
  let a = ≤g-⊔g-left g₁ g₂
      b = ≤g-⊔g-left (g₁ ⊔g g₂) g₃
      c = ≤g-⊔g-left g₁ (g₂ ⊔g g₃)
  in begin
    degrade p (degrade b (degrade a e))
      ≡⟨ degrade-compose b p (≤g-trans b p) (degrade a e) ⟩
    degrade (≤g-trans b p) (degrade a e)
      ≡⟨ degrade-compose a (≤g-trans b p)
           (≤g-trans a (≤g-trans b p)) e ⟩
    degrade (≤g-trans a (≤g-trans b p)) e
      ≡⟨ cong (λ z → degrade z e)
           (≤g-prop (≤g-trans a (≤g-trans b p)) (≤g-trans c q)) ⟩
    degrade (≤g-trans c q) e
      ≡⟨ sym (degrade-compose c q (≤g-trans c q) e) ⟩
    degrade q (degrade c e)
  ∎
  where open ≡-Reasoning
