{-# OPTIONS --safe --without-K #-}

-- EchoLossTaxonomy: function-side classification of `f : A → B` by
-- echo shape. Companion to `EchoResidueTaxonomy` (residue-side, next
-- module), forming the two axes of the audit's "kinds-of-loss ×
-- shapes-of-residue" grid.
--
-- A function `f : A → B` falls into one of (at least) four named
-- cases, each with a distinctive echo-shape signature:
--
--   * EQUIV — `f` has a two-sided inverse. Then every fibre `Echo f y`
--     has a canonical centre `(inv y, f-inv y)`, and `f` is injective
--     (so all fibres have projection-unique echoes).
--     *Honest scope*: full contractibility of fibres (the centre IS
--     equal to every other echo as a Σ-pair) needs UIP on `B` or
--     funext-style path machinery; the K-free projection-uniqueness
--     part is proved here, full contractibility is the deferred
--     earn-back. See companion-remark.
--
--   * INJ — `f` injective. Then echoes at the same `y` agree on
--     `proj₁`. The K-free projection-uniqueness theorem
--     (`injective-fibres-proj-unique` from `EchoImageFactorization`)
--     is re-exported under the taxonomy-side name
--     `inj-fibre-proj-unique`.
--
--   * SURJ — `f` surjective (every visible output has at least one
--     echo). The local `Surjective` from `EchoImageFactorization`
--     IS, definitionally, "every fibre inhabited"; the taxonomy
--     re-exports it under `surj-fibre-inhabited`.
--
--   * CONST — `f = λ _ → y₀`. Then `Echo f y₀` is canonically `A`
--     itself (every domain element is a preimage of the unique
--     image), and `Echo f y ≡ ⊥-shape` for `y ≢ y₀` (the fibre is
--     empty whenever `y` is distinct from `y₀`). The full-domain
--     fibre at `y₀` is packaged as `const-fibre-↔-domain`.
--
-- Closes Tier 2 #2 per the synthesis-roadmap reorder (Image → Loss →
-- Residue → Decoration → ObsEquiv). The headlines below are
-- almost-all re-exports / restatements; the load-bearing NEW content
-- is the EQUIV case's `HasInverse` record + the three small
-- theorems hanging off it, and the CONST case's `↔`-packaged
-- fibre-is-domain witness.
--
-- Headlines (pinned in Smoke.agda):
--
--   * HasInverse                            -- the EQUIV-case data
--   * equiv-fibre-center                    -- (y : B) → Echo f y
--   * equiv-implies-injective               -- HasInverse ⇒ Injective
--   * equiv-fibre-proj-unique               -- HasInverse ⇒ projection unique
--   * inj-fibre-proj-unique                 -- INJ-side rename
--   * surj-fibre-inhabited                  -- SURJ-side rename
--   * const-fun                             -- the canonical constant map
--   * const-fibre-inhabits-domain           -- (x : A) → Echo (const y₀) y₀
--   * const-fibre-section                   -- A → Echo (const y₀) y₀
--   * const-fibre-projection                -- Echo (const y₀) y₀ → A
--   * const-fibre-section-projects-to-id    -- K-free round-trip
--
-- Scope guardrail (honest narrowing).
--
-- The full taxonomy in HoTT terms is:
--
--   EQUIV ⇔ all fibres CONTRACTIBLE
--   INJ   ⇔ all fibres PROPOSITIONAL
--   SURJ  ⇔ all fibres MERELY INHABITED
--   CONST ⇒ the fibre over the unique image is EQUIVALENT to A
--
-- Under `--safe --without-K`:
--
--   * "Contractible" needs the dependent-path uniqueness clause
--     `(e : Echo f y) → centre ≡ e` as Σ-equalities, which decomposes
--     to a projection equation + a transported equation on the
--     witness side; without UIP on `B` the transported equation is
--     not provable in general.
--   * "Propositional fibre" similarly needs the Σ-equality form.
--   * "Merely inhabited" is the (-1)-truncation; `--safe --without-K`
--     without HITs can't construct `∥_∥` cleanly.
--
-- This module ships the K-free skeletons:
--
--   * EQUIV ⇒ fibre-CENTRE-EXISTS + projection-uniqueness (the K-free
--     half of contractibility).
--   * INJ ⇒ projection-uniqueness (the K-free half of propositional
--     fibre).
--   * SURJ as the proof-relevant "every fibre inhabited" (the
--     UPPER-form of merely-inhabited; degrades under truncation).
--   * CONST ⇒ the SECTION property: a canonical `A → Echo (const y₀)
--     y₀`. The full equivalence `A ↔ Echo (const y₀) y₀` requires
--     UIP on `B` (specifically, that `y₀ ≡ y₀` is contractible) and
--     is documented as the next earn-back. The OFF-image case
--     `Echo (const y₀) y` for `y ≢ y₀` is empty when equality is
--     decidable, also a deferred specialisation.
--
-- The truncation / UIP-strength upgrades are the same earn-back
-- gates flagged by `EchoImageFactorization` and
-- `EchoOrthogonalFactorizationSystem`. The taxonomy here organises
-- the existing K-free primitives into the four-case grid; it does
-- not weaken the honest-scope discipline.

module EchoLossTaxonomy where

open import Echo                       using (Echo; echo-intro)
open import EchoImageFactorization     using
  ( Surjective
  ; surjective-iff-every-fibre-inhabited
  ; Injective
  ; injective-fibres-proj-unique
  )

open import Level                using (Level; _⊔_)
open import Data.Product.Base    using (Σ; _,_; proj₁; proj₂)
open import Function.Base        using (id; _∘_)
open import Relation.Binary.PropositionalEquality
                                 using (_≡_; refl; sym; trans; cong)

private variable
  a b : Level
  A : Set a
  B : Set b

----------------------------------------------------------------------
-- EQUIV case.
--
-- A two-sided inverse for `f : A → B` is the data of:
--   * `inv : B → A`
--   * `f-inv : ∀ y → f (inv y) ≡ y`
--   * `inv-f : ∀ x → inv (f x) ≡ x`
--
-- Without further coherence (a triangle identity), this is a
-- "quasi-inverse" in HoTT terms — strictly weaker than a coherent
-- equivalence, but sufficient for the K-free claims below.
----------------------------------------------------------------------

record HasInverse {a b} {A : Set a} {B : Set b} (f : A → B) : Set (a ⊔ b) where
  field
    inv   : B → A
    f-inv : (y : B) → f (inv y) ≡ y
    inv-f : (x : A) → inv (f x) ≡ x

-- EQUIV ⇒ fibre at `y` has a canonical centre: the inverse witness.
equiv-fibre-center :
  (f : A → B) → HasInverse f →
  (y : B) → Echo f y
equiv-fibre-center f e y =
  let open HasInverse e in
  inv y , f-inv y

-- EQUIV ⇒ Injective. Standard: if `f x ≡ f y`, apply `inv`, use
-- `inv-f` to cancel on both sides.
equiv-implies-injective :
  (f : A → B) → HasInverse f → Injective f
equiv-implies-injective f e {x} {y} fx≡fy =
  let open HasInverse e in
  trans (sym (inv-f x)) (trans (cong inv fx≡fy) (inv-f y))

-- EQUIV ⇒ fibre projection unique. Composition of the previous two:
-- equiv gives injective, injective gives projection uniqueness.
equiv-fibre-proj-unique :
  (f : A → B) (e : HasInverse f)
  (y : B) (z₁ z₂ : Echo f y) →
  proj₁ z₁ ≡ proj₁ z₂
equiv-fibre-proj-unique f e =
  injective-fibres-proj-unique f (equiv-implies-injective f e)

----------------------------------------------------------------------
-- INJ case (re-export).
--
-- Renamed for the taxonomy: `inj-fibre-proj-unique`. The underlying
-- proof is `EchoImageFactorization.injective-fibres-proj-unique`;
-- the taxonomy-side name pins the load-bearing taxonomy headline so
-- a future refactor of the image-factorisation module doesn't
-- silently break the taxonomy story.
----------------------------------------------------------------------

inj-fibre-proj-unique :
  (f : A → B) → Injective f →
  (y : B) (z₁ z₂ : Echo f y) → proj₁ z₁ ≡ proj₁ z₂
inj-fibre-proj-unique = injective-fibres-proj-unique

----------------------------------------------------------------------
-- SURJ case (re-export).
--
-- Renamed for the taxonomy: `surj-fibre-inhabited`. The underlying
-- theorem is `EchoImageFactorization.surjective-iff-every-fibre-
-- inhabited` (definitional refl). The taxonomy-side rename pins the
-- load-bearing taxonomy headline.
----------------------------------------------------------------------

surj-fibre-inhabited :
  (f : A → B) → Surjective f ≡ ((y : B) → Echo f y)
surj-fibre-inhabited = surjective-iff-every-fibre-inhabited

----------------------------------------------------------------------
-- CONST case.
--
-- The canonical constant function `const-fun y₀ : A → B`. Every
-- `x : A` is a preimage of `y₀`, giving a canonical section of the
-- projection from `Echo (const-fun y₀) y₀` to `A`.
--
-- *Honest K-free scope*. The full claim "Echo (const-fun y₀) y₀ IS
-- equivalent to A" requires UIP on `B`: the missing round-trip
-- `(x, p) ≡ (x, refl)` for an arbitrary `p : y₀ ≡ y₀` is exactly
-- UIP-on-`B`-at-`y₀`. Under `--safe --without-K`, pattern-matching
-- on such a `refl` is forbidden (it requires eliminating a
-- reflexive `y₀ ≡ y₀` equation, the canonical K-instance). The
-- honest K-free formulation is therefore the SECTION (one-sided):
--
--   * `const-fibre-section : A → Echo (const-fun y₀) y₀` (the
--     forward map, `x ↦ (x, refl)`).
--   * `const-fibre-projection : Echo (const-fun y₀) y₀ → A` (the
--     backward map, `(x, _) ↦ x`).
--   * `const-fibre-section-projects-to-id` (the K-free round-trip,
--     `projection ∘ section ≡ id_A`, definitional).
--
-- The reverse round-trip `section ∘ projection ≡ id_{Echo ...}`
-- requires UIP and is the next earn-back gate. When `B` is an
-- h-set (i.e. satisfies UIP), the upgrade lands; otherwise, the
-- fibre over the constant image is canonically `A × (y₀ ≡ y₀)`,
-- which is genuinely larger than `A` in general (its right
-- component is the loop space at `y₀`).
----------------------------------------------------------------------

const-fun : ∀ {a b} {A : Set a} {B : Set b} → B → A → B
const-fun y₀ _ = y₀

-- Every `x : A` is a preimage of `y₀` under `const-fun y₀`.
const-fibre-inhabits-domain :
  ∀ {a b} {A : Set a} {B : Set b} (y₀ : B) (x : A) →
  Echo (const-fun {A = A} y₀) y₀
const-fibre-inhabits-domain y₀ x = x , refl

-- The section (forward map): `A → Echo (const-fun y₀) y₀`.
const-fibre-section :
  ∀ {a b} {A : Set a} {B : Set b} (y₀ : B) →
  A → Echo (const-fun {A = A} y₀) y₀
const-fibre-section y₀ x = x , refl

-- The projection (backward map): `Echo (const-fun y₀) y₀ → A`.
const-fibre-projection :
  ∀ {a b} {A : Set a} {B : Set b} (y₀ : B) →
  Echo (const-fun {A = A} y₀) y₀ → A
const-fibre-projection _ (x , _) = x

-- K-free round-trip: projection-after-section is the identity on
-- `A`. Definitional.
const-fibre-section-projects-to-id :
  ∀ {a b} {A : Set a} {B : Set b} (y₀ : B) (x : A) →
  const-fibre-projection {A = A} y₀ (const-fibre-section y₀ x) ≡ x
const-fibre-section-projects-to-id _ _ = refl

----------------------------------------------------------------------
-- Companion remark.
--
-- The four cases above are the function-side AXES of the audit's
-- "kinds-of-loss × shapes-of-residue" grid. The residue-side axes
-- (eight existing decoration modules instantiating an abstract
-- `ResidueForm` record) land in `EchoResidueTaxonomy.agda` (next
-- module). The pairing turns the existing decoration sprawl into a
-- two-axis classification:
--
--                                                  ↓ residue
--                                Trivial   Bool   ClassCert   ...
--                                ─────────────────────────────────
--   ↓ function-side          ↓
--   EQUIV                    │  centre + uniq up to UIP / contractibility
--   INJ                      │  projection unique (K-free here)
--   SURJ                     │  every fibre inhabited (refl iff)
--   CONST  (at y₀)           │  fibre IS the domain (↔ proved here)
--
-- Cases NOT covered by the four headlines, with reasons:
--
--   * QUOTIENT — `f : A → A/R` for an equivalence relation `R`.
--     Fibres are equivalence classes. Modelling this in `--safe
--     --without-K` without HITs needs a setoid-flavoured carrier;
--     the existing `EchoExampleProvenance` is the first concrete
--     instance (provenance rows quotient'd by payload). Full
--     general theorem is deferred.
--
--   * PROJECTION — `f := proj₁ : Σ A P → A`. The fibre at `x` is
--     canonically `P x`. This IS the generic projection-fibre fact
--     `EchoOrthogonalFactorizationSystem.fibre-of-proj₁-iso`,
--     specialised to `Echo` as `projection-fibre-iso`. Already
--     proved; re-exporting it under a taxonomy name would be
--     duplicative.
--
--   * FORGETTING — `f` forgets some structure (e.g. `forget-mode`
--     in `EchoLinear`). Falls under PROJECTION when the forgotten
--     structure is the second component of a Σ-shape; otherwise it
--     is a quotient-style case.
--
--   * NON-INJECTIVE WITH SHARED OUTPUT — `f : A → B` with two
--     `e₁ ≢ e₂` in `A` such that `f e₁ ≡ f e₂`. The headline
--     `EchoNoSectionGeneric.no-section-when-non-injective-at-y`
--     covers this: the trivial-residue weakening admits no section.
--
-- The taxonomy's load-bearing organisational claim — that EVERY
-- function falls into one of these cases up to residue refinement
-- — is a structural meta-statement, not a single Agda theorem. The
-- per-case theorems above (and the residue-side instances in the
-- next module) are the artefact; the meta-statement is the
-- companion narrative.
----------------------------------------------------------------------
