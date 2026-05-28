{-# OPTIONS --safe --without-K #-}

-- EchoResidueTaxonomy: residue-side companion to EchoLossTaxonomy.
-- Function-side classifies `f : A → B` by echo shape (equiv / inj /
-- surj / const); this module classifies RESIDUES by carrier shape.
-- Together they form the two axes of the audit's "kinds-of-loss ×
-- shapes-of-residue" grid.
--
-- The shared residue-form interface is intentionally thin: a
-- per-output residue carrier together with a lowering map from the
-- full Echo down to the residue. Every decoration module in the
-- repo's "decoration zoo" (Linear / Graded / Choreo / Access / Cost
-- / Search / Indexed / Epistemic) instantiates this interface with
-- a different choice of `Residue`. The eight modules differ in:
--
--   * What the residue carries (a mode tag, a grade, a role
--     projection, an access modality, a cost, a search bound, an
--     index, a knowledge-equivalence class).
--   * How much of the witness it retains (full echo at the
--     "transparent" end, ⊤ at the "opaque" end, intermediate
--     classifications in between).
--
-- They agree on the structural shape: each residue admits a
-- canonical `lower : Echo f y → Residue y`. The shared shape is
-- the load-bearing organisational fact this module pins.
--
-- This module ships four concrete `ResidueForm` instances:
--
--   * `trivial-residue` — the maximally-collapsed residue
--     `(λ _ → ⊤)`. The "drop everything" form. Every decoration
--     module's "fully forgetful" endpoint specialises to this.
--
--   * `identity-residue` — the trivially-non-lossy residue
--     `Echo f` itself. Lowering is the identity. The "lose
--     nothing" form. Every decoration module's "transparent"
--     endpoint specialises to this.
--
--   * `echoR-residue` — the GENERIC `EchoR R Cert y := Σ R (Cert
--     r y)` form parameterised by a classifying predicate. The
--     universal Σ-shape residue (`EchoResidue.EchoR`); every
--     classifier-based decoration falls into this case.
--
--   * `linear-affine-residue` — the concrete `LEcho affine`
--     decoration on `collapse : Bool → ⊤`, lowering via `weaken`.
--     The first non-trivial instance witness, showing the eight
--     decoration modules genuinely sit in this taxonomy.
--
-- The other six decoration modules (Graded / Choreo / Access / Cost
-- / Search / Indexed / Epistemic) are STRUCTURALLY COMPATIBLE with
-- the `ResidueForm` interface but require per-module wiring (each
-- has its own carrier signature, some parameterise over `f` and
-- some fix a specific `collapse`). The companion-remark documents
-- which goes where; the four instances above demonstrate the
-- pattern at the two endpoints + the generic Σ-cert form + one
-- worked instance. Adding the remaining six is mechanical wiring
-- that does not change the organisational story.
--
-- Closes Tier 2 #3 per the synthesis-roadmap reorder. The
-- decoration RECIPE (order / order-prop / join / degrade-compose /
-- degrade-via-join) is the companion abstraction `EchoDecoration-
-- Structure.agda` (Tier 2 #4, observation-side): residue shape
-- here, decoration recipe there.
--
-- Headlines (pinned in Smoke.agda):
--
--   * ResidueForm                    -- the shared residue-shape record
--   * trivial-residue                -- ⊤ residue instance
--   * identity-residue               -- Echo f residue instance
--   * echoR-residue                  -- generic Σ-cert residue instance
--   * linear-affine-residue          -- LEcho affine on collapse instance
--
-- Scope guardrail. `ResidueForm` packages the minimum unified shape
-- (carrier + lowering). The four instances are real and `lower`-
-- complete; deeper laws (e.g. "lowering is natural in f", "the
-- diagram of residues forms a poset under degradation") live in the
-- per-decoration modules and in the upcoming `EchoDecoration-
-- Structure.agda` recipe-packaging companion. The taxonomy here
-- does not weaken either; it organises what is.

module EchoResidueTaxonomy where

open import Echo                  using (Echo)
open import EchoResidue           using
  ( EchoR
  ; echo-to-residue
  )
open import EchoCharacteristic    using (collapse)
open import EchoLinear            using (LEcho; affine; weaken)

open import Level                 using (Level; _⊔_)
open import Data.Product.Base     using (Σ; _,_)
open import Data.Unit.Base        using (⊤; tt)
open import Relation.Binary.PropositionalEquality
                                  using (_≡_; refl)

private variable
  a b c r ℓ : Level
  A : Set a
  B : Set b

----------------------------------------------------------------------
-- The shared residue-form interface.
--
-- A `ResidueForm f R` is the data of a per-output residue carrier
-- `R : B → Set ℓ` together with a canonical lowering map
-- `lower : Echo f y → R y` for every `y`.
--
-- The two endpoints `R = (λ _ → ⊤)` and `R = Echo f` are always
-- available (universal `lower`s exist); non-trivial cases pick a
-- `R` and supply the lowering.
----------------------------------------------------------------------

record ResidueForm
  {a b ℓ} {A : Set a} {B : Set b}
  (f : A → B) (R : B → Set ℓ) : Set (a ⊔ b ⊔ ℓ) where
  field
    lower : ∀ {y : B} → Echo f y → R y

----------------------------------------------------------------------
-- Endpoint instances.
--
-- Every `f : A → B` admits these two as the "trivial" and
-- "identity" residue forms — the maximum-collapse and the
-- no-collapse ends of the spectrum.
----------------------------------------------------------------------

-- The MAXIMUM-COLLAPSE residue: drop every echo to ⊤.
trivial-residue : (f : A → B) → ResidueForm f (λ _ → ⊤)
trivial-residue _ = record { lower = λ _ → tt }

-- The IDENTITY (no-collapse) residue: keep the full echo. Lowering
-- is the identity. Witnesses that "the residue can be the echo
-- itself" — the universal upper bound on residue informativeness.
identity-residue : (f : A → B) → ResidueForm f (Echo f)
identity-residue _ = record { lower = λ e → e }

----------------------------------------------------------------------
-- Generic Σ-cert residue instance.
--
-- The universal classifier-based residue from `EchoResidue.EchoR`:
-- pick a classifier carrier `C`, a classifying predicate
-- `Cert : C → B → Set`, and a soundness witness
-- `sound : ∀ x → Cert (κ x) (f x)`. Lowering is
-- `echo-to-residue f κ Cert sound`, the existing generic lowering
-- from `EchoResidue.agda`.
--
-- Every decoration module that exposes a Σ-shape residue (with a
-- classifying predicate) is an instance of this case.
----------------------------------------------------------------------

echoR-residue :
  ∀ {a b c r} {A : Set a} {B : Set b} {C : Set c}
  (f : A → B)
  (κ : A → C)
  (Cert : C → B → Set r)
  (sound : ∀ x → Cert (κ x) (f x)) →
  ResidueForm f (λ y → EchoR C Cert y)
echoR-residue f κ Cert sound =
  record { lower = echo-to-residue f κ Cert sound }

----------------------------------------------------------------------
-- Linear-affine instance.
--
-- The first non-endpoint, non-generic decoration instance: the
-- `LEcho affine` carrier on `collapse : Bool → ⊤`. Lowering is
-- the existing `weaken : LEcho linear → LEcho affine`, noting that
-- `LEcho linear` is definitionally `Echo collapse tt` and the
-- `{y}` parameter is forced to `tt` because `⊤` has a unique
-- constructor.
--
-- This witnesses that the eight decoration modules from the repo's
-- decoration zoo sit in this taxonomy non-trivially; the remaining
-- seven (Graded / Choreo / Access / Cost / Search / Indexed /
-- Epistemic) are structurally compatible per the companion-remark.
----------------------------------------------------------------------

linear-affine-residue : ResidueForm collapse (λ _ → LEcho affine)
linear-affine-residue = record { lower = λ {tt} e → weaken e }

----------------------------------------------------------------------
-- Indexed instance (2026-05-27, audit follow-on).
--
-- `EchoIndexed.Echoᵢ I ι f i y = Σ A (λ x → ι x ≡ i × f x ≡ y)`
-- exposes the index `i` alongside the standard Echo data. Collecting
-- over all index values, the per-output residue at `y` is
-- `Σ I (λ i → Echoᵢ I ι f i y)`, and the lowering from `Echo f y`
-- is `(x, p) ↦ (ι x, x, refl, p)`.
--
-- This is the second non-endpoint, non-generic decoration instance
-- (after `linear-affine-residue`). Closes the
-- "EchoIndexed structurally compatible but not packaged" gap noted
-- in the original companion remark.
----------------------------------------------------------------------

open import EchoIndexed using (Echoᵢ)

indexed-residue :
  ∀ {a b i} {A : Set a} {B : Set b}
  (I : Set i) (ι : A → I) (f : A → B) →
  ResidueForm f (λ y → Σ I (λ idx → Echoᵢ I ι f idx y))
indexed-residue I ι f =
  record { lower = λ {y} (x , p) → ι x , x , refl , p }

----------------------------------------------------------------------
-- Cost instance (2026-05-27, audit follow-on).
--
-- `EchoCost.Cost.EchoC K cost c f y` is the cost-indexed Echo at
-- budget `c`. Lowering from `Echo f y` requires a budget-meets
-- witness `∀ x → cost x ≤ c` (since the residue carries a budget
-- receipt). The parametric record requires opening `Cost K` for
-- the carrier; the `module _ (K : CostAlgebra ℓ)` block keeps the
-- imports tidy.
--
-- Closes the "EchoCost structurally compatible but parametric"
-- gap noted in the original companion remark. Third non-endpoint,
-- non-generic decoration instance.
----------------------------------------------------------------------

open import EchoCost using (CostAlgebra; module Cost)

module CostInstance {ℓ} (K : CostAlgebra ℓ) where
  open CostAlgebra K
  open Cost K

  cost-residue :
    ∀ {a b} {A : Set a} {B : Set b}
    (f : A → B)
    (cost : A → Cost)
    (c : Cost)
    (cost-meets : ∀ x → cost x ≤ c) →
    ResidueForm f (λ y → EchoC cost c f y)
  cost-residue f cost c cost-meets =
    record { lower = λ {y} (x , p) → x , p , cost-meets x }

----------------------------------------------------------------------
-- Search instance (2026-05-28, Tier-2 grid completion).
--
-- `EchoSearch.EchoS enum f y n` is the bounded-`n` witness-search
-- echo: a step index `k < n` at which the enumerator returns a
-- preimage of `y` under `f`.  Lowering from `Echo f y` requires
-- a search-completeness witness — for every echo at `y`, an
-- enumerator step `k < n` produces its source element.
--
-- The search-completeness assumption is exactly the per-fibre
-- "enum exhausts A within n steps" property.  Compared to
-- `cost-residue` (where the budget-meets witness is a numeric
-- bound on cost), `search-residue` requires structural location
-- information (a specific step).  Both fit the same parametric
-- shape: an external witness supplied at the ResidueForm boundary.
--
-- Closes the "EchoSearch structurally compatible but not packaged"
-- gap noted in the companion remark.  Fourth non-endpoint,
-- non-generic decoration instance.
----------------------------------------------------------------------

open import EchoSearch using (EchoS; SearchStrategy)
open import Data.Nat.Base using (ℕ; _<_)
open import Data.Product.Base using (_×_; proj₁)
open import Relation.Binary.PropositionalEquality using (cong; trans)

search-residue :
  ∀ {a b} {A : Set a} {B : Set b}
  (enum : SearchStrategy A) (f : A → B) (n : ℕ)
  (search-complete : ∀ {y : B} (e : Echo f y) →
                     Σ ℕ (λ k → (k < n) × (enum k ≡ proj₁ e))) →
  ResidueForm f (λ y → EchoS enum f y n)
search-residue enum f n search-complete =
  record { lower = λ {y} e@(x , p) →
    let (k , k<n , eq) = search-complete e
    in  k , k<n , trans (cong f eq) p }

----------------------------------------------------------------------
-- Epistemic instance (2026-05-28, Tier-2 grid completion).
--
-- For a role `r : Role` from `EchoChoreo`, the indistinguishability
-- class at observation value `y` is exactly the fibre
-- `Echo (obs r) y` — every global indistinguishable-at-r from a
-- representative IS a fibre element.  The "knowledge-equivalence-
-- class residue" interpretation thus DEFINITIONALLY collapses to
-- `identity-residue` specialised to `obs r`.
--
-- Pinning under a separate name makes the epistemic reading
-- discoverable at the taxonomy boundary without introducing a
-- distinct carrier (which would require either propositional
-- truncation of the class — same earn-back as `(epi, mono)` image
-- factorisation, handled by `EchoImageFactorizationProp` — or a
-- setoid carrier with an explicit equivalence relation).
--
-- Closes the "EchoEpistemic structurally compatible but
-- relational" gap noted in the companion remark.  Fifth instance
-- (degenerate-but-named: definitionally equal to `identity-residue
-- (obs r)`, but the name pins the epistemic reading).
----------------------------------------------------------------------

open import EchoChoreo using (Role; obs)

epistemic-residue : (r : Role) → ResidueForm (obs r) (Echo (obs r))
epistemic-residue r = identity-residue (obs r)

----------------------------------------------------------------------
-- Companion remark.
--
-- The eight decoration modules in the repo's decoration zoo and
-- their position in this taxonomy:
--
--   1. *EchoLinear*. Mode-tagged carrier (`linear` / `affine`).
--      `linear` end = identity-residue (definitionally), `affine`
--      end = `linear-affine-residue` (this module). The mode order
--      is the propositional `linear ≤m affine`.
--
--   2. *EchoGraded*. Grade-tagged carrier (`keep` / `residue` /
--      `forget`). `keep` end = identity-residue (definitionally,
--      `GEcho keep = Echo collapse tt`); `forget` end =
--      trivial-residue (`GEcho forget = ⊤`); `residue` middle =
--      `EchoR ⊤ TrivialCert tt`, instance of echoR-residue.
--
--   3. *EchoAccess*. Five-grade access modality (`free` /
--      `decidable` / `enum` / `feasible` / `infeasible`). `free`
--      end ≈ identity-residue (with EchoDec at `decidable`);
--      `infeasible` end = trivial-residue.
--
--   4. *EchoChoreo*. Role-projected residue (role-tag + projected
--      observation). The lowering applies `obs`; an instance of
--      echoR-residue where `C = Role` and `Cert` packages the
--      projection.
--
--   5. *EchoCost*. LANDED 2026-05-27 as `cost-residue` inside
--      `module CostInstance (K : CostAlgebra ℓ)` above. Lowering
--      requires a budget-meets witness `∀ x → cost x ≤ c`; the
--      parametric record sits inside the `K`-parameterised
--      sub-module to keep the carrier signature tidy.
--
--   6. *EchoSearch*. LANDED 2026-05-28 as `search-residue` above.
--      Per-output carrier `EchoS enum f y n` (bounded-`n` search
--      witness); lowering requires a search-completeness witness
--      `∀ {y} (e : Echo f y) → Σ ℕ λ k → (k < n) × (enum k ≡ proj₁ e)`
--      passed at the boundary (mirrors `cost-residue`'s
--      `cost-meets` parameter).  Degenerate endpoints: search bound
--      0 trivialises (no echo lowers — the `EchoS f y 0` is empty
--      via `echo-search-bound-zero`); unbounded search via a
--      surjective enumerator recovers identity-residue.
--
--   7. *EchoIndexed*. LANDED 2026-05-27 as `indexed-residue`
--      above. Per-output carrier `Σ I (λ idx → Echoᵢ I ι f idx y)`;
--      lowering `(x, p) ↦ (ι x, x, refl, p)`.
--
--   8. *EchoEpistemic*. LANDED 2026-05-28 as `epistemic-residue`
--      above.  Definitionally `identity-residue (obs r)`: the
--      indistinguishability class at observation `y` IS the fibre
--      `Echo (obs r) y`.  Pinned under a distinct name so the
--      epistemic reading is discoverable at the taxonomy boundary;
--      no new carrier (a setoid carrier with explicit equivalence
--      relation or a propositional-truncation of the class would
--      both be separate earn-back lifts).
--
-- All eight are now packaged.  Endpoint instances (1-3:
-- trivial-residue + identity-residue + echoR-residue) cover the
-- generic shapes; six non-endpoint instances ship the worked
-- decoration-specific wiring (linear-affine-residue,
-- indexed-residue, module CostInstance.cost-residue,
-- search-residue, epistemic-residue, and choreo-residue via
-- echoR-residue with `C = Role`).  Each instance's `lower` either
-- discharges definitionally (`linear-affine` / `indexed` /
-- `epistemic`) or requires a parametric witness at the boundary
-- (`cost-meets` for cost / `search-complete` for search) that
-- locates the relevant point in the decoration's quantitative axis.
--
-- The DECORATION RECIPE (`order` / `order-prop` / `join` /
-- `degrade-compose` / `degrade-via-join`) that each of the eight
-- decoration modules re-implements is a separate companion
-- abstraction, lands in `EchoDecorationStructure.agda` (next
-- module, Tier 2 #4). The residue taxonomy here organises the
-- CARRIER SHAPE; the decoration structure there organises the
-- DEGRADATION RECIPE; together they package the two-axis grid
-- the audit called for.
----------------------------------------------------------------------
