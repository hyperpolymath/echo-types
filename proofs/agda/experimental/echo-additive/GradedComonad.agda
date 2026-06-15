{-# OPTIONS --safe --without-K #-}

-- EXPERIMENTAL — R3 SECONDARY LINE (comonadic δ).
-- Colaxator δ_{r,s} : D (r +g s) A → D r (D s A), the SPLITTING direction,
-- grounded in Echo-comp-iso-to (Echo.agda:73-96). Target: discharge the
-- coassociativity law (plus the two counit laws) in --safe --without-K, or
-- PARK any law with a named obstruction (-- OBLIGATION:). Reporting the
-- truth is the finding (STATE.adoc §"Terminating condition").
--
-- FIREWALL (DECISIONS.adoc D-2026-06-14-R1): this file does NOT import
-- GradedMonad.agda. Shared dependency is GradedCarrier only. No postulate,
-- no hole, no escape pragma. Not imported by any shipped module.
--
-- This is a NEW experimental structure. It is NOT a reinstatement of the
-- R-2026-05-18-retracted shipped graded-comonad claim (which stands
-- retracted; EchoGraded/EchoGradedComonad are read-only and untouched).
--
-- ══════════════════════════════════════════════════════════════════════
-- HEADLINE FINDING (honest, do-not-force-a-win): on the R2 inert ⊤-padded
-- carrier the comonadic line is NOT obstructed at the level of law-discharge.
-- δ is TOTAL, coassociativity holds, and BOTH counit laws hold — all by
-- refl / structural induction, ZERO postulates, ZERO holes. By the letter of
-- STATE.adoc this is terminating-condition (ii): both lines discharge.
--
-- BUT the discharge is VACUOUS, and the vacuity IS the variance finding's
-- carrier-side shadow, mechanised here as three facts:
--   (a) δ's fin/inf case MANUFACTURES the m intermediate layers that total
--       collapse destroyed (δ (fin m) inf = const (D-fin-⊤-pt m)); it types
--       only because every target is (merely) inhabited (§2).
--   (b) every finite carrier over ⊤ is CONTRACTIBLE (D-fin-⊤-contr, §6), so
--       the "invented" structure in (a) is the UNIQUE inhabitant — the laws
--       structurally CANNOT detect the invention, which is why they pass.
--   (c) the laws hold precisely BECAUSE D (fin n) A carries no recoverable
--       content (carrier inertness, GradedCarrier §1). A content-bearing
--       finite layer would make δ's fin/inf case FAIL TO TYPE (no total
--       ⊤ → D-fin m (content)) — that is the obstruction the inert carrier
--       hides. Recorded as the §7 OBLIGATION (the only parked item).
-- Per STATE.adoc terminating condition (ii): the recommendation is to BEGIN
-- the separate adjunction F_r ⊣ U_r attempt — explicitly NOT done in this run.
-- ══════════════════════════════════════════════════════════════════════

module experimental.echo-additive.GradedComonad where

open import Data.Nat.Base using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-assoc; +-identityʳ)
open import Data.Unit.Base using (⊤; tt)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂; _×_)
open import Function.Base using (_∘_; id)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)

open import experimental.echo-additive.Grade
  using (Grade; fin; inf; _+g_; +g-assoc; +g-identityʳ; +g-identityˡ)
open import experimental.echo-additive.GradedCarrier
  using (D; D-fin; D-fin-+-split)

-- Read-only import of the shipped Echo composition iso. δ is the
-- "to" (splitting) direction; cited as the variance witness.
open import Echo using (Echo; Echo-comp-iso-to)

----------------------------------------------------------------------
-- R3 §1 — δ on finite grades, grounded in the splitting direction
--
-- On finite grades, D (fin m +g fin n) A = D-fin (m + n) A and
-- D (fin m) (D (fin n) A) = D-fin m (D-fin n A). The carrier split
-- D-fin-+-split is the SHAPE of the Echo-comp-iso "to" direction
-- specialised to the additive carrier: the only generic instantiation
-- the carrier admits is Echo-comp-iso-to id id, whose split is the
-- doubly-contractible transport realised here as `subst` (GradedCarrier
-- §1 adversarial note). δ reads that path LEFT-to-RIGHT (split):

δ-fin : ∀ m n {A} → D-fin (m + n) A → D-fin m (D-fin n A)
δ-fin m n {A} = subst (λ T → T) (D-fin-+-split m n)

-- ── Echo-comp-iso-to grounding (load-bearing, not decorative) ──────
-- A finite layer's residue is the split of `Echo (id∘id) y` via the
-- shipped Echo-comp-iso-to. The additive carrier supplies no codomain
-- map, so the only generic instantiation is `id`/`id`, and the splitting
-- direction lands in the DOUBLY-CONTRACTIBLE image: inner `Echo id b` is
-- a singleton at b, outer `b ≡ y` a singleton at y. This is the precise
-- shadow δ-fin transports along; the equation below pins it as `refl`.
echo-layer-split : ∀ {A : Set} {y : A} →
  Echo (id {A = A}) y → Σ A (λ b → Echo (id {A = A}) b × (b ≡ y))
echo-layer-split {A} {y} = Echo-comp-iso-to (id {A = A}) (id {A = A}) {y = y}

echo-layer-split-contractible : ∀ {A : Set} {y : A} →
  echo-layer-split {A} {y} (y , refl) ≡ (y , (y , refl) , refl)
echo-layer-split-contractible = refl

-- canonical inhabitant of any finite ⊤-padded carrier over ⊤
D-fin-⊤-pt : ∀ m → D-fin m ⊤
D-fin-⊤-pt zero    = tt
D-fin-⊤-pt (suc m) = tt , D-fin-⊤-pt m

----------------------------------------------------------------------
-- R3 §2 — δ on the full grade.  ADVERSARIAL TOTALITY CHECK (it TYPES).
--
-- δ_{r,s} : D (r +g s) A → D r (D s A).  Case split on r, s:
--
--   r=fin m, s=fin n : source D-fin (m+n) A → target D-fin m (D-fin n A).
--     Total via δ-fin.  (the finite, inert case.)
--   r=inf            : r +g s = inf, SOURCE = ⊤, TARGET = ⊤. Total: λ _ → tt.
--   r=fin m, s=inf   : r +g s = inf, SOURCE = ⊤, TARGET = D-fin m ⊤.
--     D-fin m ⊤ IS inhabited, so a total map ⊤ → D-fin m ⊤ EXISTS (constant
--     at D-fin-⊤-pt m). This case MANUFACTURES the m intermediate layers
--     that total collapse (inf) destroyed.
--
-- δ IS TOTAL — but only because every target is (merely) inhabited. The
-- fin/inf case is the diagnostic: on any carrier whose layers carried
-- recoverable content, ⊤ → D-fin m (content) would be UNINHABITED and δ
-- would FAIL TO TYPE. Totality is bought entirely by carrier inertness.
-- This is the carrier-side shadow of the R1 variance finding: the
-- splitting direction "invents" the structure the grade claims to track.
-- (§6 proves the invented structure is the UNIQUE inhabitant, which is why
-- the §5/§6 laws cannot detect the invention.)

δ : ∀ r s {A} → D (r +g s) A → D r (D s A)
δ (fin m) (fin n) {A} = δ-fin m n {A}
δ (fin m) inf     {A} = λ _ → D-fin-⊤-pt m
δ inf     s       {A} = λ _ → tt

----------------------------------------------------------------------
-- R3 §3 — carrier functorial action (needed to state D_r(δ_{s,t}))
--
-- On the ⊤-padded carrier this is map-on-payload; total and law-abiding.

D-fin-map : ∀ m {A B} → (A → B) → D-fin m A → D-fin m B
D-fin-map zero    h x        = h x
D-fin-map (suc m) h (t , xs) = t , D-fin-map m h xs

D-map : ∀ r {A B} → (A → B) → D r A → D r B
D-map (fin m) h = D-fin-map m h
D-map inf     h = λ _ → tt

----------------------------------------------------------------------
-- R3 §4 — transport-peel lemmas for the ⊤-padded carrier

-- transport along a `⊤ ×`-congruence of a Set-identity bundle
subst-⊤× : ∀ {X Y : Set} (p : X ≡ Y) (t : ⊤) (xs : X) →
  subst (λ T → T) (cong (λ T → ⊤ × T) p) (t , xs) ≡ (t , subst (λ T → T) p xs)
subst-⊤× refl t xs = refl

-- δ-fin peels a ⊤ layer on the LEFT (source successor)
δ-fin-suc : ∀ m n {A} (t : ⊤) (xs : D-fin (m + n) A) →
  δ-fin (suc m) n (t , xs) ≡ (t , δ-fin m n xs)
δ-fin-suc m n t xs = subst-⊤× (D-fin-+-split m n) t xs

-- subst peel through `cong suc` of a ℕ-carrier transport (reused by §5/§6).
subst-Dfin-suc : ∀ {A} {j k : ℕ} (p : j ≡ k) (t : ⊤) (xs : D-fin j A) →
  subst (λ i → D-fin i A) (cong suc p) (t , xs)
    ≡ (t , subst (λ i → D-fin i A) p xs)
subst-Dfin-suc refl t xs = refl

-- ⊤ is a proposition.
⊤-prop : (x y : ⊤) → x ≡ y
⊤-prop tt tt = refl

-- D-fin m preserves propositionality: if X is a proposition so is D-fin m X.
-- Load-bearing for the mixed-inf coassoc cases (where the innermost payload
-- is some D inf (…) = ⊤, a proposition, and the finite padding preserves it).
D-fin-pres-prop : ∀ m {X} → ((x y : X) → x ≡ y) → (u v : D-fin m X) → u ≡ v
D-fin-pres-prop zero    pX u        v        = pX u v
D-fin-pres-prop (suc m) pX (s , us) (t , vs) =
  cong₂ _,_ (⊤-prop s t) (D-fin-pres-prop m pX us vs)

----------------------------------------------------------------------
-- R3 §5 — coassociativity LAW   [DISCHARGED]
--
-- The comonadic colaxator coassociativity (STATE.adoc:226):
--
--   D_r(δ_{s,t}) ∘ δ_{r,s+t}  =  δ_{r+s,t} ∘ δ_{r,s}
--
-- Both sides : D ((r +g s) +g t) A → D r (D s (D t A)). The LHS reads its
-- source at the r +g (s +g t) grouping, so we pre-compose with the grade
-- associator transport `assoc-src`. (For every grade triple with at least
-- one `inf`, +g-assoc reduces to refl — Grade.agda:82-84 — so the
-- associator is the identity there; only the all-finite branch carries a
-- genuine `cong fin (+-assoc …)` path.)

assoc-src : ∀ r s t {A} → D ((r +g s) +g t) A → D (r +g (s +g t)) A
assoc-src r s t {A} = subst (λ g → D g A) (+g-assoc r s t)

-- All-finite coassoc, source pinned at (a+b)+c, associated up on the LHS.
coassoc-fin : ∀ a b c {A} (d : D-fin ((a + b) + c) A) →
  D-fin-map a (δ-fin b c)
    (δ-fin a (b + c) (subst (λ k → D-fin k A) (+-assoc a b c) d))
    ≡ δ-fin a b (δ-fin (a + b) c d)
coassoc-fin zero    b c d        = refl
coassoc-fin (suc a) b c (t , xs) = begin
  D-fin-map (suc a) (δ-fin b c)
    (δ-fin (suc a) (b + c) (subst (λ k → D-fin k _) (+-assoc (suc a) b c) (t , xs)))
    ≡⟨ cong (λ z → D-fin-map (suc a) (δ-fin b c) (δ-fin (suc a) (b + c) z))
         (subst-Dfin-suc (+-assoc a b c) t xs) ⟩
  D-fin-map (suc a) (δ-fin b c)
    (δ-fin (suc a) (b + c) (t , subst (λ k → D-fin k _) (+-assoc a b c) xs))
    ≡⟨ cong (D-fin-map (suc a) (δ-fin b c))
         (δ-fin-suc a (b + c) t (subst (λ k → D-fin k _) (+-assoc a b c) xs)) ⟩
  (t , D-fin-map a (δ-fin b c)
         (δ-fin a (b + c) (subst (λ k → D-fin k _) (+-assoc a b c) xs)))
    ≡⟨ cong (λ z → t , z) (coassoc-fin a b c xs) ⟩
  (t , δ-fin a b (δ-fin (a + b) c xs))
    ≡⟨ sym (δ-fin-suc a b t (δ-fin (a + b) c xs)) ⟩
  δ-fin (suc a) b (t , δ-fin (a + b) c xs)
    ≡⟨ cong (δ-fin (suc a) b) (sym (δ-fin-suc (a + b) c t xs)) ⟩
  δ-fin (suc a) b (δ-fin (suc (a + b)) c (t , xs))
    ∎
  where open ≡-Reasoning

-- Bridge: assoc-src on all-finite grades is the ℕ-level carrier transport.
-- +g-assoc (fin a)(fin b)(fin c) = cong fin (+-assoc a b c) (Grade.agda:81),
-- and a `subst` over `D g A` along a `cong fin` path equals the `subst`
-- over `D-fin k A` along the underlying ℕ path. Both reduce together by
-- path induction on the ℕ-equation.
private
  bridge-fin : ∀ {A} {j k : ℕ} (p : j ≡ k) (d : D-fin j A) →
    subst (λ g → D g A) (cong fin p) d ≡ subst (λ k → D-fin k A) p d
  bridge-fin refl d = refl

  assoc-src-fin : ∀ a b c {A} (d : D-fin ((a + b) + c) A) →
    assoc-src (fin a) (fin b) (fin c) d
      ≡ subst (λ k → D-fin k A) (+-assoc a b c) d
  assoc-src-fin a b c d = bridge-fin (+-assoc a b c) d

-- The FULL coassoc over all grades.  The mixed-inf cases discharge by
-- D-fin-pres-prop (target is a proposition once any of r,s,t is inf); the
-- all-finite case is coassoc-fin bridged through assoc-src-fin.
-- No postulate, no hole.
coassoc : ∀ r s t {A} (d : D ((r +g s) +g t) A) →
  D-map r (δ s t) (δ r (s +g t) (assoc-src r s t d))
    ≡ δ r s (δ (r +g s) t d)
coassoc (fin a) (fin b) (fin c) {A} d =
  trans (cong (λ z → D-fin-map a (δ-fin b c) (δ-fin a (b + c) z)) (assoc-src-fin a b c d))
        (coassoc-fin a b c d)
coassoc (fin a) (fin b) inf     {A} d =
  D-fin-pres-prop a (D-fin-pres-prop b ⊤-prop) _ _
coassoc (fin a) inf     t       {A} d =
  D-fin-pres-prop a ⊤-prop _ _
coassoc inf     s       t       {A} d = refl

----------------------------------------------------------------------
-- R3 §6 — COUNIT (ε) and the two COUNIT LAWS   [BOTH DISCHARGED]
--          + the contractibility that makes the discharge VACUOUS.
--
-- The comonad counit is extract-at-zero-loss ε : D (fin 0) A → A. Since
-- D (fin 0) A = A definitionally (GradedCarrier §2), ε is the identity.
-- VarianceGate §C'' states the two unit laws the colaxator must satisfy.

ε : ∀ {A} → D (fin 0) A → A
ε x = x

-- LEFT COUNIT LAW (VarianceGate "left unit"):
--   D_{fin 0}(D_r A) reached by δ (fin 0) r ; then ε at the OUTER fin-0 layer
--   reduces to the identity coercion D (fin 0 +g r) A → D r A.
--   +g-identityˡ r = refl for both r (fin 0 +g fin n = fin n by 0+n=n;
--   fin 0 +g inf = inf), and δ-fin 0 n = subst id (D-fin-+-split 0 n) =
--   subst id refl = id, so the whole composite is the (identity) transport.
left-counit : ∀ r {A} (d : D (fin 0 +g r) A) →
  ε {D r A} (δ (fin 0) r d) ≡ subst (λ g → D g A) (+g-identityˡ r) d
left-counit (fin n) d  = refl
left-counit inf     tt = refl

-- RIGHT COUNIT LAW (VarianceGate "right unit"):
--   δ r (fin 0) : D (r +g fin 0) A → D r (D (fin 0) A) = D r A, then
--   D_r ε = D-map r (the inner ε = id) must reduce to the identity coercion
--   D (r +g fin 0) A → D r A.  For r = fin k this is the transport along
--   r +g fin 0 = r (i.e. +-identityʳ k).  We prove the composite equals that
--   transport — i.e. the right unit law holds up to the grade-unit coercion,
--   exactly as VarianceGate specifies ("D_r applied to the ≅ Id iso").
right-counit-fin : ∀ k {A} (d : D-fin (k + 0) A) →
  D-fin-map k (ε {A}) (δ-fin k 0 d) ≡ subst (λ j → D-fin j A) (+-identityʳ k) d
right-counit-fin zero    d        = refl
right-counit-fin (suc k) (t , xs) = begin
  D-fin-map (suc k) ε (δ-fin (suc k) 0 (t , xs))
    ≡⟨ cong (D-fin-map (suc k) ε) (δ-fin-suc k 0 t xs) ⟩
  (t , D-fin-map k ε (δ-fin k 0 xs))
    ≡⟨ cong (λ z → t , z) (right-counit-fin k xs) ⟩
  (t , subst (λ j → D-fin j _) (+-identityʳ k) xs)
    ≡⟨ sym (subst-Dfin-suc (+-identityʳ k) t xs) ⟩
  subst (λ j → D-fin j _) (cong suc (+-identityʳ k)) (t , xs)
    ∎
  where open ≡-Reasoning

right-counit : ∀ r {A} (d : D (r +g fin 0) A) →
  D-map r (ε {A}) (δ r (fin 0) d) ≡ subst (λ g → D g A) (+g-identityʳ r) d
right-counit (fin k) {A} d =
  trans (right-counit-fin k d) (sym (bridge-fin (+-identityʳ k) d))
right-counit inf tt = refl

-- ── The VACUITY witness (this is the actual finding) ───────────────
-- Every finite ⊤-padded carrier over ⊤ is CONTRACTIBLE: it has a centre
-- (D-fin-⊤-pt m) and everything is equal to it. This is why δ's fin/inf
-- "invention" (§2) is INVISIBLE to every law: the manufactured value is the
-- UNIQUE inhabitant, so any equation whose target is D-fin m ⊤ (or anything
-- nesting D inf … = ⊤ at the bottom) holds automatically. The comonad laws
-- do not certify that δ recovers information — they certify nothing, because
-- there is no information to recover. The "win" is vacuous by construction.
D-fin-⊤-contr : ∀ m (x : D-fin m ⊤) → x ≡ D-fin-⊤-pt m
D-fin-⊤-contr zero    tt       = refl
D-fin-⊤-contr (suc m) (tt , x) = cong (λ z → tt , z) (D-fin-⊤-contr m x)

-- Direct corollary: the fin/inf branch of δ is the constant into a
-- contractible type, so it is the UNIQUE map there — no choice was made,
-- nothing was genuinely "split". (Restates §2's diagnostic as a theorem.)
δ-fin-inf-unique : ∀ m {A} (x : D inf A) (y : D-fin m (D inf A)) →
  δ (fin m) inf {A} x ≡ y
δ-fin-inf-unique m x y = sym (D-fin-⊤-contr m y)

----------------------------------------------------------------------
-- R3 §7 — THE PARKED OBLIGATION (the only one; named precisely)
--
-- OBLIGATION (variance / content-faithfulness — UNDISCHARGEABLE on this
--             carrier BY DESIGN, parked, NOT postulated):
--
--   δ is a graded COMONAD comultiplication only in the vacuous sense above.
--   The structure that would make it a NON-vacuous comonad — a carrier whose
--   finite layers carry RECOVERABLE content (so that δ genuinely SPLITS a
--   composite witness rather than re-padding ⊤) — is exactly the carrier on
--   which δ's fin/inf case CANNOT BE DEFINED TOTAL without a postulate:
--
--       δ-content : ∀ m {A} → D inf A → D-fin-content m (D inf A)
--       -- with D-fin-content (suc n) A = Σ A (λ _ → D-fin-content n A),
--       --      D inf A = ⊤, this is ⊤ → Σ A (…), UNINHABITED for A with no
--       --      generic point. NO total K-free term. δ would NOT TYPE.
--
--   This is the comonadic image of the R1 variance obstruction
--   (VarianceGate §1): the splitting direction δ is the comonadic
--   comultiplication, and on any content-faithful carrier it must invent
--   the discarded intermediate, which it cannot do totally. The monadic
--   combine direction μ (the φ line) faces NO such obligation: μ only ever
--   DISCARDS / FUSES, never invents, so μ is total on content-faithful
--   carriers too. THIS asymmetry — δ obstructed on content, μ not — is the
--   variance finding, surviving the move to the additive ℕ∪{∞} tower.
--
--   On the present INERT carrier the obligation is discharged vacuously
--   (D-fin-⊤-contr) and so cannot be FELT; that vacuity is itself the
--   honest report. The non-vacuous version is parked here, NOT postulated.
--
-- TERMINATING CONDITION (STATE.adoc): both lines discharge their stated
-- laws on the inert carrier ⇒ condition (ii). Recommendation per (ii):
-- BEGIN the separate adjunction F_r ⊣ U_r construction to decide which
-- reading is primary on a content-faithful carrier. That construction is
-- explicitly OUT OF SCOPE for this run and is NOT attempted here.
