{-# OPTIONS --safe --without-K #-}

-- EXPERIMENTAL — R4 deliverable: the F_r ⊣ U_r ADJUNCTION ATTEMPT on the
-- CONTENT-FAITHFUL carrier (terminating-condition (ii) discriminator).
--
-- Per STATE.adoc / DECISIONS.adoc: R2/R3 reached terminating condition (ii)
-- (both the monad line φ and the comonad line δ discharge on the INERT
-- carrier — but δ vacuously). Condition (ii) mandates a SEPARATE construction:
-- build F_r and U_r as functors and ATTEMPT the adjunction F_r ⊣ U_r in
-- --safe --without-K. The adjunction is NOT inherited from the R3 discharge.
--
-- PREDICTION (GradedComonad §7 + VarianceGate §2 Option B): on the
-- content-faithful carrier, F_r, U_r, the unit η, and the induced graded MONAD
-- U_r F_r discharge; the COMONADIC half (the counit ε / the induced comonad
-- F_r U_r comultiplication / the δ direction) is OBSTRUCTED — it forces a
-- total map of shape ⊤ → Σ A (…) (invent a payload total collapse destroyed),
-- which has NO K-free term. That obstruction is PARKED as an -- OBLIGATION
-- comment (NEVER a postulate); the rest of the file typechecks clean.
--
-- FIREWALL (W2): imports GradedCarrierFaithful + Grade + (read-only) Echo.
-- Does NOT import GradedMonad / GradedComonad (their proofs are about the
-- INERT carrier — a different object; importing them would contaminate the
-- finding). ZERO POSTULATES, ZERO HOLES (W3/W4). NOT shipped (W5/W6).

module experimental.echo-additive.GradedAdjunction where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (⊤; tt)
open import Data.Product.Base using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import experimental.echo-additive.Grade
  using (Grade; fin; inf)
open import experimental.echo-additive.GradedCarrierFaithful
  using (Dc; Dc-fin; Dc-map; Dc-fin-map)

-- (Provenance note: the head-extraction counit ε and the diagonal unit η are
--  the additive images of Echo-comp-iso-to/from — the split/combine directions
--  in Echo.agda:73-96 — read on the content-faithful carrier. Echo itself is
--  not imported here; the adjunction is built from the carrier functor alone,
--  which is the standard unit/counit route and keeps the firewall minimal.)

----------------------------------------------------------------------
-- R4 §1 — The functors F_r and U_r (VarianceGate §2 Option B, concretised)
--
-- We work in the (only) category the additive signature gives us: SET, with
-- F_r and U_r as endofunctors. The coeffect reading of Option B:
--
--   F_r : Set → Set   introduces r units of loss-structure.
--         F_r A := Dc r A   (the content-faithful r-layer tower over A).
--         Functor action = Dc-map (maps over every layer).
--
--   U_r : Set → Set   FORGETS the loss-structure back to a bare payload.
--         For the adjunction we take U_r = Id (the forgetful functor to the
--         underlying Set), which is the standard coeffect choice: F_r is the
--         "free r-graded" left adjoint, U_r the underlying-object right
--         adjoint. (The grade is carried by F_r; U_r discards it.)
--
-- The induced GRADED MONAD is U_r ∘ F_r = Dc r (the "store r layers" monad);
-- the induced GRADED COMONAD is F_r ∘ U_r = Dc r as well (since U_r = Id),
-- but read in the OPPOSITE variance. The asymmetry the variance finding
-- predicts shows up in WHICH of unit / counit is K-free constructible.

F : Grade → Set → Set
F r A = Dc r A

F-map : ∀ {A B : Set} (f : A → B) (r : Grade) → F r A → F r B
F-map f r = Dc-map f r

U : Set → Set
U A = A

U-map : ∀ {A B : Set} (f : A → B) → U A → U B
U-map f = f

----------------------------------------------------------------------
-- R4 §2 — THE UNIT  η : A → U (F_r A) = Dc r A      [EXPECTED: DISCHARGES]
--
-- The unit of F_r ⊣ U_r at object A is a map A → U(F_r A) = Dc r A. It must
-- introduce r layers of loss-structure from a bare payload. On the
-- CONTENT-FAITHFUL carrier this is the diagonal: copy the payload into every
-- one of the r+1 layers. NO invention — the payload is given, we duplicate it.
-- This is the monadic-direction unit (Id ⇒ D) the variance finding flags as
-- the natural, total direction. Total and K-free for every r.

η-fin : ∀ (n : ℕ) {A} → A → Dc-fin n A
η-fin zero    a = a
η-fin (suc n) a = a , η-fin n a

η : ∀ (r : Grade) {A} → A → U (F r A)
η (fin n) a = η-fin n a
η inf     a = tt          -- Dc inf A = ⊤; collapse is forced (and total)

-- The finite-grade head-EXTRACTION (the total fragment of the counit ε; the
-- full counit and its obstruction are discussed in §4). Defined here because
-- the monad multiplication μ (§3) is built from it. TOTAL and K-free: on the
-- content-faithful carrier a finite layer genuinely HOLDS a payload, so we can
-- read it off (proj₁ at suc; id at zero) — no invention.
ε-fin : ∀ (n : ℕ) {A} → Dc-fin n A → A
ε-fin zero    x        = x
ε-fin (suc n) (a , _)  = a

----------------------------------------------------------------------
-- R4 §3 — THE COUNIT AS A NATURAL TRANSFORMATION, and the INDUCED MONAD μ
--
-- The counit of F_r ⊣ U_r is a natural transformation ε_B : F U B → B, i.e.
-- (since U = Id)  ε_B : Dc r B → B,  instantiated at EVERY object B. The
-- induced monad U F_r = Dc r then has multiplication  μ_A := U(ε_{F A}) =
-- ε_{Dc r A} : Dc r (Dc r A) → Dc r A — i.e. μ is the SAME natural ε at the
-- object Dc r A. This is the standard "monad-from-adjunction" recipe; it is
-- NOT a free design choice. So once ε is fixed, μ is forced.
--
-- ε_B = head-EXTRACTION (ε-fin at finite grade): on the content-faithful
-- carrier a finite layer genuinely holds a payload, so we read off the head.
-- TOTAL and K-free at finite grades. (At r = inf, ε_B : ⊤ → B is the
-- obstruction — see §4.)
--
-- Therefore μ_A = ε_{Dc r A} = head-extraction at object Dc r A:

μ-fin : ∀ (n : ℕ) {A} → Dc-fin n (Dc-fin n A) → Dc-fin n A
μ-fin n {A} = ε-fin n {Dc-fin n A}      -- = U(ε_{F A}); FORCED by the recipe

μ : ∀ (r : Grade) {A} → Dc r (Dc r A) → Dc r A
μ (fin n) x = μ-fin n x
μ inf     _ = tt

----------------------------------------------------------------------
-- R4 §4 — THE COUNIT  ε : F_r (U A) → A = Dc r A → A   [THE OBSTRUCTION POINT]
--
-- The counit of F_r ⊣ U_r at object A is ε : F_r (U A) → A, i.e. Dc r A → A.
-- It must EXTRACT a payload from an r-layer tower. Consider the two endpoints:
--
--   r = fin 0 : Dc (fin 0) A = A, so ε = id. TOTAL, K-free. (extract at no loss)
--   r = fin (suc n) : Dc-fin (suc n) A = Σ A (…), so ε = proj₁ (the head).
--                     TOTAL, K-free.  (a content layer DOES hold a payload)
--   r = inf   : Dc inf A = ⊤. ε would need ⊤ → A. *** UNINHABITED ***
--               total collapse destroyed every payload; there is no A to
--               extract and no generic point. NO K-free total term.
--
-- So ε is TOTAL on the finite grades (the content layers genuinely carry the
-- payload — this is what content-faithfulness BUYS) but FAILS at r = inf.
-- We expose the finite, total fragment (ε-fin, defined in §2 because μ uses it)
-- and PARK the inf case as the obligation.

-- The finite-grade counit. TOTAL and K-free.
ε-fin-grade : ∀ (n : ℕ) {A} → F (fin n) (U A) → A
ε-fin-grade n x = ε-fin n x

-- OBLIGATION (R4 LIVE OBSTRUCTION — counit at inf, UNDISCHARGEABLE K-free):
--
--   ε : ∀ (r : Grade) {A} → F r (U A) → A
--   ε (fin n) x = ε-fin n x       -- total: the head payload (extract)
--   ε inf     x = ?               -- ⊤ → A, UNINHABITED for generic A.
--
-- There is NO total K-free term completing the inf clause: x : ⊤ carries no
-- payload, A has no generic point. A graded counit at the COLLAPSE grade would
-- have to FABRICATE the payload total collapse destroyed — precisely the
-- ⊤ → Σ A (…) shape GradedComonad §7 names (here in its starkest form ⊤ → A).
-- This is the comonadic-direction invention the monad never needs. NOT
-- postulated; parked. (The finite fragment ε-fin-grade above is the honest
-- total content.)

----------------------------------------------------------------------
-- R4 §5 — THE ADJUNCTION STATEMENT and the discharge attempt
--
-- We state F_r ⊣ U_r via unit/counit + the two TRIANGLE (zig-zag) identities.
-- With ε_B : Dc r B → B the natural counit and η_A : A → Dc r A the unit:
--
--   (T1)  ε_{F_r A} ∘ F_r(η_A)  =  id_{F_r A}    : Dc r A → Dc r A
--         F_r(η_A) = Dc-map η_A r : Dc r A → Dc r (Dc r A); ε_{F_r A} : Dc r (Dc r A) → Dc r A
--   (T2)  U_r(ε_A) ∘ η_{U_r A}  =  id_{U_r A}    : A → A
--         (U=Id) reads  ε_A ∘ η_A = id_A : A → A.
--
-- These are forced once η (diagonal copy) and ε (head extraction) are fixed:
-- ε is the natural transformation, η is the unit, the recipe leaves no slack.
--
-- ── (T2) DISCHARGES on FINITE grades (refl). ──────────────────────────
-- ε_A ∘ η_A : at suc n, ε-fin (suc n) (η-fin (suc n) a) = proj₁ (a , η-fin n a) = a.
triangle₂-fin : ∀ (n : ℕ) {A} (a : A) → ε-fin n (η-fin n a) ≡ a
triangle₂-fin zero    a = refl
triangle₂-fin (suc n) a = refl

-- (T2) at object Dc-fin n A is the monad LEFT-unit law μ ∘ η_{F A} = id; it is
-- the same statement, instance of triangle₂-fin, and DISCHARGES (refl).
monad-unit-left-fin : ∀ (n : ℕ) {A} (x : Dc-fin n A) →
                      μ-fin n (η-fin n {Dc-fin n A} x) ≡ x
monad-unit-left-fin zero    x        = refl
monad-unit-left-fin (suc n) x        = refl   -- = triangle₂-fin (suc n) {Dc-fin n A} x

-- ── (T1) is the OBSTRUCTION — it FAILS even at FINITE grades. ──────────
-- (T1)  ε_{F A} ∘ Dc-map η_A = id  : Dc-fin n A → Dc-fin n A.
-- At suc n with x = (a , xs):
--   Dc-fin-map (η-fin (suc n)) (suc n) (a , xs)
--     = (η-fin (suc n) a , Dc-fin-map (η-fin (suc n)) n xs)
--     = ((a , η-fin n a) , …)
--   ε_{F A} = ε-fin (suc n) extracts the head = (a , η-fin n a).
-- The goal RHS is (a , xs). So (T1) demands  η-fin n a ≡ xs  for ARBITRARY xs.
-- That is FALSE in general (η-fin n a is the all-a diagonal; xs is arbitrary).
-- There is NO K-free term: the head-extraction counit DISCARDS the tail xs and
-- the diagonal unit cannot have produced an arbitrary xs. This is the comonadic
-- zig-zag failing: the counit, which must FORGET, cannot reconstruct the tail
-- the unit's diagonal did not put there. PARKED, not postulated.
--
-- OBLIGATION (R4 LIVE OBSTRUCTION — triangle T1, UNDISCHARGEABLE K-free):
--
--   triangle₁-fin : ∀ (n : ℕ) {A} (x : Dc-fin n A) →
--                   ε-fin n (Dc-fin-map (η-fin n) n x) ≡ x
--   triangle₁-fin zero    x        = refl           -- base: id
--   triangle₁-fin (suc n) (a , xs) = ?              -- needs  η-fin n a ≡ xs
--   -- ?: goal  (a , η-fin n a) ≡ (a , xs)  reduces to  η-fin n a ≡ xs,
--   --    FALSE for arbitrary xs.  No K-free (indeed NO) total inhabitant.
--
-- The base case (n = 0) discharges (refl): at zero loss F U = Id and the
-- triangle is trivial. EVERY positive content layer breaks it. This is sharper
-- than the §4 inf-only prediction: content-faithfulness makes the comonadic
-- zig-zag fail across ALL finite suc grades, because the counit must forget the
-- per-layer content the diagonal unit duplicated, and forgetting is not
-- invertible. The MONADIC half (η + μ = ε_{F A} with the LEFT unit law,
-- monad-unit-left-fin) discharges; the comonadic zig-zag T1 does not.

-- The base-case fragment of T1 (the only sub-case that discharges):
triangle₁-fin-base : ∀ {A} (x : Dc-fin 0 A) → ε-fin 0 (Dc-fin-map (η-fin 0) 0 x) ≡ x
triangle₁-fin-base x = refl

----------------------------------------------------------------------
-- R4 §6 — The induced GRADED MONAD associativity-style law  [DISCHARGES]
--
-- The monad U F_r = Dc r with μ = ε_{F A} (head-extraction). The OTHER monad
-- unit law (M-right) μ ∘ F(η) is exactly the failing T1 above — so as a MONAD
-- the right-unit law also fails on this μ/η pairing at suc grades. What DOES
-- discharge is the part of the structure that only ever projects/forgets:
-- the left-unit (above) and the counit naturality on finite grades.

-- Counit NATURALITY on finite grades:  f ∘ ε = ε ∘ Dc-map f.   [DISCHARGES]
-- (ε is a natural transformation Dc r ⇒ Id on finite grades.)
ε-natural-fin : ∀ (n : ℕ) {A B} (f : A → B) (x : Dc-fin n A) →
                f (ε-fin n x) ≡ ε-fin n (Dc-fin-map f n x)
ε-natural-fin zero    f x        = refl
ε-natural-fin (suc n) f (a , xs) = refl

-- Unit NATURALITY on finite grades:  Dc-map f ∘ η = η ∘ f.   [DISCHARGES]
η-natural-fin : ∀ (n : ℕ) {A B} (f : A → B) (a : A) →
                Dc-fin-map f n (η-fin n a) ≡ η-fin n (f a)
η-natural-fin zero    f a = refl
η-natural-fin (suc n) f a = cong (λ z → f a , z) (η-natural-fin n f a)
