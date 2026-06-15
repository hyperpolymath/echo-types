{-# OPTIONS --safe --without-K #-}

-- EXPERIMENTAL — R2 deliverable (SHARED CARRIER).
-- Carrier D : Grade → Set → Set for the echo-additive composition lines,
-- PLUS the degrade reindexing action over the loss order extended to all of
-- Grade, PLUS the carrier-level helpers the R3 laws consume (the fin 0 ≅ Id
-- coercion, the D inf ≅ ⊤ collapse, the D-functor map, the ⊤-tower point).
--
-- Imported by BOTH GradedMonad.agda (primary, φ) and GradedComonad.agda
-- (secondary, δ). The two lines MUST NOT import each other; this module is
-- their only shared dependency beyond Grade / Echo / stdlib (firewall W2).
--
-- INVARIANTS (per STATE.adoc / DECISIONS.adoc D-2026-06-14-R1):
--   --safe --without-K, zero postulates, no holes, no escape pragmas (W3/W4).
--   No shipped module edited. Not imported by any shipped module (W5).
--   NOT merged to main; experimental working-tree only (W6).

module experimental.echo-additive.GradedCarrier where

open import Data.Nat.Base using (ℕ; zero; suc; _+_; _≤_; z≤n; s≤s)
open import Data.Unit.Base using (⊤; tt)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import experimental.echo-additive.Grade
  using (Grade; fin; inf; _+g_)

----------------------------------------------------------------------
-- R2 §1 — The carrier D : Grade → Set → Set
--
-- Required endpoints (prompt + VarianceGate):
--   D (fin 0)       A = Id   = A            (Old.keep / no loss)
--   D inf           A = ⊤                    (Old.forget / total collapse)
--   D (fin (suc n)) A = ?                    (THE R2 QUESTION)
--
-- ── Grounding in Echo / Echo-comp-iso ──────────────────────────────
-- Echo-comp-iso (Echo.agda:73-96) is the bidirectional law
--   Echo (g∘f) y  ≅  Σ B (λ b → Echo f b × (g b ≡ y)).
-- The COMBINING ("from") direction Echo-comp-iso-from FUSES an accumulated
-- two-layer witness into one — this is the monadic μ the primary line φ
-- builds on. The SPLITTING ("to") direction Echo-comp-iso-to SPLITS one
-- layer into two — this is the comonadic δ the secondary line builds on.
-- The nested RHS `Σ B (Echo f b × …)` is the shape of D r (D s A): an
-- outer layer (the Σ-over-intermediate-base carrying a residue equation)
-- wrapping an inner Echo. ONE additive grade-unit = ONE residue layer.
--
-- ── THE R2 DESIGN CHOICE (the load-bearing honesty point) ──────────
-- A residue layer of `Echo f b × (g b ≡ y)` needs a codomain map (`g`)
-- and a base point (`y`) to pin a NON-TRIVIAL equation. The additive
-- carrier has signature `Grade → Set → Set`: it receives a payload `A`
-- and NOTHING ELSE — no codomain map, no base point. The only generic
-- map available to instantiate Echo-comp-iso-{to,from} is `id`, and at
-- `id`/`id` both the inner `Echo id b` (singleton at b) and the residue
-- `id b ≡ y` (singleton at y) are CONTRACTIBLE. Hence every residue
-- equation a finite additive layer could carry is `refl`-only, and the
-- only K-free finite layer the carrier supports is PAYLOAD-INDEPENDENT —
-- a `⊤` factor carrying the trivial residue. This is what makes the
-- additive composition law DEFINITIONAL (D-fin-+-split below) and is the
-- same fact that makes the additive grade STRUCTURALLY INERT:
-- D (fin n) A ≅ A for every finite n. The grade counts layers; the layers
-- carry no recoverable content because there is no codomain to recover
-- against. This inertness is the carrier-side shadow of the R1 variance
-- finding, and it is what both lines' law-discharge tests expose.
--
-- The rejected alternative (recorded for honesty): a content-bearing
-- finite layer `D-fin (suc n) A = Σ A (λ _ → D-fin n A)` — a real copy of
-- A per layer — gives A^((m+1)(n+1)) under nesting, which does NOT fuse
-- with addition's A^(n+m+1). The outer Σ would be over A vs over D-fin n A,
-- so the additive split below would FAIL definitionally. Only the ⊤-padded
-- tower fuses; making φ constructible via Echo-comp-iso-from forces it.

-- Finite-grade carrier: n payload-independent residue layers over A.
-- The trivial (refl-only) residue layer is written as a `⊤ ×` factor on
-- the LEFT, so the additive split  D-fin (m + n) A ≡ D-fin m (D-fin n A)
-- is DEFINITIONAL.  The δ line reads this LEFT-to-RIGHT (split, the
-- additive image of Echo-comp-iso-TO); the φ line reads its `sym`
-- RIGHT-to-LEFT (combine, the additive image of Echo-comp-iso-FROM).
D-fin : ℕ → Set → Set
D-fin zero    A = A
D-fin (suc n) A = ⊤ × D-fin n A

-- Full carrier.
D : Grade → Set → Set
D (fin n) A = D-fin n A
D inf     A = ⊤

----------------------------------------------------------------------
-- R2 §2 — Endpoint sanity (all refl)

D-fin0-Id : ∀ {A} → D (fin 0) A ≡ A
D-fin0-Id = refl

D-inf-Top : ∀ {A} → D inf A ≡ ⊤
D-inf-Top = refl

-- The fin 0 ≅ Id coercion as named functions (definitional, so both refl).
-- The R3 unit laws state "φ (fin 0) r = the D (fin 0)(−) ≅ Id coercion";
-- exposing the coercion by name lets that law be read against this carrier.
D-fin0-coe : ∀ {A} → D (fin 0) A → A
D-fin0-coe x = x

D-fin0-coe-inv : ∀ {A} → A → D (fin 0) A
D-fin0-coe-inv x = x

-- The D inf ≅ ⊤ collapse, named for the same reason.
D-inf-collapse : ∀ {A} → D inf A → ⊤
D-inf-collapse _ = tt

----------------------------------------------------------------------
-- R2 §3 — Additive composition shape on FINITE grades
--
-- The pivotal R2 lemma: on finite grades the additive carrier splits
-- DEFINITIONALLY along +.  D-fin (m + n) A  ≡  D-fin m (D-fin n A)  by a
-- chain of refl, proved by induction on m. This is the carrier-level
-- statement BOTH lines build their composition maps on top of, and is
-- the additive shadow of Echo-comp-iso.
--
-- The δ (secondary) line reads it LEFT-to-RIGHT (split: D (m+n) A →
-- D m (D n A)); the φ (primary) line reads `sym` of it RIGHT-to-LEFT
-- (combine: D m (D n A) → D (m+n) A). Both are transports along this same
-- path — which is itself the symptom the variance finding predicts.

D-fin-+-split : ∀ m n {A} → D-fin (m + n) A ≡ D-fin m (D-fin n A)
D-fin-+-split zero    n     = refl
D-fin-+-split (suc m) n {A} = cong (λ T → ⊤ × T) (D-fin-+-split m n)

----------------------------------------------------------------------
-- R2 §4 — The carrier functor (D-fin-map / D-map)
--
-- Needed to state D_r(φ_{s,t}) in the φ pentagon and D_r(δ_{s,t}) in the
-- δ coassociativity. On the ⊤-padded carrier this is map-on-innermost-
-- payload, leaving every trivial ⊤ layer fixed. Function-first argument
-- order (matching the primary φ line's local convention). Hosted here so
-- the carrier is self-describing; the line files keep their own local
-- copies for their reasoning, but this is the canonical shared form.

D-fin-map : ∀ {A B : Set} (f : A → B) (n : ℕ) → D-fin n A → D-fin n B
D-fin-map f zero    x        = f x
D-fin-map f (suc n) (tt , y) = tt , D-fin-map f n y

D-map : ∀ {A B : Set} (f : A → B) (r : Grade) → D r A → D r B
D-map f (fin n) x = D-fin-map f n x
D-map f inf     _ = tt

-- Functor identity law (witness that D-map is a genuine functorial action).
D-fin-map-id : ∀ {A : Set} (n : ℕ) (x : D-fin n A) →
               D-fin-map (λ a → a) n x ≡ x
D-fin-map-id zero    x        = refl
D-fin-map-id (suc n) (tt , y) = cong (λ z → tt , z) (D-fin-map-id n y)

----------------------------------------------------------------------
-- R2 §5 — The ⊤-tower point
--
-- Canonical inhabitant of any finite ⊤-padded carrier over ⊤. The δ line
-- needs this to MANUFACTURE the m intermediate layers that total collapse
-- (inf) destroyed when splitting D inf A = ⊤ into D (fin m) (D inf A) =
-- D-fin m ⊤. Its inhabitedness is exactly carrier inertness — the
-- carrier-side shadow of the variance finding on the δ side.

D-fin-⊤-pt : ∀ m → D-fin m ⊤
D-fin-⊤-pt zero    = tt
D-fin-⊤-pt (suc m) = tt , D-fin-⊤-pt m

----------------------------------------------------------------------
-- R2 §6 — The loss order on all of Grade, and the degrade reindexing
--          action over it (fin 0 = Id unit; inf = Top collapse)
--
-- The loss order ⊑g extends ℕ's ≤ with inf as the top (most lossy):
--   fin m ⊑g fin n   iff   m ≤ n        (losing MORE layers is higher)
--   g     ⊑g inf                         (total collapse is the cap)
-- This is the same order whose 3-point restriction {fin 0, fin 1, inf}
-- is the shipped EchoGraded `keep ≤g residue ≤g forget` action (read-only;
-- mirrored here, NOT edited). fin 0 (no loss) is the bottom; inf the top.

infix 4 _⊑g_
data _⊑g_ : Grade → Grade → Set where
  fin⊑fin : ∀ {m n} → m ≤ n → fin m ⊑g fin n
  ⊑inf    : ∀ {g}           → g     ⊑g inf

-- degrade: reindex a carrier value UP the loss order (forgetting structure).
-- On the inert ⊤-tower, degrading fin m → fin n (m ≤ n) re-pads to n layers;
-- degrading anything → inf collapses to tt. Total and K-free.
--
-- The finite case recurses on the ≤ proof: the z≤n base re-pads a bare
-- payload to n trivial layers (D-fin0-pad); the s≤s step peels one ⊤ on
-- each side.

-- pad a bare payload (D-fin 0 A = A) up to n trivial ⊤ layers.
D-fin0-pad : ∀ {A} n → A → D-fin n A
D-fin0-pad zero    x = x
D-fin0-pad (suc n) x = tt , D-fin0-pad n x

degrade-fin : ∀ {A} {m n} → m ≤ n → D-fin m A → D-fin n A
degrade-fin {n = n} z≤n     x        = D-fin0-pad n x
degrade-fin         (s≤s p) (tt , y) = tt , degrade-fin p y

degrade : ∀ {A} {r s} → r ⊑g s → D r A → D s A
degrade (fin⊑fin p) x = degrade-fin p x
degrade ⊑inf        _ = tt

-- degrade at a reflexive finite step is the identity (the fin 0 unit law in
-- carrier form: degrading along m ≤ m changes nothing). Witnessed via the
-- ≤-reflexive proof built structurally.
≤-refl-nat : ∀ n → n ≤ n
≤-refl-nat zero    = z≤n
≤-refl-nat (suc n) = s≤s (≤-refl-nat n)

degrade-fin-refl : ∀ {A} n (x : D-fin n A) →
                   degrade-fin (≤-refl-nat n) x ≡ x
degrade-fin-refl zero    x        = refl
degrade-fin-refl (suc n) (tt , y) = cong (λ z → tt , z) (degrade-fin-refl n y)

-- degrade into inf is the total collapse (the Old.forget endpoint, in
-- carrier form): every value maps to the unique ⊤ inhabitant.
degrade-to-inf : ∀ {A} {r} (p : r ⊑g inf) (x : D r A) → degrade p x ≡ tt
degrade-to-inf ⊑inf x = refl
