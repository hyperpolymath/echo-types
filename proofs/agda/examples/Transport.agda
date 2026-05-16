{-# OPTIONS --safe --without-K #-}

------------------------------------------------------------------------
-- Gate #3 candidate example: transport-echo (block averaging as
-- structured loss on a discrete field).
--
-- Bridge axis decision (graded, EchoGraded).  Block averaging is
-- read against the GRADED axis, not the linear/affine one.  The
-- linear axis (EchoLinear) is a two-element resource-discipline
-- chain `linear ⊑ affine` carrying exactly one strict weakening
-- step into a trivial residue; it can say "averaging loses data"
-- but has no multi-level lattice in which to express the *iterated*
-- structure that makes block averaging interesting.  The graded
-- axis (EchoGraded) is a lattice `keep ⊑ residue ⊑ forget` whose
-- load-bearing content is `degrade-comp` / `degrade-compose`:
-- successive coarsenings compose and different factorings of a
-- coarsening through intermediate resolutions agree.  Block
-- averaging is exactly an iterated coarsening — averaging blocks of
-- blocks is a coarser average — so its echo is the
-- compositional-degradation story the graded axis already names.
-- Hence the graded axis fits cleanly; no new axis is introduced.
--
-- Carrier note.  `Field n` is `Vec ℚ n`, a first-order carrier, so
-- equality of fields is structural.  A `Fin n → ℚ` carrier was
-- tried first but makes every `≡`-between-fields claim an equality
-- of functions, which needs function extensionality (unavailable
-- under `--safe` without a postulate); the Vec carrier sidesteps
-- that exactly as the other Gate-3 examples use data codomains.
------------------------------------------------------------------------

module examples.Transport where

open import Data.Nat.Base using (ℕ; zero; suc) renaming (_*_ to _*ℕ_)
open import Data.Nat.Properties using (*-comm)
import Data.Nat.Coprimality as Cop
open import Data.Integer.Base using (ℤ; +_)
open import Data.Vec.Base
  using ( Vec; []; _∷_; _++_; map; concat; group; zipWith; _∷ʳ_
        ; reverse; replicate )
  renaming (cast to vcast)
open import Data.Vec.Properties
  using ( subst-is-cast; map-∷ʳ; map-reverse; map-replicate
        ; reverse-∷; zipWith-replicate )
open import Function.Base using (_∘_)
open import Data.Rational.Base
  using (ℚ; mkℚ; 0ℚ; 1ℚ; _+_; _*_; _-_; -_; _/_; 1/_)
import Data.Rational.Properties as ℚP
open import Data.Product.Base using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)
open import Relation.Nullary using (¬_)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- Rung 1 — definitions.
--
-- A discrete field of length n is a ℚ-valued vector.  `avg`
-- averages each contiguous block of (suc k) entries; the `suc k`
-- in the signature guards against an empty block (k = 0 still
-- gives blocks of size 1, i.e. avg = identity-shaped).

Field : ℕ → Set
Field n = Vec ℚ n

-- Sum over a field (kept local to this module, as instructed;
-- `Data.Vec.Base.sum` is ℕ-only so cannot be reused here).
sum : ∀ {n} → Field n → ℚ
sum []       = 0ℚ
sum (x ∷ xs) = x + sum xs

-- (suc k) as a rational, built directly with `mkℚ` (no `normalize`,
-- so it stays reducible for abstract k), and its reciprocal as the
-- field inverse `1/ (sk k)` — making the cancellation law exactly
-- stdlib's `*-inverseʳ`.
sk : ℕ → ℚ
sk k = mkℚ (+ suc k) 0 (Cop.sym (Cop.1-coprimeTo (suc k)))

recip : ℕ → ℚ
recip k = 1/ (sk k)

-- Cancellation: (suc k) · (1 / (suc k)) = 1.
mul-recip : ∀ k → sk k * recip k ≡ 1ℚ
mul-recip k = ℚP.*-inverseʳ (sk k)

-- Average of one block of size (suc k).
blockAvg : ∀ {k} → Vec ℚ (suc k) → ℚ
blockAvg {k} b = sum b * recip k

-- `group n (suc k)` reshapes a length-(n * suc k) vector into n
-- contiguous blocks of size (suc k) (and records the defining
-- equation `xs ≡ concat xss`); we cast across `*-comm` to accept
-- the spec'd `Field (suc k * n)`.
avg : ∀ {k n} → Field (suc k *ℕ n) → Field n
avg {k} {n} f =
  map (blockAvg {k}) (proj₁ (group n (suc k) (vcast (*-comm (suc k) n) f)))

------------------------------------------------------------------------
-- Rung 2 — avg-not-injective.
--
-- Witnesses at k = 1, n = 1 (blocks of size 2, one output entry):
--   f₁ = [0, 2],  f₂ = [1, 1].   Both blocks average to 1.

f₁ : Field 2
f₁ = 0ℚ ∷ (+ 2) / 1 ∷ []

f₂ : Field 2
f₂ = 1ℚ ∷ 1ℚ ∷ []

-- Distinct: the head entries 0ℚ and 1ℚ differ, refuted by pushing
-- through the numerator to a ℕ clash (no decidable ℚ equality used).
f₁≢f₂ : ¬ (f₁ ≡ f₂)
f₁≢f₂ eq = 0≢1 (cong ℤ.∣_∣ (cong ℚ.↥_ (cong hd eq)))
  where
    import Data.Rational.Base as ℚ
    import Data.Integer.Base  as ℤ
    hd : Field 2 → ℚ
    hd (x ∷ _) = x
    0≢1 : (0 ≡ 1) → ⊥
    0≢1 ()

-- Collision: both fields average (blockwise) to the same field.
avg-collide : avg {1} {1} f₁ ≡ avg {1} {1} f₂
avg-collide = refl

avg-not-injective :
  Σ[ g₁ ∈ Field 2 ] Σ[ g₂ ∈ Field 2 ]
    (¬ (g₁ ≡ g₂) × avg {1} {1} g₁ ≡ avg {1} {1} g₂)
avg-not-injective = f₁ , f₂ , f₁≢f₂ , avg-collide

------------------------------------------------------------------------
-- Rung 3 — avg-preserves-sum.
--
-- The total mass is conserved up to the block factor:
--   sum f ≡ (suc k) · sum (avg f).

-- sum is a monoid map for vector concatenation.
sum-++ : ∀ {m n} (xs : Vec ℚ m) (ys : Vec ℚ n) →
         sum (xs ++ ys) ≡ sum xs + sum ys
sum-++ []       ys = sym (ℚP.+-identityˡ (sum ys))
sum-++ (x ∷ xs) ys =
  trans (cong (λ z → x + z) (sum-++ xs ys)) (sym (ℚP.+-assoc x (sum xs) (sum ys)))

-- Summing a flattened vector = summing the per-block sums.
sum-concat : ∀ {m n} (xss : Vec (Vec ℚ m) n) →
             sum (concat xss) ≡ sum (map sum xss)
sum-concat []         = refl
sum-concat (xs ∷ xss) =
  trans (sum-++ xs (concat xss)) (cong (λ z → sum xs + z) (sum-concat xss))

-- `sum` is invariant under the length-relabelling `subst`/`cast`.
sum-subst : ∀ {m n} (eq : m ≡ n) (xs : Vec ℚ m) →
            sum (subst (Vec ℚ) eq xs) ≡ sum xs
sum-subst refl xs = refl

sum-vcast : ∀ {m n} (eq : m ≡ n) (xs : Vec ℚ m) →
            sum (vcast eq xs) ≡ sum xs
sum-vcast eq xs =
  trans (cong sum (sym (subst-is-cast eq xs))) (sum-subst eq xs)

-- The block-average scalar factors out of a sum of block averages.
sum-map-blockAvg : ∀ k {n} (bs : Vec (Vec ℚ (suc k)) n) →
  sum (map (blockAvg {k}) bs) ≡ recip k * sum (map sum bs)
sum-map-blockAvg k []       = sym (ℚP.*-zeroʳ (recip k))
sum-map-blockAvg k (b ∷ bs) =
  trans
    (cong₂ _+_ (ℚP.*-comm (sum b) (recip k)) (sum-map-blockAvg k bs))
    (sym (ℚP.*-distribˡ-+ (recip k) (sum b) (sum (map sum bs))))

avg-preserves-sum : ∀ {k n} (f : Field (suc k *ℕ n)) →
  sum f ≡ sk k * sum (avg {k} {n} f)
avg-preserves-sum {k} {n} f = begin
  sum f
    ≡⟨ sym (sum-vcast (*-comm (suc k) n) f) ⟩
  sum (vcast (*-comm (suc k) n) f)
    ≡⟨ cong sum (proj₂ G) ⟩
  sum (concat (proj₁ G))
    ≡⟨ sum-concat (proj₁ G) ⟩
  sum (map sum (proj₁ G))
    ≡⟨ sym (ℚP.*-identityˡ _) ⟩
  1ℚ * sum (map sum (proj₁ G))
    ≡⟨ cong (_* sum (map sum (proj₁ G))) (sym (mul-recip k)) ⟩
  (sk k * recip k) * sum (map sum (proj₁ G))
    ≡⟨ ℚP.*-assoc (sk k) (recip k) (sum (map sum (proj₁ G))) ⟩
  sk k * (recip k * sum (map sum (proj₁ G)))
    ≡⟨ cong (sk k *_) (sym (sum-map-blockAvg k (proj₁ G))) ⟩
  sk k * sum (map (blockAvg {k}) (proj₁ G))
    ∎
  where
    open ≡-Reasoning
    G = group n (suc k) (vcast (*-comm (suc k) n) f)

------------------------------------------------------------------------
-- Rung 4 — instance, not new axis.
--
-- The chosen bridge axis is the graded one.  Its echo-indexed
-- family is the base `Echo` of module `Echo`: in `EchoGraded`,
-- `GEcho keep = Echo collapse tt`, i.e. the keep-grade IS the base
-- Echo of the loss map.  The transport-echo step here is that same
-- base Echo with the loss map taken to be `avg`.
--
-- Scope note (honest, per the lane rules).  `EchoGraded.degrade`
-- is *not* a loss-map-parametric combinator: its signature
-- `∀ {g1 g2} → g1 ≤g g2 → GEcho g1 → GEcho g2` hard-wires the
-- `collapse`/`EchoR ⊤ TrivialCert` instance.  So `avg` is not a
-- value of `degrade`'s type; what it instantiates is the *base
-- Echo the graded axis is built on*.  That instantiation needs no
-- extra property of `avg` (no idempotence, no section) — the
-- agreement below is a definitional equality.  No bridge axis was
-- weakened or introduced.

open import Echo using (Echo)
import EchoGraded            -- chosen bridge axis (graded); see header

EchoStep : ∀ {k n} → Field n → Set
EchoStep {k} {n} y = Σ[ x ∈ Field (suc k *ℕ n) ] avg {k} {n} x ≡ y

echoStep-is-Echo : ∀ {k n} (y : Field n) →
  EchoStep {k} {n} y ≡ Echo (avg {k} {n}) y
echoStep-is-Echo y = refl

------------------------------------------------------------------------
-- Rung 5 — step-bijective.  STOP — the rung is false as specified.
--
-- `step` is one explicit-Euler diffusion step with periodic boundary
-- conditions and λ = ¼:
--
--   step f i = f i + ¼ · ( f(i⊖1) − 2·f i + f(i⊕1) ).
--
-- It is *not* an `Inverse`, and the documented downgrade (trivial
-- kernel, `step f ≡ const 0 → f ≡ const 0`) is *also false* for the
-- specified operator: the periodic explicit-Euler step is the
-- circulant `I + ¼·L`, whose eigenvalues are ½(1 + cos θ); at the
-- Nyquist mode (θ = π, present whenever n is even) the eigenvalue
-- is 0, so the operator is singular and its kernel is non-trivial.
-- The concrete refutation below at n = 2 (the alternating vector
-- [1, −1] is killed by `step`) is a compiled disproof of both the
-- Inverse claim and its downgrade.  No decidable ℚ equality is
-- involved; the obstruction is mathematical, not a missing lemma.
-- Per the lane discipline the build stops at this rung; Rung 6
-- (which composes `step`) is not attempted.

¼ : ℚ
¼ = (+ 1) / 4

2ℚ : ℚ
2ℚ = (+ 2) / 1

-- Cyclic rotations realise the periodic boundary.
rotL : ∀ {n} → Vec ℚ n → Vec ℚ n
rotL []       = []
rotL (x ∷ xs) = xs ∷ʳ x

rotR : ∀ {n} → Vec ℚ n → Vec ℚ n
rotR xs = reverse (rotL (reverse xs))

step : ∀ {n} → Field n → Field n
step f =
  zipWith _+_ f
    (map (λ d → ¼ * d)
      (zipWith _+_
        (zipWith _-_ (rotR f) (map (λ c → 2ℚ * c) f))
        (rotL f)))

-- Nyquist witness at n = 2: [1, −1] ≠ 0 but step [1, −1] = 0.
ker : Field 2
ker = 1ℚ ∷ - 1ℚ ∷ []

step-kills-ker : step ker ≡ 0ℚ ∷ 0ℚ ∷ []
step-kills-ker = refl

ker≢0 : ¬ (ker ≡ 0ℚ ∷ 0ℚ ∷ [])
ker≢0 eq = 1≢0 (cong ℤ.∣_∣ (cong ℚ.↥_ (cong hd eq)))
  where
    import Data.Rational.Base as ℚ
    import Data.Integer.Base  as ℤ
    hd : Field 2 → ℚ
    hd (x ∷ _) = x
    1≢0 : (1 ≡ 0) → ⊥
    1≢0 ()

-- Rung 5 disproved: step has a non-trivial kernel, so it is neither
-- an Inverse nor does it have the (downgraded) trivial kernel.
step-kernel-nontrivial :
  Σ[ f ∈ Field 2 ] (¬ (f ≡ 0ℚ ∷ 0ℚ ∷ []) × step f ≡ 0ℚ ∷ 0ℚ ∷ [])
step-kernel-nontrivial = ker , ker≢0 , step-kills-ker

------------------------------------------------------------------------
-- Rung 5a — name the kernel mode.
--
-- The disproof above is no longer a stopping point: the kernel mode
-- is itself the content.  `nyquist n` is the alternating vector
-- [1, −1, 1, −1, …] of length 2·n — the eigenvector of the periodic
-- explicit-Euler step at eigenvalue 0.  It is built as n copies of
-- the 2-block [1, −1] (so the alternation is structural), then cast
-- to the spec'd length `2 * n`.

blk : Vec ℚ 2
blk = 1ℚ ∷ - 1ℚ ∷ []

nyquist : (n : ℕ) → Vec ℚ (2 *ℕ n)
nyquist n = vcast (*-comm n 2) (concat (replicate n blk))

-- Concrete instances land by computation (the existing n = 2 disproof
-- is exactly `nyquist-in-step-kernel-1`'s content one size up).
nyquist-in-step-kernel-1 : step (nyquist 1) ≡ replicate (2 *ℕ 1) 0ℚ
nyquist-in-step-kernel-1 = refl

nyquist-in-step-kernel-2 : step (nyquist 2) ≡ replicate (2 *ℕ 2) 0ℚ
nyquist-in-step-kernel-2 = refl

-- Factored general case (reported, not postulated).  The headline
--
--   nyquist-in-step-kernel : ∀ n →
--     step (nyquist n) ≡ replicate (2 * n) 0ℚ
--
-- does not land here.  It factors into the single Vec lemma
--
--   rotL (nyquist n) ≡ map -_ (nyquist n)   (and the same for rotR)
--
-- after which `stepKills` (below, proved general) closes it.  That
-- rotation-invariance of the alternating vector through stdlib's
-- `reverse`/`_∷ʳ_`-based `rotL`/`rotR`, composed with the
-- `vcast ∘ concat ∘ replicate` builder, needs a Vec-rotation lemma
-- library not in scope; the lane forbids postulating it, so the
-- general case is delivered only at n = 1 and n = 2 above.  The
-- *homogeneity* infrastructure that the general case would also use
-- IS proved generally (see `step-homog`), and is what makes Rung 5b
-- land at the fixed even size below.

------------------------------------------------------------------------
-- Rung 5b — kernel characterisation (downgrade taken).
--
-- The full span `step f ≡ 0 → f ≡ c · nyquist` at n = 4 is a
-- symbolic 4×4 linear solve over ℚ (well past the ~150-line / type-
-- fighting threshold the spec flags).  We take the ALLOWED DOWNGRADE
-- to the containment half: every scalar multiple of the Nyquist mode
-- is in the kernel.  It is delivered at the rung's fixed even size
-- (n = 2, i.e. Field 4 — the same size Rung 6 uses).  The `∀ n`
-- form reduces, via the *general* `step-homog` proved here, to the
-- factored general `nyquist-in-step-kernel` above (same blocker as
-- 5a); only that one Vec-rotation lemma is missing.  No third
-- downgrade is invented — this is the sanctioned containment, at
-- the rung size.

-- step is ℚ-homogeneous: it commutes with scalar multiplication.
-- This is genuine general linearity content, not a size hack.

-- scalar pushes through the two ℚ-affine pieces of `step`
*-pushˡ-+ : ∀ c x y → c * (x + y) ≡ c * x + c * y
*-pushˡ-+ = ℚP.*-distribˡ-+

*-pushˡ-- : ∀ c x y → c * (x - y) ≡ c * x - c * y
*-pushˡ-- c x y =
  trans (ℚP.*-distribˡ-+ c x (- y))
        (cong (λ z → c * x + z) (sym (ℚP.neg-distribʳ-* c y)))

*-swap : ∀ c k x → c * (k * x) ≡ k * (c * x)
*-swap c k x =
  trans (sym (ℚP.*-assoc c k x))
        (trans (cong (_* x) (ℚP.*-comm c k)) (ℚP.*-assoc k c x))

-- map-(c*) commutes with each combinator used by `step`.
scale-+ : ∀ {m} c (xs ys : Vec ℚ m) →
  map (c *_) (zipWith _+_ xs ys) ≡ zipWith _+_ (map (c *_) xs) (map (c *_) ys)
scale-+ c []       []       = refl
scale-+ c (x ∷ xs) (y ∷ ys) =
  cong₂ _∷_ (*-pushˡ-+ c x y) (scale-+ c xs ys)

scale-- : ∀ {m} c (xs ys : Vec ℚ m) →
  map (c *_) (zipWith _-_ xs ys) ≡ zipWith _-_ (map (c *_) xs) (map (c *_) ys)
scale-- c []       []       = refl
scale-- c (x ∷ xs) (y ∷ ys) =
  cong₂ _∷_ (*-pushˡ-- c x y) (scale-- c xs ys)

scale-mul : ∀ {m} c k (v : Vec ℚ m) →
  map (c *_) (map (k *_) v) ≡ map (k *_) (map (c *_) v)
scale-mul c k []       = refl
scale-mul c k (x ∷ xs) =
  cong₂ _∷_ (*-swap c k x) (scale-mul c k xs)

scale-rotL : ∀ {m} c (v : Vec ℚ m) →
  map (c *_) (rotL v) ≡ rotL (map (c *_) v)
scale-rotL c []       = refl
scale-rotL c (x ∷ xs) = map-∷ʳ (c *_) x xs

scale-rotR : ∀ {m} c (v : Vec ℚ m) →
  map (c *_) (rotR v) ≡ rotR (map (c *_) v)
scale-rotR c v = begin
  map (c *_) (reverse (rotL (reverse v)))
    ≡⟨ map-reverse (c *_) (rotL (reverse v)) ⟩
  reverse (map (c *_) (rotL (reverse v)))
    ≡⟨ cong reverse (scale-rotL c (reverse v)) ⟩
  reverse (rotL (map (c *_) (reverse v)))
    ≡⟨ cong (reverse ∘ rotL) (map-reverse (c *_) v) ⟩
  reverse (rotL (reverse (map (c *_) v)))
    ∎
  where open ≡-Reasoning; open import Function.Base using (_∘_)

step-homog : ∀ {m} c (v : Vec ℚ m) →
  step (map (c *_) v) ≡ map (c *_) (step v)
step-homog c v = begin
  step (map (c *_) v)
    ≡⟨⟩
  zipWith _+_ (map (c *_) v)
    (map (λ d → ¼ * d)
      (zipWith _+_
        (zipWith _-_ (rotR (map (c *_) v)) (map (λ e → 2ℚ * e) (map (c *_) v)))
        (rotL (map (c *_) v))))
    ≡⟨ cong (λ z → zipWith _+_ (map (c *_) v)
                     (map (λ d → ¼ * d)
                       (zipWith _+_
                         (zipWith _-_ z (map (λ e → 2ℚ * e) (map (c *_) v)))
                         (rotL (map (c *_) v)))))
         (sym (scale-rotR c v)) ⟩
  zipWith _+_ (map (c *_) v)
    (map (λ d → ¼ * d)
      (zipWith _+_
        (zipWith _-_ (map (c *_) (rotR v)) (map (λ e → 2ℚ * e) (map (c *_) v)))
        (rotL (map (c *_) v))))
    ≡⟨ cong (λ z → zipWith _+_ (map (c *_) v)
                     (map (λ d → ¼ * d)
                       (zipWith _+_
                         (zipWith _-_ (map (c *_) (rotR v)) z)
                         (rotL (map (c *_) v)))))
         (sym (scale-mul c 2ℚ v)) ⟩
  zipWith _+_ (map (c *_) v)
    (map (λ d → ¼ * d)
      (zipWith _+_
        (zipWith _-_ (map (c *_) (rotR v)) (map (c *_) (map (λ e → 2ℚ * e) v)))
        (rotL (map (c *_) v))))
    ≡⟨ cong (λ z → zipWith _+_ (map (c *_) v)
                     (map (λ d → ¼ * d)
                       (zipWith _+_
                         (zipWith _-_ (map (c *_) (rotR v)) (map (c *_) (map (λ e → 2ℚ * e) v)))
                         z)))
         (sym (scale-rotL c v)) ⟩
  zipWith _+_ (map (c *_) v)
    (map (λ d → ¼ * d)
      (zipWith _+_
        (zipWith _-_ (map (c *_) (rotR v)) (map (c *_) (map (λ e → 2ℚ * e) v)))
        (map (c *_) (rotL v))))
    ≡⟨ cong (λ z → zipWith _+_ (map (c *_) v)
                     (map (λ d → ¼ * d) (zipWith _+_ z (map (c *_) (rotL v)))))
         (sym (scale-- c (rotR v) (map (λ e → 2ℚ * e) v))) ⟩
  zipWith _+_ (map (c *_) v)
    (map (λ d → ¼ * d)
      (zipWith _+_
        (map (c *_) (zipWith _-_ (rotR v) (map (λ e → 2ℚ * e) v)))
        (map (c *_) (rotL v))))
    ≡⟨ cong (λ z → zipWith _+_ (map (c *_) v) (map (λ d → ¼ * d) z))
         (sym (scale-+ c (zipWith _-_ (rotR v) (map (λ e → 2ℚ * e) v)) (rotL v))) ⟩
  zipWith _+_ (map (c *_) v)
    (map (λ d → ¼ * d)
      (map (c *_)
        (zipWith _+_ (zipWith _-_ (rotR v) (map (λ e → 2ℚ * e) v)) (rotL v))))
    ≡⟨ cong (λ z → zipWith _+_ (map (c *_) v) z)
         (sym (scale-mul c ¼
                 (zipWith _+_ (zipWith _-_ (rotR v) (map (λ e → 2ℚ * e) v)) (rotL v)))) ⟩
  zipWith _+_ (map (c *_) v)
    (map (c *_)
      (map (λ d → ¼ * d)
        (zipWith _+_ (zipWith _-_ (rotR v) (map (λ e → 2ℚ * e) v)) (rotL v))))
    ≡⟨ sym (scale-+ c v
              (map (λ d → ¼ * d)
                (zipWith _+_ (zipWith _-_ (rotR v) (map (λ e → 2ℚ * e) v)) (rotL v)))) ⟩
  map (c *_) (step v)
    ∎
  where open ≡-Reasoning

-- map-(c*) annihilates the zero vector.
scale-zero : ∀ {m} c → map (c *_) (replicate m 0ℚ) ≡ replicate m 0ℚ
scale-zero {m} c =
  trans (map-replicate (c *_) 0ℚ m) (cong (replicate m) (ℚP.*-zeroʳ c))

step-kernel-contains-nyquist-multiples :
  ∀ c → step (map (c *_) (nyquist 2)) ≡ replicate (2 *ℕ 2) 0ℚ
step-kernel-contains-nyquist-multiples c = begin
  step (map (c *_) (nyquist 2))
    ≡⟨ step-homog c (nyquist 2) ⟩
  map (c *_) (step (nyquist 2))
    ≡⟨ cong (map (c *_)) nyquist-in-step-kernel-2 ⟩
  map (c *_) (replicate (2 *ℕ 2) 0ℚ)
    ≡⟨ scale-zero c ⟩
  replicate (2 *ℕ 2) 0ℚ
    ∎
  where open ≡-Reasoning

------------------------------------------------------------------------
-- Rung 6 (revised) — composition produces a strictly larger kernel.
--
-- `step-then-avg = avg ∘ step` at n = 4, block size 2 (Field 4 →
-- Field 2).  Witness `g6 = [1, −1, −1, 1]`:
--   (a) step-then-avg g6 ≡ 0   (step g6 = [½,−½,−½,½], block-sums 0)
--   (b) g6 is not a scalar multiple of `nyquist 2`
--   (c) step g6 ≠ 0  — so g6's place in ker(avg ∘ step) is via avg,
--       not via step alone.  Condition (c) is *kept* (the witness is
--       constructed directly, so its step-image is computed, not
--       pre-imaged): no drop.

step-then-avg : Field 4 → Field 2
step-then-avg f = avg {1} {2} (step f)

g6 : Field 4
g6 = 1ℚ ∷ - 1ℚ ∷ - 1ℚ ∷ 1ℚ ∷ []

g6-a : step-then-avg g6 ≡ replicate 2 0ℚ
g6-a = refl

g6-b : ¬ (Σ[ c ∈ ℚ ] g6 ≡ map (c *_) (nyquist 2))
g6-b (c , eq) = 1≢-1 (trans (cong idx0 eq) (sym (cong idx2 eq)))
  where
    import Data.Rational.Base as ℚ
    import Data.Integer.Base  as ℤ
    idx0 : Field 4 → ℚ
    idx0 (x ∷ _) = x
    idx2 : Field 4 → ℚ
    idx2 (_ ∷ _ ∷ x ∷ _) = x
    1≢-1 : (1ℚ ≡ - 1ℚ) → ⊥
    1≢-1 p with cong ℚ.↥_ p
    ... | ()

g6-c : ¬ (step g6 ≡ replicate 4 0ℚ)
g6-c eq = ½≢0 (cong ℤ.∣_∣ (cong ℚ.↥_ (cong idx0 eq)))
  where
    import Data.Rational.Base as ℚ
    import Data.Integer.Base  as ℤ
    idx0 : Field 4 → ℚ
    idx0 (x ∷ _) = x
    ½≢0 : (1 ≡ 0) → ⊥
    ½≢0 ()

compose-kernel-strictly-larger :
  Σ[ f ∈ Field 4 ]
    ( step-then-avg f ≡ replicate 2 0ℚ
    × ¬ (Σ[ c ∈ ℚ ] f ≡ map (c *_) (nyquist 2))
    × ¬ (step f ≡ replicate 4 0ℚ) )
compose-kernel-strictly-larger = g6 , g6-a , g6-b , g6-c

------------------------------------------------------------------------
-- Step A — step-additive.
--
-- `step` also commutes with vector addition.  Same shape as
-- `step-homog`: every combinator in `step` (the two `zipWith`s, the
-- ¼/2 scalings, and both rotations) distributes over `zipWith _+_`.
-- The ¼/2 scalings reuse `scale-+`; the rotations need a local
-- `zipWith`/`_∷ʳ_` lemma (`++∷ʳ`) and a `reverse`/`zipWith` lemma
-- (`reverse-zipWith`); the two `zipWith`-level regroupings use the
-- ℚ abelian-group identities `+-interchange` and `sub-exchange`.
-- None of these are in stdlib for ℚ vectors, so they are proved
-- locally (named below); nothing is postulated.

-- ℚ abelian-group element identities.
+-interchange : ∀ a b c d → (a + b) + (c + d) ≡ (a + c) + (b + d)
+-interchange a b c d = begin
  (a + b) + (c + d)   ≡⟨ ℚP.+-assoc a b (c + d) ⟩
  a + (b + (c + d))   ≡⟨ cong (λ z → a + z) (sym (ℚP.+-assoc b c d)) ⟩
  a + ((b + c) + d)   ≡⟨ cong (λ z → a + (z + d)) (ℚP.+-comm b c) ⟩
  a + ((c + b) + d)   ≡⟨ cong (λ z → a + z) (ℚP.+-assoc c b d) ⟩
  a + (c + (b + d))   ≡⟨ sym (ℚP.+-assoc a c (b + d)) ⟩
  (a + c) + (b + d)   ∎
  where open ≡-Reasoning

sub-exchange : ∀ a b c d → (a + c) - (b + d) ≡ (a - b) + (c - d)
sub-exchange a b c d = begin
  (a + c) - (b + d)         ≡⟨ cong (λ z → (a + c) + z) (ℚP.neg-distrib-+ b d) ⟩
  (a + c) + ((- b) + (- d)) ≡⟨ +-interchange a c (- b) (- d) ⟩
  (a + (- b)) + (c + (- d)) ∎
  where open ≡-Reasoning

-- zipWith liftings.
zip-interchange : ∀ {m} (A B C D : Vec ℚ m) →
  zipWith _+_ (zipWith _+_ A B) (zipWith _+_ C D)
  ≡ zipWith _+_ (zipWith _+_ A C) (zipWith _+_ B D)
zip-interchange []       []       []       []       = refl
zip-interchange (a ∷ A) (b ∷ B) (c ∷ C) (d ∷ D) =
  cong₂ _∷_ (+-interchange a b c d) (zip-interchange A B C D)

zip-sub-exchange : ∀ {m} (A B C D : Vec ℚ m) →
  zipWith _-_ (zipWith _+_ A C) (zipWith _+_ B D)
  ≡ zipWith _+_ (zipWith _-_ A B) (zipWith _-_ C D)
zip-sub-exchange []       []       []       []       = refl
zip-sub-exchange (a ∷ A) (b ∷ B) (c ∷ C) (d ∷ D) =
  cong₂ _∷_ (sub-exchange a b c d) (zip-sub-exchange A B C D)

++∷ʳ : ∀ {m} (xs ys : Vec ℚ m) x y →
  zipWith _+_ (xs ∷ʳ x) (ys ∷ʳ y) ≡ (zipWith _+_ xs ys) ∷ʳ (x + y)
++∷ʳ []       []       x y = refl
++∷ʳ (a ∷ xs) (b ∷ ys) x y =
  cong (λ z → (a + b) ∷ z) (++∷ʳ xs ys x y)

reverse-zipWith : ∀ {m} (v w : Vec ℚ m) →
  reverse (zipWith _+_ v w) ≡ zipWith _+_ (reverse v) (reverse w)
reverse-zipWith []       []       = refl
reverse-zipWith (x ∷ xs) (y ∷ ys) = begin
  reverse ((x + y) ∷ zipWith _+_ xs ys)
    ≡⟨ reverse-∷ (x + y) (zipWith _+_ xs ys) ⟩
  reverse (zipWith _+_ xs ys) ∷ʳ (x + y)
    ≡⟨ cong (λ z → z ∷ʳ (x + y)) (reverse-zipWith xs ys) ⟩
  zipWith _+_ (reverse xs) (reverse ys) ∷ʳ (x + y)
    ≡⟨ sym (++∷ʳ (reverse xs) (reverse ys) x y) ⟩
  zipWith _+_ (reverse xs ∷ʳ x) (reverse ys ∷ʳ y)
    ≡⟨ cong₂ (zipWith _+_) (sym (reverse-∷ x xs)) (sym (reverse-∷ y ys)) ⟩
  zipWith _+_ (reverse (x ∷ xs)) (reverse (y ∷ ys))
    ∎
  where open ≡-Reasoning

add-rotL : ∀ {m} (v w : Vec ℚ m) →
  rotL (zipWith _+_ v w) ≡ zipWith _+_ (rotL v) (rotL w)
add-rotL []       []       = refl
add-rotL (x ∷ xs) (y ∷ ys) = sym (++∷ʳ xs ys x y)

add-rotR : ∀ {m} (v w : Vec ℚ m) →
  rotR (zipWith _+_ v w) ≡ zipWith _+_ (rotR v) (rotR w)
add-rotR v w = begin
  reverse (rotL (reverse (zipWith _+_ v w)))
    ≡⟨ cong (reverse ∘ rotL) (reverse-zipWith v w) ⟩
  reverse (rotL (zipWith _+_ (reverse v) (reverse w)))
    ≡⟨ cong reverse (add-rotL (reverse v) (reverse w)) ⟩
  reverse (zipWith _+_ (rotL (reverse v)) (rotL (reverse w)))
    ≡⟨ reverse-zipWith (rotL (reverse v)) (rotL (reverse w)) ⟩
  zipWith _+_ (reverse (rotL (reverse v))) (reverse (rotL (reverse w)))
    ∎
  where open ≡-Reasoning

step-additive : ∀ {n} (v w : Vec ℚ n) →
  step (zipWith _+_ v w) ≡ zipWith _+_ (step v) (step w)
step-additive v w = begin
  step (zipWith _+_ v w)
    ≡⟨⟩
  zipWith _+_ (zipWith _+_ v w)
    (map (λ d → ¼ * d)
      (zipWith _+_
        (zipWith _-_ (rotR (zipWith _+_ v w))
                     (map (λ e → 2ℚ * e) (zipWith _+_ v w)))
        (rotL (zipWith _+_ v w))))
    ≡⟨ cong (λ z → zipWith _+_ (zipWith _+_ v w)
                     (map (λ d → ¼ * d)
                       (zipWith _+_
                         (zipWith _-_ z (map (λ e → 2ℚ * e) (zipWith _+_ v w)))
                         (rotL (zipWith _+_ v w)))))
         (add-rotR v w) ⟩
  zipWith _+_ (zipWith _+_ v w)
    (map (λ d → ¼ * d)
      (zipWith _+_
        (zipWith _-_ (zipWith _+_ (rotR v) (rotR w))
                     (map (λ e → 2ℚ * e) (zipWith _+_ v w)))
        (rotL (zipWith _+_ v w))))
    ≡⟨ cong (λ z → zipWith _+_ (zipWith _+_ v w)
                     (map (λ d → ¼ * d)
                       (zipWith _+_
                         (zipWith _-_ (zipWith _+_ (rotR v) (rotR w)) z)
                         (rotL (zipWith _+_ v w)))))
         (scale-+ 2ℚ v w) ⟩
  zipWith _+_ (zipWith _+_ v w)
    (map (λ d → ¼ * d)
      (zipWith _+_
        (zipWith _-_ (zipWith _+_ (rotR v) (rotR w))
                     (zipWith _+_ (map (λ e → 2ℚ * e) v) (map (λ e → 2ℚ * e) w)))
        (rotL (zipWith _+_ v w))))
    ≡⟨ cong (λ z → zipWith _+_ (zipWith _+_ v w)
                     (map (λ d → ¼ * d)
                       (zipWith _+_ z (rotL (zipWith _+_ v w)))))
         (zip-sub-exchange (rotR v) (map (λ e → 2ℚ * e) v)
                           (rotR w) (map (λ e → 2ℚ * e) w)) ⟩
  zipWith _+_ (zipWith _+_ v w)
    (map (λ d → ¼ * d)
      (zipWith _+_
        (zipWith _+_ (zipWith _-_ (rotR v) (map (λ e → 2ℚ * e) v))
                     (zipWith _-_ (rotR w) (map (λ e → 2ℚ * e) w)))
        (rotL (zipWith _+_ v w))))
    ≡⟨ cong (λ z → zipWith _+_ (zipWith _+_ v w)
                     (map (λ d → ¼ * d)
                       (zipWith _+_
                         (zipWith _+_ (zipWith _-_ (rotR v) (map (λ e → 2ℚ * e) v))
                                      (zipWith _-_ (rotR w) (map (λ e → 2ℚ * e) w)))
                         z)))
         (add-rotL v w) ⟩
  zipWith _+_ (zipWith _+_ v w)
    (map (λ d → ¼ * d)
      (zipWith _+_
        (zipWith _+_ (zipWith _-_ (rotR v) (map (λ e → 2ℚ * e) v))
                     (zipWith _-_ (rotR w) (map (λ e → 2ℚ * e) w)))
        (zipWith _+_ (rotL v) (rotL w))))
    ≡⟨ cong (λ z → zipWith _+_ (zipWith _+_ v w) (map (λ d → ¼ * d) z))
         (zip-interchange (zipWith _-_ (rotR v) (map (λ e → 2ℚ * e) v))
                          (zipWith _-_ (rotR w) (map (λ e → 2ℚ * e) w))
                          (rotL v) (rotL w)) ⟩
  zipWith _+_ (zipWith _+_ v w)
    (map (λ d → ¼ * d)
      (zipWith _+_
        (zipWith _+_ (zipWith _-_ (rotR v) (map (λ e → 2ℚ * e) v)) (rotL v))
        (zipWith _+_ (zipWith _-_ (rotR w) (map (λ e → 2ℚ * e) w)) (rotL w))))
    ≡⟨ cong (λ z → zipWith _+_ (zipWith _+_ v w) z)
         (scale-+ ¼
            (zipWith _+_ (zipWith _-_ (rotR v) (map (λ e → 2ℚ * e) v)) (rotL v))
            (zipWith _+_ (zipWith _-_ (rotR w) (map (λ e → 2ℚ * e) w)) (rotL w))) ⟩
  zipWith _+_ (zipWith _+_ v w)
    (zipWith _+_
      (map (λ d → ¼ * d)
        (zipWith _+_ (zipWith _-_ (rotR v) (map (λ e → 2ℚ * e) v)) (rotL v)))
      (map (λ d → ¼ * d)
        (zipWith _+_ (zipWith _-_ (rotR w) (map (λ e → 2ℚ * e) w)) (rotL w))))
    ≡⟨ zip-interchange v w
         (map (λ d → ¼ * d)
           (zipWith _+_ (zipWith _-_ (rotR v) (map (λ e → 2ℚ * e) v)) (rotL v)))
         (map (λ d → ¼ * d)
           (zipWith _+_ (zipWith _-_ (rotR w) (map (λ e → 2ℚ * e) w)) (rotL w))) ⟩
  zipWith _+_ (step v) (step w)
    ∎
  where open ≡-Reasoning

------------------------------------------------------------------------
-- Step B — the step-kernel is a ℚ-subspace.
--
-- One-off packaging for this example (NOT a general subspace
-- hierarchy): the kernel predicate, closed under both addition
-- (Step A) and scalar multiplication (`step-homog`).  Together with
-- `step-kills-ker` (non-trivial) this says the kernel is a
-- non-zero ℚ-subspace.

StepKernel : ∀ {n} → Vec ℚ n → Set
StepKernel {n} f = step f ≡ replicate n 0ℚ

zero-+-zero : ∀ {n} →
  zipWith _+_ (replicate n 0ℚ) (replicate n 0ℚ) ≡ replicate n 0ℚ
zero-+-zero {n} =
  trans (zipWith-replicate _+_ 0ℚ 0ℚ)
        (cong (replicate n) (ℚP.+-identityˡ 0ℚ))

record StepKernelSubspace : Set where
  field
    closed-+  : ∀ {n} (v w : Vec ℚ n) →
                StepKernel v → StepKernel w → StepKernel (zipWith _+_ v w)
    closed-*ₗ : ∀ {n} (c : ℚ) (v : Vec ℚ n) →
                StepKernel v → StepKernel (map (c *_) v)

step-kernel-subspace : StepKernelSubspace
step-kernel-subspace = record
  { closed-+ = λ v w hv hw →
      trans (step-additive v w)
            (trans (cong₂ (zipWith _+_) hv hw) zero-+-zero)
  ; closed-*ₗ = λ c v hv →
      trans (step-homog c v)
            (trans (cong (map (c *_)) hv) (scale-zero c))
  }

------------------------------------------------------------------------
-- Step C — see report.  The subspace closures (Steps A, B) say the
-- kernel is *a* ℚ-subspace but not *which* one; pinning it to the
-- Nyquist line at n = 4 is the rank-1 fact, which is the symbolic
-- 4×4 ℚ solve the rung-5b spec already flagged as past the
-- ~150-line / type-fighting threshold.  Per the allowed outcome
-- (iii) it is not pursued past that threshold; the containment
-- result `step-kernel-contains-nyquist-multiples` above stands, and
-- Steps A and B are the genuine deliverable of this run.

