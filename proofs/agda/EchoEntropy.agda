{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

-- EchoEntropy: Shannon-entropy non-distinguishing theorem (discrete form).
--
-- Companion to `EchoAbstractionBarrier` (Track B of the Echo-vs-Σ
-- identity claim). The abstraction-barrier module shows that the
-- AFFINE-MODE consumer interface cannot distinguish `weaken echo-true`
-- from `weaken echo-false`, while a raw-Σ `proj₁` consumer CAN
-- distinguish the unweakened echoes. This module discharges the
-- complementary "Shannon entropy alone cannot distinguish" claim:
-- any consumer that depends only on the fibre's *entropic shadow*
-- (the per-fibre count, or `⌊log₂⌋` of it) agrees on the two echoes,
-- while the raw witness — exactly what the entropic shadow forgets —
-- continues to distinguish.
--
-- The shadow used here is the finite-domain fibre count from
-- `EchoFiberCount.FiberSize-fin`, applied to the canonical
-- `Fin 2 → ⊤` representation of `collapse : Bool → ⊤`. Both Bool
-- branches map to `tt`, so the fibre count is `2`, and Shannon's
-- uniform-prior entropy `⌊log₂ 2⌋ ≡ 1` bit. Both echoes share this
-- shadow exactly because they share the fibre.
--
-- Why discrete? Real-valued Shannon entropy `H(P) = -Σ p log p`
-- needs real arithmetic and a probability layer, neither of which
-- is available under `--safe --without-K` without a heavy real-
-- numbers / measure-theoretic library. The discrete fibre count is
-- the standard uniform-distribution surrogate: under the maximum-
-- entropy prior on the fibre, `H = log₂ (fibre size)`. The numerical
-- log reuses `EchoThermodynamics.⌊log₂1⌋≡0` for the singleton case
-- and is computed directly for the two-element case here.
--
-- Closes the "Shannon-entropy / mutual-information formalisations:
-- not yet present" item flagged in `EchoThermodynamics.agda` and
-- `EchoStabilityTests.agda`. See also
-- `core/skepticisms/what-is-actually-new.md` (the entropic shadow
-- is exactly what the "just information loss" skeptic conflates with
-- Echo).
--
-- Headlines (pinned in Smoke.agda):
--
--   * collapse-as-fin                 -- Fin 2 representation of collapse
--   * collapse-fibre-count            -- FiberSize-fin = 2
--   * entropy-shadow                  -- the fibre-count proxy
--   * shannon-shadow                  -- ⌊log₂⌋ of the proxy (= 1 bit)
--   * entropy-shadow-equal            -- shadow agrees on echo-true vs false
--   * shannon-shadow-equal            -- Shannon bits agree on echo-true vs false
--   * entropy-shadow-blind            -- any consumer factoring through the
--                                        fibre-count agrees on the two echoes
--   * shannon-shadow-blind            -- the same, after taking log₂
--   * witness-distinguishes-where-entropy-cannot
--                                     -- matched-negative: proj₁ DOES
--                                        distinguish (cited from
--                                        sigma-distinguishes)
--   * entropy-blind-parametric        -- parametric: any functional of any
--                                        fibre-determined distribution is blind
--   * entropy-witness-distinguishes   -- matched-negative (parametric): a
--                                        witness-determined distribution
--                                        distinguishes
--
-- Scope guardrail. Two non-distinguishing forms are proved: the
-- discrete one ("any function of the fibre count is constant on
-- echo-true vs echo-false") and its parametric generalisation
-- (`entropy-blind-parametric`: any functional of any fibre-determined
-- distribution is constant, with `entropy-witness-distinguishes` the
-- matched-negative). What is NOT formalised is only the *construction*
-- of a concrete real-valued `H(P) = -Σ p log p` — an orthogonal
-- reals/logarithm task; the non-distinguishing already covers any such
-- functional once supplied. See the companion remark at the end.

module EchoEntropy where

open import Echo                    using (Echo; echo-intro)
open import EchoCharacteristic      using (collapse; echo-true; echo-false; true≢false)
open import EchoFiberCount          using (FiberSize-fin; FiberSize-fin-all-hit)
open import EchoThermodynamics      using (⌊log₂1⌋≡0)
open import EchoAbstractionBarrier  using (sigma-distinguishes)

open import Data.Bool.Base          using (Bool)
open import Data.Fin.Base           using (Fin; zero; suc)
open import Data.Nat.Base           using (ℕ; suc; zero)
open import Data.Nat.Logarithm      using (⌊log₂_⌋)
open import Data.Product.Base       using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.Unit.Base          using (⊤; tt)
open import Relation.Binary.PropositionalEquality
                                    using (_≡_; _≢_; refl; cong)
open import Relation.Nullary.Decidable.Core using (Dec; yes; no)
open import Level                   using (Level)

private variable
  ℓ : Level

----------------------------------------------------------------------
-- Local: decidable equality on ⊤.
--
-- The fibre-count function `FiberSize-fin` takes a `(y₁ y₂ : B) →
-- Dec (y₁ ≡ y₂)` argument. For `B = ⊤` (the codomain of `collapse`)
-- this is one line. Kept local to avoid a stdlib import dependency
-- that other Echo modules don't pull in.
----------------------------------------------------------------------

⊤-≟ : (x y : ⊤) → Dec (x ≡ y)
⊤-≟ tt tt = yes refl

----------------------------------------------------------------------
-- The `Fin 2` representation of `collapse`.
--
-- `collapse : Bool → ⊤` has Bool as its domain; `FiberSize-fin`
-- needs a `Fin n` domain. The canonical 2-element enumeration is
-- `Fin 2`. Both branches map to `tt`, so the fibre at `tt` is the
-- full domain.
----------------------------------------------------------------------

collapse-as-fin : Fin 2 → ⊤
collapse-as-fin _ = tt

----------------------------------------------------------------------
-- The fibre count at `tt`. The all-hit lemma discharges this in one
-- line: every `Fin 2` index maps to `tt`, so the count is the
-- domain size `2`.
----------------------------------------------------------------------

collapse-fibre-count :
  FiberSize-fin collapse-as-fin tt ⊤-≟ ≡ 2
collapse-fibre-count =
  FiberSize-fin-all-hit collapse-as-fin tt ⊤-≟ (λ _ → refl)

----------------------------------------------------------------------
-- The entropy shadow.
--
-- Any `e : Echo collapse tt` shares the same fibre at `tt`; its
-- "entropic content" — the count of preimages collapsed onto the
-- same visible value — is exactly the constant `2`. Stated as a
-- function `Echo collapse tt → ℕ` so it has the same shape as
-- downstream consumers; the function is constant in `e`.
----------------------------------------------------------------------

entropy-shadow : Echo collapse tt → ℕ
entropy-shadow _ = FiberSize-fin collapse-as-fin tt ⊤-≟

----------------------------------------------------------------------
-- The Shannon shadow: `⌊log₂⌋` of the fibre count.
--
-- Under the maximum-entropy (uniform) prior on the fibre, this is
-- exactly Shannon's `H = log₂ |fibre|` measured in bits. For
-- `collapse` at `tt` the fibre has size 2, so the Shannon shadow
-- is `⌊log₂ 2⌋ ≡ 1` bit. Definitional in `⌊log₂_⌋`.
----------------------------------------------------------------------

shannon-shadow : Echo collapse tt → ℕ
shannon-shadow e = ⌊log₂ entropy-shadow e ⌋

----------------------------------------------------------------------
-- Headline 1 (positive). The entropy shadow agrees on `echo-true`
-- and `echo-false`. Definitional: `entropy-shadow _ = 2` does not
-- inspect its argument.
----------------------------------------------------------------------

entropy-shadow-equal :
  entropy-shadow echo-true ≡ entropy-shadow echo-false
entropy-shadow-equal = refl

----------------------------------------------------------------------
-- Headline 2 (positive). The Shannon shadow agrees on `echo-true`
-- and `echo-false`. Both reduce to `⌊log₂ 2⌋ = 1`.
----------------------------------------------------------------------

shannon-shadow-equal :
  shannon-shadow echo-true ≡ shannon-shadow echo-false
shannon-shadow-equal = refl

----------------------------------------------------------------------
-- Headline 3 (positive). Any consumer that factors through the
-- entropy shadow gives the same value on `echo-true` and
-- `echo-false`. This is the abstract statement of "Shannon entropy
-- alone cannot distinguish": the shadow is the entropic data, and
-- any function of *only* that data is blind to the witness.
----------------------------------------------------------------------

entropy-shadow-blind :
  {X : Set ℓ} (g : ℕ → X) →
  g (entropy-shadow echo-true) ≡ g (entropy-shadow echo-false)
entropy-shadow-blind g = cong g entropy-shadow-equal

----------------------------------------------------------------------
-- Headline 4 (positive). Same shape, after taking `⌊log₂⌋`: any
-- consumer of the Shannon-bits view is blind to the witness.
----------------------------------------------------------------------

shannon-shadow-blind :
  {X : Set ℓ} (g : ℕ → X) →
  g (shannon-shadow echo-true) ≡ g (shannon-shadow echo-false)
shannon-shadow-blind g = cong g shannon-shadow-equal

----------------------------------------------------------------------
-- Headline 5 (negative companion — the matched-negative artefact).
-- The entropy-blind result is non-trivial because the WITNESS side
-- DOES distinguish: `proj₁ : Echo collapse tt → Bool` produces
-- `true` on `echo-true` and `false` on `echo-false`. Cited directly
-- from `EchoAbstractionBarrier.sigma-distinguishes` so the pairing
-- is a checked artefact.
--
-- This is the load-bearing observation: the abstraction-barrier
-- counter-program is ALSO the witness-side counter-program for the
-- entropy theorem. Both shadows discard the same component (the
-- second-projection equality witness); the affine consumer
-- interface and the entropic shadow are two different ways of
-- "looking at" the echo that both lose its distinguishing power.
----------------------------------------------------------------------

witness-distinguishes-where-entropy-cannot :
  Σ (Echo collapse tt → Bool)
    (λ g → g echo-true ≢ g echo-false)
witness-distinguishes-where-entropy-cannot = sigma-distinguishes

----------------------------------------------------------------------
-- Parametric generalisation: arbitrary distribution, arbitrary
-- information functional.
--
-- Headline 3 (`entropy-shadow-blind`) covers any function of the
-- fibre *count* — a single `ℕ`. The strictly stronger statement the
-- companion remark flags as open quantifies instead over a whole
-- *distribution* across the fibre — the data a real-valued
-- `H(P) = -Σ p log p` actually consumes — valued in an arbitrary
-- weight type `W` and fed to an arbitrary information functional
-- `H : (Fin 2 → W) → X` (Shannon / Rényi entropy, mutual
-- information, the raw probability vector, …).
--
-- The fibre of `collapse` at `tt` is the whole domain `Fin 2`,
-- shared by both echoes. A distribution *read off the fibre* (not off
-- the witness `proj₁ e`) does not mention the echo, so any functional
-- of it is blind. This discharges the *non-distinguishing* content of
-- the "parametric probability distribution" item for ANY such
-- functional, with no reals/log library required — the blindness is
-- structural. Constructing a concrete real-valued `-Σ p log p` is an
-- orthogonal analysis task (a reals + logarithm formalisation),
-- independent of Echo, and is deliberately NOT attempted here.
----------------------------------------------------------------------

-- A fibre-determined distribution valued in `W`: a weight per fibre
-- index, chosen independently of which echo is held. It ignores its
-- echo argument — that is exactly what "read off the fibre, not the
-- witness" means.
fibre-distribution : {W : Set ℓ} → (Fin 2 → W) → Echo collapse tt → (Fin 2 → W)
fibre-distribution P _ = P

----------------------------------------------------------------------
-- Headline 6 (positive, parametric). Any information functional `H`
-- of any fibre-determined distribution `P` agrees on `echo-true` and
-- `echo-false`. Strictly generalises Headline 3 from a function of
-- the count to a functional of the full distribution — covering
-- real-/rational-/abstract-valued entropy the moment such a
-- functional is supplied. Definitional: `fibre-distribution P`
-- ignores its echo argument.
----------------------------------------------------------------------

entropy-blind-parametric :
  {W X : Set ℓ}
  (P : Fin 2 → W) (H : (Fin 2 → W) → X) →
  H (fibre-distribution P echo-true) ≡ H (fibre-distribution P echo-false)
entropy-blind-parametric P H = refl

----------------------------------------------------------------------
-- Headline 7 (negative companion, parametric). A distribution read
-- off the WITNESS — here every index carries the distinguishing bit
-- `proj₁ sigma-distinguishes e` — DOES separate the two echoes under
-- a functional that samples it. Matched-negative for Headline 6:
-- blindness holds for fibre-determined distributions and fails for
-- witness-determined ones, mirroring the fibre-vs-witness split of
-- the discrete result.
----------------------------------------------------------------------

witness-distribution : Echo collapse tt → (Fin 2 → Bool)
witness-distribution e _ = proj₁ sigma-distinguishes e

entropy-witness-distinguishes :
  Σ ((Fin 2 → Bool) → Bool)
    (λ H → H (witness-distribution echo-true) ≢ H (witness-distribution echo-false))
entropy-witness-distinguishes = (λ d → d zero) , proj₂ sigma-distinguishes

----------------------------------------------------------------------
-- Companion remark on what is NOT claimed.
--
-- * The *non-distinguishing* content for a parametric distribution is
--   now formalised: `entropy-blind-parametric` (Headline 6) shows any
--   information functional of any fibre-determined distribution is
--   witness-blind, and `entropy-witness-distinguishes` (Headline 7) is
--   the matched-negative for witness-determined distributions. What
--   remains unformalised is only the *construction* of a concrete
--   real-valued `H(P) = -Σ p log p` — a reals + logarithm formalisation,
--   an analysis task orthogonal to Echo. Headline 6 already covers it
--   for ANY such functional the moment one is supplied.
--
-- * Mutual information `I(X; Y) = H(X) - H(X|Y)` is not formalised
--   either. The corresponding Echo-side statement would be:
--   "the mutual information between the visible output and the
--   raw witness is positive at fibres of size ≥ 2". The fibre-count
--   shadow proved here is the `H(X)` side; the `H(X|Y)` side
--   requires a conditional-probability layer.
--
-- * The discrete theorem here is the strongest form available under
--   `--safe --without-K` without funext or real arithmetic. It is
--   exactly the cementing artefact requested in the audit follow-up:
--   "Shannon entropy alone cannot distinguish echo-true vs
--   echo-false". The discharge is a one-line `cong` of the witness-
--   blind shadow.
----------------------------------------------------------------------
