{-# OPTIONS --safe --without-K #-}

-- Gate F4 feasibility spike (docs/echo-types/earn-back-plan.adoc §"Gate
-- F4 — Universal property, honestly qualified").
--
-- The R-2026-05-18 retraction narrowed `EchoPullback.echo-pullback-univ`
-- to a *pointwise* mediator property (`∀ v → m' v ≡ m v`); the
-- terminal-cone universal property `m' ≡ m` was unstatable there
-- without funext, and a funext postulate is forbidden estate-wide.
--
-- F4's earn-back is NOT "retracted → unconditional"; it is
-- "retracted → *true, conditional*": parameterise the strict
-- terminality result by an EXPLICIT funext hypothesis (a module
-- parameter — never a postulate), exactly as `Echo.agda` parameterises
-- `cancel-iso-from-to` / `cancel-iso-to-from` by the triangle-identity
-- coherences. Then `echo-pullback-univ-strict` is a genuine universal
-- property *given funext*, with zero postulates retained, and the
-- unconditional pointwise result stays as the funext-free corollary.
--
-- Result of the spike: it closes in three lines on top of the
-- already-landed pointwise lemma. No K, no funext in the trusted
-- base (funext is a hypothesis the caller must supply, exactly like
-- `triangle₁`/`triangle₂` in `Echo.agda`), zero postulates. Not wired
-- into `All.agda` / `Smoke.agda` until Gate F4 is recorded passed.

module Echo.Bridges.EchoPullbackUnivF4 where

open import Echo.Core using (Echo)
open import Echo.Bridges.EchoPullback using (EchoCone; IsMediator; echo-pullback-univ)
open import Data.Product.Base using (Σ; _,_; _×_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_)

----------------------------------------------------------------------
-- The funext hypothesis, as an explicit (level-0) coherence — NOT a
-- postulate. `Set₁` because it quantifies over `Set`; this is exactly
-- the universe `EchoPullback` lives at (`{A B : Set}`, `V : Set`,
-- `Echo f y : Set`), so no `Setω` and no extra level machinery.

FunExt₀ : Set₁
FunExt₀ =
  {A : Set} {B : A → Set} {f g : (x : A) → B x} →
  (∀ x → f x ≡ g x) → f ≡ g

----------------------------------------------------------------------
-- Strict terminality, parameterised by funext.
--
-- `echo-cone` is the terminal cone *strictly*: every cone morphism is
-- equal — as a function — to the mediator, not merely pointwise. The
-- proof is one application of the supplied `funext` to the pointwise
-- uniqueness already proved (funext-free, K-free) in
-- `EchoPullback.echo-pullback-univ`.

module _ (funext : FunExt₀) where

  echo-pullback-univ-strict :
    {A B : Set} (f : A → B) (y : B) {V : Set} (c : EchoCone f y V) →
    Σ (V → Echo f y) (λ m →
      IsMediator f y c m
      × (∀ (m' : V → Echo f y) → IsMediator f y c m' → m' ≡ m))
  echo-pullback-univ-strict f y c with echo-pullback-univ f y c
  ... | m , med , uniq-pt =
        m , med , λ m' med' → funext (uniq-pt m' med')

----------------------------------------------------------------------
-- The funext-free corollary is kept verbatim: it is exactly
-- `EchoPullback.echo-pullback-univ`, re-exported here so the
-- conditional/unconditional pair lives in one place. Reading:
--
--   * unconditional, zero hypotheses : pointwise mediator property
--       (`echo-pullback-univ`        — `∀ v → m' v ≡ m v`);
--   * conditional on `funext`        : strict terminal cone
--       (`echo-pullback-univ-strict` — `m' ≡ m`).
--
-- No claim is upgraded beyond what its hypothesis license: the strict
-- form is *true given funext*, stated as such.

echo-pullback-univ-pointwise :
  {A B : Set} (f : A → B) (y : B) {V : Set} (c : EchoCone f y V) →
  Σ (V → Echo f y) (λ m →
    IsMediator f y c m
    × (∀ (m' : V → Echo f y) → IsMediator f y c m' →
         ∀ v → m' v ≡ m v))
echo-pullback-univ-pointwise = echo-pullback-univ
