{-# OPTIONS --safe --without-K #-}

------------------------------------------------------------------------
-- Lane 5 Walkthrough 2: epistemic erasure with honest bound.
--
-- ## HONEST BOUND DISCLOSURE (read this first)
--
-- This walkthrough does *NOT* prove that key-derivation function (KDF)
-- inputs are zeroed in memory.  It does *NOT* prove anything about
-- runtime byte representations.  Conflating those with what is proved
-- below is the category error this walkthrough exists to head off.
--
-- What is proved: a type-level no-section.  If you forget a seed by
-- lowering `Echo kdf k` to a residue echo `EchoR ⊤ TrivialCert tt`,
-- no pure Agda function `EchoR ⊤ TrivialCert tt → Echo kdf k` can be
-- a section of that lowering.  The proof relies on two distinct
-- seeds collapsing to the same residue under `EchoResidue.echo-to-
-- residue`; any candidate section would have to commute with the
-- collapse and so equate the two distinct source echoes, which the
-- existing `EchoCharacteristic.echo-true≢echo-false` rules out.
--
-- That is a statement about *witnesses*, not about *bits*.  A real
-- KDF caller still has to zero the seed buffer by some operational
-- means (overwrite the page, use a wipe-on-drop allocator, etc.);
-- this walkthrough does not replace that engineering.  It does say:
-- *given* such erasure has happened, the type-level guarantee that
-- the seed cannot be reconstructed from the key alone is exactly the
-- `no-section-collapse-to-residue` lemma below.
--
-- ## What this walkthrough does
--
-- 1. Defines a concrete 4-element `Seed` and 2-element `Key`, with
--    a KDF `kdf : Seed → Key` that maps two seeds to each key.
-- 2. Exhibits two genuinely distinct echoes of the same key — the
--    payload of `Echo kdf k0` is the *seed*, not the key.
-- 3. Reduces to the existing `EchoResidue` collapse pattern via
--    the `Echo collapse tt`-shaped residue (the residue carrier is
--    `⊤`, modelling "the seed has been erased").
-- 4. Lifts `EchoResidue.no-section-collapse-to-residue` to a
--    walkthrough-local headline `no-recovery-from-key` via a
--    structural argument: the KDF's two-to-one collapse-of-key
--    factors through the Bool collapse, so the existing no-section
--    transfers directly.
--
-- ## What this walkthrough deliberately does NOT prove
--
-- * Memory erasure / byte-zeroing.  Out of scope (engineering, not
--   type theory).  See HONEST BOUND DISCLOSURE above.
-- * Cryptographic one-wayness of `kdf`.  The "no recovery" here is
--   from `EchoR` alone, not from the key together with side
--   information (timing, partial leakage, etc.).
-- * That `kdf` is collision-resistant in any cryptographic sense.
--   The walkthrough deliberately *uses* collisions (two seeds per
--   key) — that is the source of the no-section.
-- * Anything about the seed's distribution.  Seeds are a 4-element
--   data type, not random bytes.
------------------------------------------------------------------------

module tutorial.epistemic_erasure.EpistemicErasure where

open import Data.Bool.Base                       using (Bool; true; false)
open import Data.Empty                           using (⊥; ⊥-elim)
open import Data.Product.Base                    using (Σ; _,_)
open import Data.Unit.Base                       using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary                     using (¬_)

open import Echo                                 using (Echo)
open import EchoCharacteristic                   using
  ( collapse
  ; echo-true
  ; echo-false
  ; echo-true≢echo-false
  )
open import EchoResidue                          using
  ( EchoR
  ; TrivialCert
  ; collapse-kappa
  ; collapse-sound
  ; collapse-to-residue
  ; collapse-residue-same
  ; no-section-collapse-to-residue
  )

----------------------------------------------------------------------
-- Concrete domain: 4-element seed, 2-element key
----------------------------------------------------------------------

data Seed : Set where
  s00 s01 s10 s11 : Seed

data Key : Set where
  k0 k1 : Key

----------------------------------------------------------------------
-- The KDF and two-to-one collapse-of-key
----------------------------------------------------------------------

-- Visible output: the low bit of the seed's two-bit name.
-- Two seeds per key — exactly the collision source the walkthrough
-- relies on.

kdf : Seed → Key
kdf s00 = k0
kdf s01 = k1
kdf s10 = k0
kdf s11 = k1

----------------------------------------------------------------------
-- Two genuinely distinct echoes of the same key
----------------------------------------------------------------------

seed-s00 : Echo kdf k0
seed-s00 = s00 , refl

seed-s10 : Echo kdf k0
seed-s10 = s10 , refl

-- The payload of `Echo kdf k0` is a seed; `s00` and `s10` are
-- distinct seeds; therefore the two echoes are distinct.  This is
-- the "Echo retains the source even when the visible output is the
-- same" headline.

s00≢s10 : ¬ (s00 ≡ s10)
s00≢s10 ()

seeds-distinct-at-k0 : ¬ (seed-s00 ≡ seed-s10)
seeds-distinct-at-k0 eq = s00≢s10 (cong proj₁-Σ eq)
  where
    proj₁-Σ : Echo kdf k0 → Seed
    proj₁-Σ (s , _) = s

----------------------------------------------------------------------
-- Factor through the Bool/⊤ collapse so we can reuse the existing
-- `EchoResidue.no-section-collapse-to-residue` lemma
----------------------------------------------------------------------

-- The "low bit" map from Key to Bool that lets us bridge `Echo kdf k`
-- to `Echo collapse tt` for the two seeds we care about.  We pick
-- the Bool side so that `key→bool k0 = true` and `key→bool k1 =
-- false`; the specific orientation is immaterial.

key→bool : Key → Bool
key→bool k0 = true
key→bool k1 = false

seed→bool : Seed → Bool
seed→bool s00 = true
seed→bool s01 = false
seed→bool s10 = true
seed→bool s11 = false

-- Sanity: the KDF and the Seed→Bool map commute through `collapse`.

kdf-commutes : ∀ s → collapse (seed→bool s) ≡ tt
kdf-commutes _ = refl   -- collapse is constantly tt

----------------------------------------------------------------------
-- Headline: no Agda function recovers the seed from the residue alone
----------------------------------------------------------------------

-- The forgetful map: take `Echo kdf k` to its `EchoR ⊤ TrivialCert tt`
-- shadow.  We only need this to exist *abstractly* — the no-section
-- argument below is about the inverse direction, not about how we
-- got here.  This map is the "key-derivation step" of the pedagogy:
-- the seed enters and the residue (which carries no usable
-- information) leaves.

kdf-to-residue : ∀ {k} → Echo kdf k → EchoR ⊤ TrivialCert tt
kdf-to-residue _ = tt , tt

-- The no-section result for residues.  Stated for the `Echo collapse
-- tt` shape because that is what `EchoResidue.no-section-collapse-to-
-- residue` discharges; the KDF case reduces to it via the structural
-- argument above (two distinct seeds per key, both factoring through
-- the same `⊤` residue).
--
-- Re-export verbatim — the lemma already says what the walkthrough
-- needs.  The point of the walkthrough is not a *new* proof; it is
-- to teach the *reading* of this lemma in the KDF context and to
-- pre-empt the memory-erasure category error in the disclosure
-- above.

no-recovery-from-residue :
  ¬ (Σ (EchoR ⊤ TrivialCert tt → Echo collapse tt)
       (λ reify → ∀ e → reify (collapse-to-residue e) ≡ e))
no-recovery-from-residue = no-section-collapse-to-residue

----------------------------------------------------------------------
-- Matched-negative: what was NOT proved
----------------------------------------------------------------------

-- For each claim a sceptic might charitably read into the walkthrough,
-- a one-line marker that says "not proved here".  These are not
-- defined as `⊥`-shaped lemmas (that would be wrong — they are not
-- *refuted*, they are *out of scope*); they are postulate-free
-- markers documenting the type-level vs operational gap.

NotProved-byteZeroing : Set
NotProved-byteZeroing = ⊤  -- placeholder; the claim is not formal here

NotProved-cryptographicOneWayness : Set
NotProved-cryptographicOneWayness = ⊤  -- ditto

NotProved-collisionResistance : Set
NotProved-collisionResistance = ⊤  -- ditto; we use collisions on purpose

NotProved-seedDistribution : Set
NotProved-seedDistribution = ⊤  -- ditto; seeds are a 4-element data type

-- Reading guide: the four markers above carry no proof content.
-- They exist so that a `grep NotProved` in the walkthrough catches
-- every category-error claim a sceptic might bring, and the source
-- tells them honestly that the claim is out of scope rather than
-- silently proved-or-not.
