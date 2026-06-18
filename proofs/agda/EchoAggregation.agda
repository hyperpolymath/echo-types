{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

-- EchoAggregation: micro→macro economic aggregation as structured loss.
--
-- This module mechanises the keystone claim of the oikos/betlang
-- "aggregate library" design note (oikos
-- `docs/alib-aggregate-bridge.adoc` §2): economic *aggregation* —
-- rolling a micro ledger up into a macro observable — is literally an
-- `Echo` map, and the *non-identifiability* of the micro state from
-- the macro observable ("you cannot disaggregate") is literally the
-- repo's `no-section` theorem.
--
-- The honest minimal instance.  The alib's `MacroState` is a rich
-- record (population, elites, capital stock, …).  Each of its fields
-- is an aggregation of the same shape: a sum (a Godley column) of
-- micro entries.  The load-bearing structural fact is visible already
-- at the smallest faithful case — a two-account ledger collapsing to
-- a total:
--
--   * `MicroLedger = ℕ × ℕ`   two sector balances (e.g. household,
--                              firm) — the micro state;
--   * `MacroTotal  = ℕ`        the aggregate money stock — one Godley
--                              column sum, the macro observable;
--   * `aggregate (a , b) = a + b`   the rollup.
--
-- The full `MacroState` is then a product of such projections; the
-- structural story (many-to-one ⇒ no canonical disaggregation) is
-- identical field-by-field, so the single-column instance is the
-- right place to pin it.
--
-- What is proved.
--
--   * `ConsistentLedgers m = Echo aggregate m` — the fibre: ALL micro
--     ledgers consistent with the macro total `m`.  This IS the
--     economist's "aggregation is many-to-one", as a type.
--   * `aggregate-non-injective` — two distinct micro ledgers,
--     `(0,1)` and `(1,0)`, are distinct echoes at the SAME macro
--     total `1`.  The fibre is genuinely non-trivial.
--   * `no-canonical-disaggregation` (keystone) — `aggregate` admits
--     NO section: there is no `raise : MacroTotal → MicroLedger`
--     recovering the micro split from the macro total for every
--     input.  This is the aggregation / non-identifiability problem,
--     as a theorem, obtained by instantiating the generic
--     `EchoNoSectionGeneric.no-section-of-collapsing-map`.
--
-- This is the SAME `no-section` machinery that underwrites the
-- affine⊑linear story in the wasm proof layer (`EchoLinear.weaken`,
-- machine-checked equal to AffineScript subtyping in
-- `nextgen-typing`'s `EchoTyping.agda`).  One type language serves
-- micro→macro aggregation, cross-language ABI, and uncertainty.
--
-- Headlines (pinned in Smoke.agda):
--
--   * aggregate                   -- the rollup map
--   * ConsistentLedgers           -- its fibre, as an Echo
--   * aggregate-non-injective     -- the fibre is non-trivial
--   * no-canonical-disaggregation -- the keystone: no section
--
-- Scope guardrail.  `aggregate` here is a concrete finite ℕ-valued
-- map; the theorem is about THIS map's non-injectivity.  It does NOT
-- claim a quantitative bound on the size of fibres, nor anything
-- about the rich `MacroState` record's joint identifiability — those
-- are downstream, and named in the alib note's open questions.  The
-- minimal claim is exactly the load-bearing one: aggregation is an
-- Echo, and the macro observable cannot in general be disaggregated.

module EchoAggregation where

open import Echo                 using (Echo; echo-intro)
open import EchoNoSectionGeneric using (no-section-of-collapsing-map)

open import Data.Nat.Base        using (ℕ; _+_)
open import Data.Product.Base    using (Σ; _×_; _,_; proj₁)
open import Relation.Binary.PropositionalEquality
                                 using (_≡_; _≢_; refl; cong)
open import Relation.Nullary     using (¬_)

----------------------------------------------------------------------
-- The micro / macro types and the aggregation map.
----------------------------------------------------------------------

-- A micro ledger: two sector balances (e.g. household, firm).
MicroLedger : Set
MicroLedger = ℕ × ℕ

-- The macro observable: one aggregate total (a Godley column sum).
MacroTotal : Set
MacroTotal = ℕ

-- Aggregation: roll the micro ledger up into the macro total.
aggregate : MicroLedger → MacroTotal
aggregate (a , b) = a + b

----------------------------------------------------------------------
-- The fibre, as an Echo.
--
-- `ConsistentLedgers m` is the type of ALL micro ledgers whose rollup
-- is exactly the macro total `m`.  Definitionally it is
-- `Σ MicroLedger (λ l → aggregate l ≡ m)` — the fibre of `aggregate`
-- over `m`.  "Aggregation is many-to-one" becomes "this type can have
-- more than one inhabitant" (witnessed below).
----------------------------------------------------------------------

ConsistentLedgers : MacroTotal → Set
ConsistentLedgers m = Echo aggregate m

----------------------------------------------------------------------
-- The fibre over macro total 1 is non-trivial: two distinct micro
-- ledgers, (0,1) and (1,0), both aggregate to 1.
----------------------------------------------------------------------

ledger₁ : MicroLedger
ledger₁ = 0 , 1

ledger₂ : MicroLedger
ledger₂ = 1 , 0

-- The two micro ledgers are distinct: their household balances differ
-- (0 vs 1).  Refuted at the first projection by constructor clash.
ledger₁≢ledger₂ : ledger₁ ≢ ledger₂
ledger₁≢ledger₂ eq with cong proj₁ eq
... | ()

-- … yet they collapse to the same macro total (both 1).
aggregate-collapses : aggregate ledger₁ ≡ aggregate ledger₂
aggregate-collapses = refl

-- As echoes at the same macro total.
echo-ledger₁ : ConsistentLedgers 1
echo-ledger₁ = echo-intro aggregate ledger₁

echo-ledger₂ : ConsistentLedgers 1
echo-ledger₂ = echo-intro aggregate ledger₂

-- The fibre is genuinely non-trivial: two distinct inhabitants at the
-- same macro observable.  This is "aggregation is many-to-one", as a
-- checked theorem.
aggregate-non-injective : echo-ledger₁ ≢ echo-ledger₂
aggregate-non-injective eq = ledger₁≢ledger₂ (cong proj₁ eq)

----------------------------------------------------------------------
-- The keystone: no canonical disaggregation.
--
-- There is no section `raise : MacroTotal → MicroLedger` recovering
-- the micro split from the macro total for every input — i.e. no
-- function with `raise (aggregate l) ≡ l` for all micro ledgers `l`.
-- This is the aggregation / non-identifiability problem of
-- macroeconomics, obtained as a one-instance application of the
-- generic no-section theorem.
----------------------------------------------------------------------

no-canonical-disaggregation :
  ¬ Σ (MacroTotal → MicroLedger)
       (λ raise → ∀ l → raise (aggregate l) ≡ l)
no-canonical-disaggregation =
  no-section-of-collapsing-map
    aggregate
    ledger₁ ledger₂
    ledger₁≢ledger₂
    aggregate-collapses

----------------------------------------------------------------------
-- Companion remark.
--
-- Why this is the right level of generality:
--
--   * The fibre `ConsistentLedgers m` is `Echo aggregate m` ON THE
--     NOSE (definitional), so every downstream `Echo`/`EchoResidue`
--     result applies to aggregation without restatement.  In
--     particular the residue machinery names what the macro layer is
--     entitled to observe after the loss.
--
--   * `no-canonical-disaggregation` refutes a LEFT inverse (a
--     section of `aggregate`).  It does NOT refute the existence of
--     SOME right inverse / choice of representative — economists pick
--     representatives all the time (a "typical household").  The
--     content is precisely that no such choice is CANONICAL: it
--     cannot satisfy `raise ∘ aggregate ≡ id`, so it always discards
--     information about ledgers it did not pick.
--
--   * Promoting this to the rich `MacroState` record is mechanical:
--     each field is an aggregation of this shape, and a section of
--     the product would restrict to a section of each projection,
--     which this theorem already refutes.  No new proof idea is
--     needed; see the alib note §3–§4.
----------------------------------------------------------------------
