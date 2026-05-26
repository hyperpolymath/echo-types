{-# OPTIONS --safe --without-K #-}

-- Track C of the Echo-vs-Σ identity claim consolidation
-- (`roadmap.adoc` §Lane 2 close-out item 2; companion to
-- `core/skepticisms/is-this-just-sigma-types.md` §5 and
-- `docs/echo-types/sigma-distinctness-map.adoc` §"Demand 5").
--
-- For each headline example (parser, provenance, absint), exhibit the
-- small raw-Σ counter-program that the Echo interface refuses to
-- export at affine mode. Each `*-sigma-distinguishes` is the
-- *negative companion* to the positive distinct-echoes-same-y theorem
-- already in the example module: it shows the concrete consumer that
-- would let the bug through if `proj₁` (or anything that factors
-- through it) were exposed.
--
-- The pattern mirrors `EchoAbstractionBarrier.sigma-distinguishes` at
-- the per-example level. Together with the affine-side guarantee in
-- `EchoAbstractionBarrier.affine-consumer-cannot-distinguish`, these
-- per-example negatives establish the Gate 3 "matched-positive +
-- matched-negative pair" discipline ("raw Σ would leak; Echo blocks
-- it") for each headline example.
--
-- Scope guardrail: each lemma is a *concrete instance* of the raw-Σ
-- distinguish pattern at the linear-side echo, exhibiting what an
-- unprotected Σ-projection would do with the example's distinct
-- preimages. The corresponding affine-side guarantee that nothing of
-- this shape can exist is the general `affine-consumer-cannot-distinguish`,
-- not re-proven here per-example.

module examples.EchoVsSigma where

open import Echo                  using (Echo)

open import EchoExampleParser
  using ( Token
        ; parses
        ; paren-pair; paren-nested
        ; echo-parse-pair; echo-parse-nested
        ; paren-nested≢paren-pair
        )
open import EchoExampleProvenance
  using ( Row; project
        ; echo-prov-true; echo-prov-false
        ; true≢false
        )
open Row using (prov)
open import EchoExampleAbsInt
  using ( Sign; Carrier; pos; α
        ; p1; p2
        ; echo-pos-p1; echo-pos-p2
        ; p1≢p2
        )

open import Data.Bool.Base    using (Bool; true)
open import Data.List.Base    using (List)
open import Data.Product.Base using (Σ; _,_; proj₁)
open import Relation.Binary.PropositionalEquality
                              using (_≡_; _≢_)
open import Function.Base     using (_∘_)

----------------------------------------------------------------------
-- Parser example (`EchoExampleParser`).
--
-- `paren-nested` (`((` `)` `)`) and `paren-pair` (`(` `)` `(` `)`)
-- both have `parses ≡ true`. The Echo retains the distinction
-- (`echo-parse-nested≢echo-parse-pair`). The raw-Σ counter-program
-- below uses `proj₁` directly to recover the original `List Token`,
-- distinguishing the two echoes via the already-proven
-- `paren-nested≢paren-pair`. The Echo interface at affine mode would
-- refuse to export `proj₁`; this lemma exhibits exactly what would
-- leak if it didn't.

parser-sigma-distinguishes :
  Σ (Echo parses true → List Token)
    (λ g → g echo-parse-nested ≢ g echo-parse-pair)
parser-sigma-distinguishes = proj₁ , paren-nested≢paren-pair

----------------------------------------------------------------------
-- Provenance example (`EchoExampleProvenance`).
--
-- `row-with-prov-true` and `row-with-prov-false` project to the same
-- payload (`project ≡ 0`) but carry distinct provenance Booleans. The
-- Echo retains the provenance (`echo-prov-true≢echo-prov-false`). The
-- raw-Σ counter-program composes `prov` with `proj₁` to leak the
-- provenance Bool, distinguishing the two echoes via `true≢false`.

provenance-sigma-distinguishes :
  Σ (Echo project 0 → Bool)
    (λ g → g echo-prov-true ≢ g echo-prov-false)
provenance-sigma-distinguishes = prov ∘ proj₁ , true≢false

----------------------------------------------------------------------
-- Abstract-interpretation example (`EchoExampleAbsInt`).
--
-- `p1` and `p2` both abstract to `pos` under the 5-element sign
-- lattice (`α p1 ≡ α p2 ≡ pos`). The Echo retains the concrete
-- carrier (`echo-pos-p1≢echo-pos-p2`). The raw-Σ counter-program
-- uses `proj₁` to recover the concrete Carrier, distinguishing via
-- `p1≢p2`.

absint-sigma-distinguishes :
  Σ (Echo α pos → Carrier)
    (λ g → g echo-pos-p1 ≢ g echo-pos-p2)
absint-sigma-distinguishes = proj₁ , p1≢p2
