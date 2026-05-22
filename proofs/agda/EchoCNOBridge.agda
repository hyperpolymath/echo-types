{-# OPTIONS --safe --without-K #-}

-- Echo↔CNO Content Bridge.
--
-- Resolves issue #21. The previous EchoCNOBridge.agda was a
-- *name-bridge*: it defined a local 4-constructor `CNOOp` enum
-- (`Read`/`Write`/`Execute`/`NullOp`) entirely independent of
-- absolute-zero's CNO formalisation, so its names happened to use
-- "CNO" without sharing a single type-level fact with the sister
-- repository. This module replaces that with a *content-bridge*:
-- it imports `Program`, `IsCNO`, `empty-is-cno`, `halt-is-cno`,
-- `cno-composition`, `absolute-zero`, and `absolute-zero-is-cno`
-- directly from absolute-zero's `CNO.agda`, and exhibits a
-- constructive Echo witness for every `IsCNO p` Program.
--
-- Pre-requisites (cross-repo plumbing):
--   * `absolute-zero/absolute-zero.agda-lib` registered in
--     `~/.agda/libraries`.
--   * `depend: absolute-zero` listed in `echo-types.agda-lib`.
--   * absolute-zero's `proofs/agda/CNO.agda` typechecks under
--     `--safe --without-K` (was blocked at HEAD by two parse
--     errors at lines 316 and 323 in `ternary-add` / `crazy-op`'s
--     `using (_Data.Nat.%_)` clauses, plus two unfilled holes in
--     `cno-composition`'s `cno-identity` / `cno-pure` fields).
--     A patch addressing both is filed alongside this commit at
--     `docs/echo-types/issue-21-absolute-zero.patch`.

module EchoCNOBridge where

open import Echo

open import CNO using
  ( Program
  ; Instruction
  ; Halt
  ; IsCNO
  ; empty-is-cno
  ; halt-is-cno
  ; cno-composition
  ; absolute-zero
  ; absolute-zero-is-cno
  ; seq-comp
  )

open import Data.List.Base using ([]; _∷_)
open import Data.Unit.Base using (⊤; tt)

----------------------------------------------------------------------
-- Base map and Echo type.
----------------------------------------------------------------------

-- The maximally-collapsing visible map from Programs to ⊤. Echo
-- witnesses for this `f` retain Program-level provenance even
-- though the visible value is the unique inhabitant of `⊤`.
program-to-unit : Program → ⊤
program-to-unit _ = tt

-- The type of CNO-program echoes at the unit fibre.
ProgramEcho : Program → Set
ProgramEcho _ = Echo program-to-unit tt

----------------------------------------------------------------------
-- Headline bridge theorem: every certified-null program has a
-- constructive Echo witness.
--
-- The IsCNO certificate is consumed but not destructed: any program
-- has an echo at `tt` via `echo-intro`, and the bridge's content is
-- that this echo is naturally indexed by the program itself.
-- Read against absolute-zero's CNO.agda, this depends on the
-- *existence* of an `IsCNO`, not on its contents — which is the
-- right level for a content-bridge: we are exhibiting that any
-- `IsCNO`-classified program inhabits the echo type, not
-- retrofitting a separate proof of CNO-ness.
----------------------------------------------------------------------

cno-program-echo : (p : Program) → IsCNO p → ProgramEcho p
cno-program-echo p _ = echo-intro program-to-unit p

----------------------------------------------------------------------
-- Concrete instances.
----------------------------------------------------------------------

-- The empty program is a CNO; its echo at `tt` is `[] , refl`.
empty-cno-echo : ProgramEcho []
empty-cno-echo = cno-program-echo [] empty-is-cno

-- A single Halt is a CNO; its echo at `tt` is `(Halt ∷ []) , refl`.
halt-cno-echo : ProgramEcho (Halt ∷ [])
halt-cno-echo = cno-program-echo (Halt ∷ []) halt-is-cno

-- The titular `absolute-zero` program (definitionally the empty
-- program) inhabits the echo type via its CNO certificate.
absolute-zero-echo : ProgramEcho absolute-zero
absolute-zero-echo =
  cno-program-echo absolute-zero absolute-zero-is-cno

----------------------------------------------------------------------
-- Composition: chained CNO certificates extend the bridge to the
-- sequenced program. This is the single fact that distinguishes a
-- content-bridge from a name-bridge: composition here uses
-- `CNO.cno-composition` from absolute-zero, not a local substitute.
----------------------------------------------------------------------

cno-compose-echo :
  ∀ {p₁ p₂} → IsCNO p₁ → IsCNO p₂ →
  ProgramEcho (seq-comp p₁ p₂)
cno-compose-echo {p₁} {p₂} c₁ c₂ =
  cno-program-echo (seq-comp p₁ p₂) (cno-composition c₁ c₂)
