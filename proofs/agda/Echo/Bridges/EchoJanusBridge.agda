{-# OPTIONS --safe --without-K #-}

-- Echo-JanusKey Bridge (Working Version)
--
-- Core bridge between echo types and JanusKey reversibility concepts.
--
-- Structural mirror of the canonical Idris2 OpKind ABI in
-- hyperpolymath/januskey:src/abi/Types.idr. The earlier 4-variant
-- local enum (Create / Delete / Modify / Move) had already drifted
-- from canon: the canonical surface has Copy (not Create), plus
-- Obliterate and three key-management ops (KeyGen / KeyRotate /
-- KeyRevoke). Theorems remain trivial (each op maps to tt : ⊤,
-- every *-preserves-echo theorem is `λ e → e`); no content-bridge
-- claim is asserted, pending januskey/PROOF-NEEDS.md.

module Echo.Bridges.EchoJanusBridge where

open import Echo.Core
open import Data.Unit.Base using (⊤; tt)
open import Data.Product.Base using (Σ; _,_; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

----------------------------------------------------------------------------
-- Section 1: Core Bridge Concepts
----------------------------------------------------------------------------

-- JanusKey operation kinds — mirrors hyperpolymath/januskey
-- src/abi/Types.idr `OpKind` (8 variants). Five file ops + three
-- key-management ops.
data OpKind : Set where
  Copy       : OpKind
  Move       : OpKind
  Delete     : OpKind
  Modify     : OpKind
  Obliterate : OpKind
  KeyGen     : OpKind
  KeyRotate  : OpKind
  KeyRevoke  : OpKind

-- File-op / key-op predicates: structural mirror of januskey's
-- IsFileOp / IsKeyOp partitioning of OpKind.
data IsFileOp : OpKind → Set where
  isFileCopy       : IsFileOp Copy
  isFileMove       : IsFileOp Move
  isFileDelete     : IsFileOp Delete
  isFileModify     : IsFileOp Modify
  isFileObliterate : IsFileOp Obliterate

data IsKeyOp : OpKind → Set where
  isKeyKeyGen    : IsKeyOp KeyGen
  isKeyKeyRotate : IsKeyOp KeyRotate
  isKeyKeyRevoke : IsKeyOp KeyRevoke

-- Function from operations to unit (for echo type)
janus-to-unit : OpKind → ⊤
janus-to-unit _ = tt

-- Echo types for Janus operations
JanusEcho : OpKind → Set
JanusEcho op = Echo janus-to-unit tt

-- Core echo instances (one per OpKind constructor)
copy-echo : JanusEcho Copy
copy-echo = echo-intro janus-to-unit Copy

move-echo : JanusEcho Move
move-echo = echo-intro janus-to-unit Move

delete-echo : JanusEcho Delete
delete-echo = echo-intro janus-to-unit Delete

modify-echo : JanusEcho Modify
modify-echo = echo-intro janus-to-unit Modify

obliterate-echo : JanusEcho Obliterate
obliterate-echo = echo-intro janus-to-unit Obliterate

keygen-echo : JanusEcho KeyGen
keygen-echo = echo-intro janus-to-unit KeyGen

keyrotate-echo : JanusEcho KeyRotate
keyrotate-echo = echo-intro janus-to-unit KeyRotate

keyrevoke-echo : JanusEcho KeyRevoke
keyrevoke-echo = echo-intro janus-to-unit KeyRevoke

----------------------------------------------------------------------------
-- Section 2: Reversibility Properties
----------------------------------------------------------------------------

-- Each operation has echo witnesses
ReversibleCopy : JanusEcho Copy
ReversibleCopy = copy-echo

ReversibleMove : JanusEcho Move
ReversibleMove = move-echo

ReversibleDelete : JanusEcho Delete
ReversibleDelete = delete-echo

ReversibleModify : JanusEcho Modify
ReversibleModify = modify-echo

ReversibleObliterate : JanusEcho Obliterate
ReversibleObliterate = obliterate-echo

ReversibleKeyGen : JanusEcho KeyGen
ReversibleKeyGen = keygen-echo

ReversibleKeyRotate : JanusEcho KeyRotate
ReversibleKeyRotate = keyrotate-echo

ReversibleKeyRevoke : JanusEcho KeyRevoke
ReversibleKeyRevoke = keyrevoke-echo

----------------------------------------------------------------------------
-- Section 3: Core Bridge Theorems
----------------------------------------------------------------------------

-- Each operation preserves echo structure (trivial: identity on echoes).
copy-preserves-echo : JanusEcho Copy → JanusEcho Copy
copy-preserves-echo e = e

move-preserves-echo : JanusEcho Move → JanusEcho Move
move-preserves-echo e = e

delete-preserves-echo : JanusEcho Delete → JanusEcho Delete
delete-preserves-echo e = e

modify-preserves-echo : JanusEcho Modify → JanusEcho Modify
modify-preserves-echo e = e

obliterate-preserves-echo : JanusEcho Obliterate → JanusEcho Obliterate
obliterate-preserves-echo e = e

keygen-preserves-echo : JanusEcho KeyGen → JanusEcho KeyGen
keygen-preserves-echo e = e

keyrotate-preserves-echo : JanusEcho KeyRotate → JanusEcho KeyRotate
keyrotate-preserves-echo e = e

keyrevoke-preserves-echo : JanusEcho KeyRevoke → JanusEcho KeyRevoke
keyrevoke-preserves-echo e = e

----------------------------------------------------------------------------
-- Section 4: Integration with Standard Echo Types
----------------------------------------------------------------------------

-- Bridge to standard echo types (Copy chosen as the canonical
-- representative — every JanusEcho is definitionally Echo janus-to-unit tt).
to-standard-echo : JanusEcho Copy → Echo janus-to-unit tt
to-standard-echo echo = echo

from-standard-echo : Echo janus-to-unit tt → JanusEcho Copy
from-standard-echo echo = echo

-- Echo composition preserves structure
echo-composition : JanusEcho Copy → JanusEcho Delete → Echo janus-to-unit tt
echo-composition e1 e2 = e1

----------------------------------------------------------------------------
-- Section 5: Main Bridge Theorem
----------------------------------------------------------------------------

-- Main result: every OpKind constructor has an echo witness.
JanusEchoBridgeTheorem :
  JanusEcho Copy × JanusEcho Move × JanusEcho Delete × JanusEcho Modify
  × JanusEcho Obliterate × JanusEcho KeyGen × JanusEcho KeyRotate × JanusEcho KeyRevoke
JanusEchoBridgeTheorem =
  copy-echo , move-echo , delete-echo , modify-echo
  , obliterate-echo , keygen-echo , keyrotate-echo , keyrevoke-echo

-- Alternative formulation: each operation is reversible (identity-preserving).
JanusReversibilityTheorem :
  (JanusEcho Copy       → JanusEcho Copy)       ×
  (JanusEcho Move       → JanusEcho Move)       ×
  (JanusEcho Delete     → JanusEcho Delete)     ×
  (JanusEcho Modify     → JanusEcho Modify)     ×
  (JanusEcho Obliterate → JanusEcho Obliterate) ×
  (JanusEcho KeyGen     → JanusEcho KeyGen)     ×
  (JanusEcho KeyRotate  → JanusEcho KeyRotate)  ×
  (JanusEcho KeyRevoke  → JanusEcho KeyRevoke)
JanusReversibilityTheorem =
  copy-preserves-echo , move-preserves-echo
  , delete-preserves-echo , modify-preserves-echo
  , obliterate-preserves-echo , keygen-preserves-echo
  , keyrotate-preserves-echo , keyrevoke-preserves-echo

----------------------------------------------------------------------------
-- Section 6: Practical Examples
----------------------------------------------------------------------------

-- Example 1: File copy with echo provenance
file-copy-example : JanusEcho Copy
file-copy-example = copy-echo

-- Example 2: File move with echo provenance
file-move-example : JanusEcho Move
file-move-example = move-echo

-- Example 3: File deletion with echo provenance
file-deletion-example : JanusEcho Delete
file-deletion-example = delete-echo

-- Example 4: File modification with echo provenance
file-modification-example : JanusEcho Modify
file-modification-example = modify-echo

-- Example 5: File obliteration with echo provenance
file-obliteration-example : JanusEcho Obliterate
file-obliteration-example = obliterate-echo

-- Example 6: Key generation with echo provenance
keygen-example : JanusEcho KeyGen
keygen-example = keygen-echo

-- Example 7: Key rotation with echo provenance
keyrotate-example : JanusEcho KeyRotate
keyrotate-example = keyrotate-echo

-- Example 8: Key revocation with echo provenance
keyrevoke-example : JanusEcho KeyRevoke
keyrevoke-example = keyrevoke-echo

-- Example 9: Composite operation sequence
composite-operation : JanusEcho Copy → JanusEcho Delete → Echo janus-to-unit tt
composite-operation copy delete = copy

----------------------------------------------------------------------------
-- Section 7: Integration Examples
----------------------------------------------------------------------------

-- Integration with standard echo types
standard-echo-integration : Echo janus-to-unit tt → JanusEcho Copy
standard-echo-integration echo = echo

-- Round-trip preservation
round-trip-preservation : ∀ echo → to-standard-echo (from-standard-echo echo) ≡ echo
round-trip-preservation echo = refl

----------------------------------------------------------------------------
-- Summary
----------------------------------------------------------------------------

-- This bridge demonstrates that echo types can model the canonical
-- januskey OpKind surface:
-- 1. Each OpKind constructor maps to a unit value via echo types
-- 2. Echo types preserve operation identity through reversibility
-- 3. The bridge provides provenance tracking for reversible operations
-- 4. Standard echo types integrate seamlessly with operation-specific echoes
-- 5. The IsFileOp / IsKeyOp predicates mirror januskey's partition of OpKind
--    into file ops (Copy / Move / Delete / Modify / Obliterate) and key
--    ops (KeyGen / KeyRotate / KeyRevoke)

-- The implementation uses the core Echo type correctly with:
-- - janus-to-unit : OpKind → ⊤ as the function f
-- - tt : ⊤ as the target value y
-- - Echo janus-to-unit tt as the fiber type
-- This maintains the theoretical connection while avoiding universe issues.

-- Theorems remain trivial (each *-preserves-echo is `λ e → e`); no
-- content-bridge claim is asserted, pending januskey/PROOF-NEEDS.md.
