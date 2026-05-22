{-# OPTIONS --safe --without-K #-}

-- Compatibility Wrapper
-- This module exists solely for import stability.
-- It is a transitional surface to prevent breaking downstream dependencies.

module Echo where

open import Echo.Core public
