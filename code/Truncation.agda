{-# OPTIONS --without-K --cubical --safe #-}

module Truncation where

open import Common
open import Basis

record TruncationExists : Setω where
  field
    ∥_∥     : Set ℓ → Set ℓ
    ∥∥-prop : (X : Set ℓ) → IsProp ∥ X ∥
    ∣_∣     : A → ∥ A ∥
    ∥∥-rec  : {P : Set ℓ₁} → IsProp P → (A → P) → ∥ A ∥ → P
