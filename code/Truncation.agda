{-# OPTIONS --without-K #-}

module Truncation where

open import Common
open import Homotopy

private
  variable
    ℓ ℓ′ : Level

record TruncationExists : Setω where
  field
    ∥_∥     : Set ℓ → Set ℓ
    ∥∥-prop : (X : Set ℓ) → IsProp ∥ X ∥
    ∣_∣     : {X : Set ℓ} → X → ∥ X ∥
    ∥∥-rec  : {X : Set ℓ} {P : Set ℓ′} → IsProp P → (X → P) → ∥ X ∥ → P
