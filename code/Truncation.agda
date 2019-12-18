{-# OPTIONS --without-K --cubical --safe #-}

module Truncation where

open import Basis

record TruncationExists : Setω where
  field
    ∥_∥     : Set ℓ → Set ℓ
    ∥∥-prop : (X : Set ℓ) → IsProp ∥ X ∥
    ∣_∣     : A → ∥ A ∥
    ∥∥-rec  : {A A₀ : Type ℓ} → IsProp A₀ → (A → A₀) → ∥ A ∥ → A₀
