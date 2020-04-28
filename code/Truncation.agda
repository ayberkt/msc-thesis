{-# OPTIONS --without-K --cubical --safe #-}

module Truncation where

open import Basis

data ∥_∥ (A : Type ℓ) : Type ℓ where
  ∣_∣    : A → ∥ A ∥
  squash : (x y : ∥ A ∥) → x ≡ y

∥∥-prop : (A : Type ℓ) → isProp ∥ A ∥
∥∥-prop _ = squash

∥∥-rec : {X Y : Type ℓ} → isProp Y → (X → Y) → ∥ X ∥ → Y
∥∥-rec Y-prop f ∣ x ∣                = f x
∥∥-rec Y-prop f (squash ∣x∣₀ ∣x∣₁ i) =
  Y-prop (∥∥-rec Y-prop f ∣x∣₀) (∥∥-rec Y-prop f ∣x∣₁) i
