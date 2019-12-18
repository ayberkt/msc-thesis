```
{-# OPTIONS --without-K --cubical --safe #-}

module Main where

open import Basis
open import Poset
open import Frame
```

## Truncation

```
open import Truncation

data ∥_∥ (A : Type ℓ) : Type ℓ where
  ∣_∣    : A → ∥ A ∥
  squash : (x y : ∥ A ∥) → x ≡ y

pt : TruncationExists
pt = record { ∥_∥ = ∥_∥ ; ∥∥-prop = λ _ → squash ; ∣_∣ = ∣_∣ ; ∥∥-rec = ∥∥-rec }
  where
    ∥∥-rec : {X Y : Type ℓ} → IsProp Y → (X → Y) → ∥ X ∥ → Y
    ∥∥-rec Y-prop f ∣ x ∣                = f x
    ∥∥-rec Y-prop f (squash ∣x∣₀ ∣x∣₁ i) =
      Y-prop (∥∥-rec Y-prop f ∣x∣₀) (∥∥-rec Y-prop f ∣x∣₁) i

open import Nucleus pt
```
