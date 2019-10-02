{-# OPTIONS --without-K #-}

module AlgebraicProperties where

open import Common

module _ {ℓ ℓ′ : Level} {X : Set ℓ} (_⊑_ : X → X → Set ℓ′) where

  IsReflexive : Set (ℓ ⊔ ℓ′)
  IsReflexive = (x : X) → x ⊑ x

  IsTransitive : Set (ℓ ⊔ ℓ′)
  IsTransitive = (x y z : X) → x ⊑ y → y ⊑ z → x ⊑ z

  IsAntisym : Set (ℓ ⊔ ℓ′)
  IsAntisym = (x y : X) → x ⊑ y → y ⊑ x → x ≡ y
