{-# OPTIONS --without-K #-}

open import Common
open import Homotopy

module AlgebraicProperties {ℓ ℓ′ : Level}
                           {X : Set ℓ}
                           (X-set : IsSet X)
                           (_⊑_ : X → X → Ω ℓ′) where

  IsReflexive : Ω (ℓ ⊔ ℓ′)
  IsReflexive = ((x : X) → (x ⊑ x) holds) , ∏-resp-prop λ x → proj₂ (x ⊑ x)

  IsTransitive : Ω (ℓ ⊔ ℓ′)
  IsTransitive = φ , φ-prop
    where
      φ      : Set (ℓ ⊔ ℓ′)
      φ      = ((x y z : X) → (x ⊑ y) holds → (y ⊑ z) holds → (x ⊑ z) holds)
      φ-prop : IsProp φ
      φ-prop = ∏-resp-prop λ x → ∏-resp-prop λ y → ∏-resp-prop λ z →
               ∏-resp-prop λ p → ∏-resp-prop λ q → proj₂ (x ⊑ z)

  IsAntisym : Ω (ℓ ⊔ ℓ′)
  IsAntisym = φ , φ-prop
    where
      φ      : Set (ℓ ⊔ ℓ′)
      φ      = ((x y : X) → (x ⊑ y) holds → (y ⊑ x) holds → x ≡ y)
      φ-prop : IsProp φ
      φ-prop = ∏-resp-prop λ x → ∏-resp-prop λ y →
               ∏-resp-prop λ p → ∏-resp-prop λ q → X-set x y
