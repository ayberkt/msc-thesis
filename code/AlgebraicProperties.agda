{-# OPTIONS --without-K --cubical --safe #-}

open import Basis

module AlgebraicProperties {ℓ ℓ′ : Level}
                           {X : Set ℓ}
                           (X-set : IsSet X)
                           (_⊑_ : X → X → Ω ℓ′) where

  IsReflexive : Ω (ℓ ⊔ ℓ′)
  IsReflexive = ((x : X) → (x ⊑ x) is-true) , ∏-prop (λ x → is-true-prop (x ⊑ x))

  IsTransitive : Ω (ℓ ⊔ ℓ′)
  IsTransitive = φ , φ-prop
    where
      φ      : Set (ℓ ⊔ ℓ′)
      φ      = ((x y z : X) → (x ⊑ y) is-true → (y ⊑ z) is-true → (x ⊑ z) is-true)
      φ-prop : IsProp φ
      φ-prop = ∏-prop λ x → ∏-prop λ y → ∏-prop λ z
             → ∏-prop (λ _ → ∏-prop λ _ → is-true-prop (x ⊑ z))

  IsAntisym : Ω (ℓ ⊔ ℓ′)
  IsAntisym = φ , φ-prop
    where
      φ      : Set (ℓ ⊔ ℓ′)
      φ      = ((x y : X) → (x ⊑ y) is-true → (y ⊑ x) is-true → x ≡ y)
      φ-prop : IsProp φ
      φ-prop = ∏-prop λ x → ∏-prop λ y →
               ∏-prop λ p → ∏-prop λ q → X-set x y
