{-# OPTIONS --without-K --cubical --safe #-}

module Family where

open import Basis

Sub : (ℓ₀ : Level) → Set ℓ₁ → Set (suc ℓ₀ ⊔ ℓ₁)
Sub ℓ A = Σ (Set ℓ) (λ I → I → A)

index : Sub ℓ₁ A → Set ℓ₁
index (I , _) = I

-- Application of a family over X to an index.
_€_ : (ℱ : Sub ℓ₀ A) → index ℱ → A
_€_ (_ , f) = f

infixr 7 _€_

-- Membership for families.
_ε_ : A → Sub ℓ₁ A → Set _
x ε S = Σ (index S) (λ i → (S € i) ≡ x)

-- Composition of a family with a function.
_⊚_ : {X : Set ℓ₀} {Y : Set ℓ₁} → (g : X → Y) → (ℱ : Sub ℓ₂ X) → Sub ℓ₂ Y
g ⊚ ℱ = (index ℱ) , g ∘ (_€_ ℱ)
