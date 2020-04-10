{-# OPTIONS --without-K --cubical --safe #-}

module Family where

open import Basis

Sub : (ℓ₀ : Level) → Type ℓ₁ → Type (suc ℓ₀ ⊔ ℓ₁)
Sub ℓ A = Σ (Set ℓ) (λ I → I → A)

index : Sub ℓ₁ A → Type ℓ₁
index (I , _) = I

-- Application of a family over X to an index.
_€_ : (ℱ : Sub ℓ₀ A) → index ℱ → A
_€_ (_ , f) = f

infixr 7 _€_

-- Membership for families.
_ε_ : A → Sub ℓ₁ A → Type _
x ε S = Σ (index S) (λ i → (S € i) ≡ x)

-- Composition of a family with a function.
_⊚_ : {X : Type ℓ₀} {Y : Type ℓ₁} → (g : X → Y) → (ℱ : Sub ℓ₂ X) → Sub ℓ₂ Y
g ⊚ ℱ = (index ℱ) , g ∘ (_€_ ℱ)
