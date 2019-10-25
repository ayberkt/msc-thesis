{-# OPTIONS --without-K #-}

module Family where

open import Variables
open import Common

Sub : (ℓ : Level) → Set ℓ′ → Set (ℓ′ ⊔ suc ℓ)
Sub ℓ A = Σ[ I ∈ Set ℓ ] (I → A)

index : {X : Set ℓ} → Sub ℓ′ X → Set ℓ′
index (I , _) = I

-- Application of a family over X to an index.
_€_ : {X : Set ℓ} → (ℱ : Sub ℓ′ X) → index ℱ → X
_€_ (_ , f) = f

infixr 7 _€_

-- Membership for families.
_ε_ : {X : Set ℓ} → X → Sub ℓ′ X → Set (ℓ ⊔ ℓ′)
x ε S = Σ[ i ∈ index S ] (S € i) ≡ x

-- Composition of a family with a function.
_⊚_ : {X : Set ℓ₀} {Y : Set ℓ₁} → (g : X → Y) → (ℱ : Sub ℓ₂ X) → Sub ℓ₂ Y
g ⊚ ℱ = (index ℱ) , g ∘ (_€_ ℱ)
