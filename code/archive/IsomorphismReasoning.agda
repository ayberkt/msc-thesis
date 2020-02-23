{-# OPTIONS --allow-unsolved-metas #-}

module IsomorphismReasoning where

open import Common
open import Homotopy

private
  variable
    ℓ ℓ′ ℓ₀ ℓ₁ ℓ₂ : Level

∘-equiv : {X : Set ℓ₀} {Y : Set ℓ₁} {Z : Set ℓ₂} {f : X → Y} {g : Y → Z}
        → isequiv g → isequiv f → isequiv (g ∘ f)
∘-equiv {ℓ₀} {ℓ₁} {ℓ₂} {X} {Y} {Z} {f} {g} i j =
  {!!}

_●_ : {X : Set ℓ₀} {Y : Set ℓ₁} {Z : Set ℓ₂} → X ≃ Y → Y ≃ Z → X ≃ Z
(f , d) ● (f′ , e) = (f′ ∘ f) , ∘-equiv e d

_≃⟨_⟩_ : (X : Set ℓ₀) {Y : Set ℓ₁} {Z : Set ℓ₂} → X ≃ Y → Y ≃ Z → X ≃ Z
_ ≃⟨ d ⟩ e = d ● e

_■ : (X : Set ℓ) → X ≃ X
_■ = id-≃

infixr  0 _≃⟨_⟩_
infix   1 _■

-- _≃⟨_⟩_ :
