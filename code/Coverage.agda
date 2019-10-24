module Coverage where

open import Variables
open import Common
open import Homotopy
open import Poset

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

-- Note that the level for the index set of the family is required to be explicitly
-- provided.
Coverage : (ℓ₂ : Level) → Poset ℓ₀ ℓ₁ → Set (ℓ₀ ⊔ ℓ₁ ⊔ suc ℓ₂)
Coverage ℓ₂ P = (y : ∣ P ∣ₚ) → Sub ℓ₂ (Σ[ x ∈ ∣ P ∣ₚ ] x ⊑[ P ] y holds)

-- A site is a poset equipped with a coverage.
Site : (ℓ₀ ℓ₁ ℓ₂ : Level) → Set (suc ℓ₀ ⊔ suc ℓ₂)
Site ℓ₀ ℓ₁ ℓ₂ = Σ[ P ∈ (Poset ℓ₀ ℓ₂) ] Coverage ℓ₂ P

-- Locality à la Dragalin.
IsLocal : (S : Site ℓ₀ ℓ₁ ℓ₂) → Set (ℓ₀ ⊔ ℓ₂)
IsLocal {ℓ₂ = ℓ₂} (P , C) =
  (a b : ∣ P ∣ₚ) → (S : ↓[ P ] a) → S ε C a → b ⊑[ P ] a holds →
    Σ[ T ∈ ↓[ P ] b ] T ε (C b) → (t : ↓[ P ] a) →
      Σ[ s ∈ ↓[ P ] a ] (proj₁ t) ⊑[ P ] (proj₁ s) holds
