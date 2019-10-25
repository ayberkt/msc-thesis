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

Covering : (ℓ : Level) → (P : Poset ℓ₀ ℓ₁) → ∣ P ∣ₚ → Set (ℓ₀ ⊔ ℓ₁ ⊔ suc ℓ)
Covering ℓ P a = Sub ℓ (↓[ P ] a)

-- Note that the level for the index set of the family is required to be explicitly
-- provided.
Coverage : (ℓ : Level) → Poset ℓ₀ ℓ₁ → Set (ℓ₀ ⊔ ℓ₁ ⊔ suc ℓ)
Coverage ℓ P = (a : ∣ P ∣ₚ) → Sub ℓ (Covering ℓ P a)

-- A site is a poset equipped with a coverage.
Site : (ℓ₀ ℓ₁ ℓ₂ : Level) → Set (suc ℓ₀ ⊔ suc ℓ₁ ⊔ suc ℓ₂)
Site ℓ₀ ℓ₁ ℓ₂ = Σ[ P ∈ (Poset ℓ₀ ℓ₁) ] Coverage ℓ₂ P

-- Locality à la Dragalin.
IsLocal : (S : Site ℓ₀ ℓ₁ ℓ₂) → Set (ℓ₀ ⊔ ℓ₁ ⊔ suc ℓ₂)
IsLocal {ℓ₂ = ℓ₂} (P , Cov) =
  (a b : ∣ P ∣ₚ) → b ⊑[ P ] a holds →
    (S : Covering ℓ₂ P a) → S ε Cov a →
      Σ[ T ∈ Covering ℓ₂ P b ] (T ε Cov b → (t : ↓[ P ] b) → t ε T →
        Σ[ s ∈ ↓[ P ] a ] (s ε S → (proj₁ t) ⊑[ P ] (proj₁ s) holds))
