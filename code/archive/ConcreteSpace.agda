module ConcreteSpace where

import Relation.Binary.PropositionalEquality as Eq

open        Eq           using (_≡_; refl)

open import Subset
open import Function     using (flip)
open import Data.Unit    using (⊤)
open import Data.Nat     using (ℕ)
open import Data.Integer using (ℤ)
open import Data.Product using (Σ-syntax; _×_)

record ConcreteSpace : Set₁ where
  -- Data.
  field
    X   : Set
    S   : Set
    _⊩_ : X → Subset S

  S1 : Subset S
  S1 = λ _ → ⊤

  _⊩⋆_ : X → Subset S → Set
  x ⊩⋆ U = Σ[ b ∈ S ] (U b × x ⊩ b)

  ext : S → Subset X
  ext = flip _⊩_

  ext⋆ : Subset S → Subset X
  ext⋆ U = λ x → Σ[ a ∈ S ] (a ∈ U × ext a x)

  _↓_ : S → S → Subset S
  a ↓ b = λ c → (ext c ⊆ ext a) × (ext c ⊆ ext b)

  -- Laws.
  field
    B₁ : (x   : X) → x ⊩⋆ S1
    B₂ : (a b : S) → ext a ∩ ext b ≡ ext⋆ (a ↓ b)

data ℕ⁺ : Set where
  one : ℕ⁺
  suc : ℕ⁺ → ℕ⁺

ℚ : Set
ℚ = ℤ × ℕ⁺

ℚ⁺ : Set
ℚ⁺ = ℕ × ℕ⁺

