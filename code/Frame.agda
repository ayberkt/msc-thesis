module Frame where

open import Level
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Product                          using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Poset

Sub : {ℓ : Level} → Set ℓ → Set (suc ℓ)
Sub {ℓ} A = Σ[ I ∈ Set ℓ ] (I → A)

record Frame {ℓ : Level} : Set (suc ℓ) where

  field
    P   : Poset {ℓ}

  O   = proj₁ P
  _⊑_ = PosetStr._⊑_ (proj₂ P)

  field
    𝟏   : O
    _⊓_ : O → O → O
    ⊔_  : Sub O → O

  field
    top    : (x     : O)     → x ⊑ 𝟏
    ⊓-low₁ : (x y   : O)     → (x ⊓ y) ⊑ x
    ⊓-low₂ : (x y   : O)     → (x ⊓ y) ⊑ y
    ⊓-max  : (x y z : O)     → z ⊑ x → z ⊑ y → z ⊑ (x ⊓ y)
    ⊔-up   : (S     : Sub O) → (o : O) → o ⊑ (⊔ S)
    ⊔-min  : (S     : Sub O) → (z : O) → ((o : O) → o ⊑ z) → (⊔ S) ⊑ z

_─f→_ : {ℓ : Level} {A B : Set ℓ}
      → Frame {ℓ} → Frame {ℓ} → Set (suc ℓ)
F₀ ─f→ F₁ =
  let
     open Frame F₀ using () renaming (P to P₀; _⊓_ to _⊓₀_; ⊔_ to ⊔₀_; 𝟏 to 𝟏₀)
     open Frame F₁ using () renaming (P to P₁; _⊓_ to _⊓₁_; ⊔_ to ⊔₁_; 𝟏 to 𝟏₁)
     A₀  = proj₁ P₀
     A₁  = proj₁ P₁
     _$_ = proj₁
   in
     Σ[ m ∈ ((proj₂ P₀) ─m→ (proj₂ P₁)) ]
     m $ 𝟏₀ ≡ 𝟏₁
     ×
     ((x y : A₀) → m $ (x ⊓₀ y) ≡ (m $ x) ⊓₁ (m $ y))
     ×
     ((ℱ : Sub A₀) → m $ (⊔₀ ℱ) ≡ (⊔₁ (proj₁ ℱ , λ i → m $ (proj₂ ℱ i))))
