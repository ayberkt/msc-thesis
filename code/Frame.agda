module Frame where

open import Level
open import Relation.Binary.PropositionalEquality using (_≡_)

Sub : {ℓ : Level} → Set ℓ → Set (suc ℓ)
Sub {ℓ} S = S → Set ℓ

record Poset {ℓ : Level} : Set (suc ℓ) where

  field
    A    : Set ℓ
    _⊑_  : A → A → Set

  field
    refl  : (x     : A) → x ⊑ x
    trans : (x y z : A) → x ⊑ y → y ⊑ z → x ⊑ z
    sym⁻¹ : (x y   : A) → x ⊑ y → y ⊑ x → x ≡ y

record Frame {ℓ : Level} : Set (suc ℓ) where

  field
    P   : Poset {ℓ}

  O   = Poset.A P
  _⊑_ = Poset._⊑_ P

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

