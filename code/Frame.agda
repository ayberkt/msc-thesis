module Frame where

open import Relation.Binary.PropositionalEquality using (_≡_)

Subset : Set → Set₁
Subset S = S → Set

record Poset : Set₁ where

  field
    A    : Set
    _⊑_  : A → A → Set

  field
    refl  : (x     : A) → x ⊑ x
    trans : (x y z : A) → x ⊑ y → y ⊑ z → x ⊑ z
    sym⁻¹ : (x y   : A) → x ⊑ y → y ⊑ x → x ≡ y

record Frame : Set₁ where

  field
    P   : Poset

  O   = Poset.A P
  _⊑_ = Poset._⊑_ P

  field
    𝟏   : O
    _⊓_ : O → O → O
    ⊔_  : Subset O → O

  field
    top    : (x   : O) → x ⊑ 𝟏
    ⊓-up₁  : (x y : O) → (x ⊓ y) ⊑ x
    ⊓-up₂  : (x y : O) → (x ⊓ y) ⊑ y
