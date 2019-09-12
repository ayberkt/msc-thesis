module Poset where

open import Relation.Binary.PropositionalEquality using (_≡_)
open import Level

record Poset {ℓ : Level} : Set (suc ℓ) where

  field
    A    : Set ℓ
    _⊑_  : A → A → Set

  field
    refl  : (x     : A) → x ⊑ x
    trans : (x y z : A) → x ⊑ y → y ⊑ z → x ⊑ z
    sym⁻¹ : (x y   : A) → x ⊑ y → y ⊑ x → x ≡ y
