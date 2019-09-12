module Semilattice where

open import Poset
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong) renaming (trans to _·_)

record MeetSemilattice : Set₁ where
  field
    P   : Poset

  open Poset.Poset P using (A; _⊑_)

  field
    𝟏   : A
    _⊓_ : A → A → A

  -- Laws.
  field
    𝟏-top      : (x     : A) → x ⊑ 𝟏
    𝟏-lower₁   : (x y   : A) → (x ⊓ y) ⊑ x
    𝟏-lower₂   : (x y   : A) → (x ⊓ y) ⊑ y
    𝟏-greatest : (x y z : A) → z ⊑ x → z ⊑ y → z ⊑ (x ⊓ y)

record AlgebraicMeetSemilattice : Set₁ where
  constructor alg-meet-semilattice

  field
    A        : Set
    _∧_      : A → A → A
    true     : A

  field
    comm     : (x y   : A) → (x ∧ y) ≡ (y ∧ x)
    assoc    : (x y z : A) → x ∧ (y ∧ z) ≡ (x ∧ y) ∧ z
    right-id : (x     : A) → x ≡ x ∧ true
    idem     : (x     : A) → x ≡ x ∧ x

orderification : AlgebraicMeetSemilattice → MeetSemilattice
orderification (alg-meet-semilattice A _∧_ true comm assoc right-id idem) =
  record
    { P = record { A = A
                 ; _⊑_ = λ x y → x ≡ x ∧ y
                 ; refl = idem
                 ; trans = λ x y z p q → {!!} ; sym⁻¹ = {!!} }
    ; 𝟏     = true
    ; _⊓_   = _∧_
    ; 𝟏-top = right-id
    ; 𝟏-lower₁ = λ x y → comm x y · (cong (_∧_ y) (idem x) · (assoc y x x · cong (λ k → k ∧ x) (comm y x)))
    ; 𝟏-lower₂ = {!!}
    ; 𝟏-greatest = {!!}
    }
