module Semilattice where

open import Poset
import Relation.Binary.PropositionalEquality as Eq
open        Eq using (_≡_; refl; cong; sym) renaming (trans to _·_)
open Eq.≡-Reasoning
open import Data.Product using (proj₁; proj₂)
import Homotopy

record MeetSemilatticeStr (P : Poset) : Set where
  open PosetStr (proj₂ P) using (_⊑_)
  A = proj₁ P

  field
    𝟏   : A
    _⊓_ : A → A → A

  -- Laws.
  field
    𝟏-top      : (x     : A) → x ⊑ 𝟏
    𝟏-lower₁   : (x y   : A) → (x ⊓ y) ⊑ x
    𝟏-lower₂   : (x y   : A) → (x ⊓ y) ⊑ y
    𝟏-greatest : (x y z : A) → z ⊑ x → z ⊑ y → z ⊑ (x ⊓ y)

record AlgMeetSemilatticeStr (A : Set) : Set where
  field
    _∧_      : A → A → A
    true     : A

  field
    comm     : (x y   : A) → (x ∧ y) ≡ (y ∧ x)
    assoc    : (x y z : A) → x ∧ (y ∧ z) ≡ (x ∧ y) ∧ z
    right-id : (x     : A) → x ≡ x ∧ true
    idem     : (x     : A) → x ≡ x ∧ x

