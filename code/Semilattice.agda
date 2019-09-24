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

poset-of : {A : Set} → AlgMeetSemilatticeStr A → PosetStr A
poset-of {A} S = posetstr (λ x y → x ≡ x ∧ y) idem trans antisym is-prop
  where
    open AlgMeetSemilatticeStr S using (_∧_; true; idem; assoc; comm)
    trans : (x y z : A) → x ≡ (x ∧ y) → y ≡ (y ∧ z) → x ≡ (x ∧ z)
    trans x y z p q =
      begin
        x              ≡⟨ p                             ⟩
        (x ∧ y)        ≡⟨ cong (λ k → x ∧ k) q          ⟩
        (x ∧ (y ∧ z))  ≡⟨ assoc x y z                   ⟩
        ((x ∧ y) ∧ z)  ≡⟨ cong (λ k → k ∧ z) (sym p)    ⟩
        (x ∧ z)
      ∎
    antisym : (x y : A) → x ≡ (x ∧ y) → y ≡ (y ∧ x) → x ≡ y
    antisym x y p q =
      begin
        x              ≡⟨ p                             ⟩
        x ∧ y          ≡⟨ cong (λ k → k ∧ y) p          ⟩
        (x ∧ y) ∧ y    ≡⟨ cong (λ k → k ∧ y) (comm x y) ⟩
        (y ∧ x) ∧ y    ≡⟨ cong (λ k → k ∧ y) (sym q)    ⟩
        y ∧ y          ≡⟨ sym (idem y)                  ⟩
        y
      ∎
    is-prop : (x y : A) → Homotopy.isprop (x ≡ (x ∧ y))
    is-prop x y = Homotopy.UIP
