module Poset where

open import Relation.Binary.PropositionalEquality using (_≡_; sym)
            renaming (cong to ap; subst to transport; trans to _·_)
open import Data.Product using (Σ; Σ-syntax; proj₁; proj₂; _,_; _×_)
open import Function     using (id; _∘_)
open import Level
open import Homotopy

_$_ : {ℓ ℓ′ : Level} {A : Set ℓ} {B : A → Set ℓ′} → Σ A B → A
_$_ = proj₁

record PosetStr {ℓ : Level} (A : Set ℓ) : Set (suc ℓ) where
  constructor posetstr

  -- Data.
  field
    _⊑_  : A → A → Set ℓ

  -- Homotopy structure.
  field
    ⊑-set : (x y : A) → IsProp (x ⊑ y)
    A-set : IsSet A

  -- Laws.
  field
    refl  : (x     : A) → x ⊑ x
    trans : (x y z : A) → x ⊑ y → y ⊑ z → x ⊑ z
    sym⁻¹ : (x y   : A) → x ⊑ y → y ⊑ x → x ≡ y

Poset : {ℓ : Level} → Set (suc ℓ)
Poset {ℓ} = Σ[ A ∈ Set ℓ ] (PosetStr A)

-- Monotonic functions.
_─m→_ : {ℓ : Level} {A B : Set ℓ} → PosetStr A → PosetStr B → Set ℓ
_─m→_ {_} {A} {B} P₁ P₂ =
  let
     open PosetStr P₁ using () renaming (_⊑_ to _⊑₁_)
     open PosetStr P₂ using () renaming (_⊑_ to _⊑₂_)
   in
     Σ[ f ∈ (A → B) ] ((x y : A) → x ⊑₁ y → (f x) ⊑₂ (f y))

-- Monotonic function composition.
_∘m_ : {A B C : Set} {P₁ : PosetStr A} {P₂ : PosetStr B} {P₃ : PosetStr C}
      → (P₂ ─m→ P₃)
      → (P₁ ─m→ P₂)
      → (P₁ ─m→ P₃)
(g , pg) ∘m (f , pf) = g ∘ f , λ x y p → pg (f x) (f y) (pf x y p)

𝟏m : {A : Set} → (P : PosetStr A) → P ─m→ P
𝟏m {A} P = id , (λ x y → id)

_≃m≃_ : {A B : Set} → PosetStr A → PosetStr B → Set
_≃m≃_ {A} {B} P₁ P₂ =
  Σ[ m₁ ∈ (P₁ ─m→ P₂) ]
  Σ[ m₂ ∈ (P₂ ─m→ P₁) ] ((proj₁ m₁ ∘ proj₁ m₂) ~ id) × ((proj₁ m₂ ∘ proj₁ m₁) ~ id)

↓ : {ℓ : Level} (P : Poset {ℓ}) → proj₁ P → Set ℓ
↓ P x = Σ[ y ∈ (proj₁ P) ] (x ⊑ y)
  where
    open PosetStr (proj₂ P) using (_⊑_)
