{-# OPTIONS --without-K #-}

module Poset where

open import Common
open import Homotopy

private
  variable
    ℓ ℓ′ : Level

_$_ : {A : Set ℓ} {B : A → Set ℓ′} → Σ A B → A
_$_ = proj₁

record PosetStr (ℓ ℓ′ : Level) (A : Set ℓ) : Set ((suc ℓ) ⊔ (suc ℓ′)) where
  constructor posetstr

  -- Data.
  field
    _⊑_  : A → A → Ω ℓ′

  -- Homotopy structure.
  field
    A-set : IsSet A

  -- Laws.
  field
    ⊑-refl    : (x     : A) → (x ⊑ x) holds
    ⊑-trans   : (x y z : A) → (x ⊑ y) holds → (y ⊑ z) holds → (x ⊑ z) holds
    ⊑-antisym : (x y   : A) → (x ⊑ y) holds → (y ⊑ x) holds → x ≡ y

Poset : (ℓ ℓ′ : Level) → Set (suc ℓ ⊔ suc ℓ′)
Poset ℓ ℓ′ = Σ[ A ∈ Set ℓ ] (PosetStr ℓ ℓ′ A)

∣_∣ₚ : {ℓ ℓ′ : Level} → Poset ℓ ℓ′ → Set ℓ
∣ X , _ ∣ₚ = X

strₚ : {ℓ ℓ′ : Level} → (P : Poset ℓ ℓ′) → PosetStr ℓ ℓ′ ∣ P ∣ₚ
strₚ (_ , s) = s

-- Monotonic functions.
_─m→_ : {ℓ ℓ′ : Level} {A B : Set ℓ} → PosetStr ℓ ℓ′ A → PosetStr ℓ ℓ′ B → Set (ℓ ⊔ ℓ′)
_─m→_ {_} {_} {A} {B} P₁ P₂ =
  let
     open PosetStr P₁ using () renaming (_⊑_ to _⊑₁_)
     open PosetStr P₂ using () renaming (_⊑_ to _⊑₂_)
   in
     Σ[ f ∈ (A → B) ] ((x y : A) → (x ⊑₁ y) holds → ((f x) ⊑₂ (f y))  holds)

-- Monotonic function composition.
_∘m_ : {A B C : Set ℓ} {P₁ : PosetStr ℓ ℓ′ A} {P₂ : PosetStr ℓ ℓ′ B} {P₃ : PosetStr ℓ ℓ′ C}
     → (P₂ ─m→ P₃)
     → (P₁ ─m→ P₂)
     → (P₁ ─m→ P₃)
(g , pg) ∘m (f , pf) = g ∘ f , λ x y p → pg (f x) (f y) (pf x y p)

𝟏m : {A : Set ℓ} → (P : PosetStr ℓ ℓ′ A) → P ─m→ P
𝟏m {A} P = id , (λ x y → id)

_≃m≃_ : {A B : Set ℓ} → PosetStr ℓ ℓ′ A → PosetStr ℓ ℓ′ B → Set (ℓ ⊔ ℓ′)
_≃m≃_ {A} {B} P₁ P₂ =
  Σ[ m₁ ∈ (P₁ ─m→ P₂) ]
  Σ[ m₂ ∈ (P₂ ─m→ P₁) ] ((proj₁ m₁ ∘ proj₁ m₂) ~ id) × ((proj₁ m₂ ∘ proj₁ m₁) ~ id)

IsDownwardClosed : (P : Poset ℓ ℓ′) → (𝒫 ∣ P ∣ₚ) → Ω (ℓ ⊔ ℓ′)
IsDownwardClosed (X , P) D = ((x y : X) → x ∈ D holds → (y ⊑ x) holds → y ∈ D holds) , prop
  where
    prop = ∏-resp-prop λ _ → ∏-resp-prop λ y → ∏-resp-prop λ _ → ∏-resp-prop λ _ →
      proj₂ (D y)
    open PosetStr P using (_⊑_)

DownwardClosedSubset : (P : Poset ℓ ℓ′) → Set (suc ℓ ⊔ ℓ′)
DownwardClosedSubset P = Σ[ S ∈ (𝒫 ∣ P ∣ₚ) ] (IsDownwardClosed P S holds)

DownwardClosedSubset-set : (P : Poset ℓ ℓ′) → IsSet (DownwardClosedSubset P)
DownwardClosedSubset-set P = Σ-set 𝒫-set (prop⇒set ∘ proj₂ ∘ IsDownwardClosed P)
