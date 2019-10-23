{-# OPTIONS --without-K #-}

module Poset where

open import Common
open import Homotopy

private
  variable
    ℓ ℓ′ : Level

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

  _⊑⟨_⟩_ : (x : A) {y z : A} → x ⊑ y holds → y ⊑ z holds → x ⊑ z holds
  _ ⊑⟨ p ⟩ q = ⊑-trans _ _ _ p q

  _■ : (x : A) → x ⊑ x holds
  _■ = ⊑-refl

  infixr 0 _⊑⟨_⟩_
  infix  1 _■

Poset : (ℓ ℓ′ : Level) → Set (suc ℓ ⊔ suc ℓ′)
Poset ℓ ℓ′ = Σ[ A ∈ Set ℓ ] (PosetStr ℓ ℓ′ A)

∣_∣ₚ : {ℓ ℓ′ : Level} → Poset ℓ ℓ′ → Set ℓ
∣ X , _ ∣ₚ = X

strₚ : {ℓ ℓ′ : Level} → (P : Poset ℓ ℓ′) → PosetStr ℓ ℓ′ ∣ P ∣ₚ
strₚ (_ , s) = s

rel : (P : Poset ℓ ℓ′) → ∣ P ∣ₚ → ∣ P ∣ₚ → Ω ℓ′
rel P = PosetStr._⊑_ (proj₂ P)

-- A convenient notation for referring to the relation of a poset.
syntax rel P x y = x ⊑[ P ] y

≡⇒⊑ : (P : Poset ℓ ℓ′) → {x y : ∣ P ∣ₚ} → x ≡ y → rel P x y holds
≡⇒⊑ P {x = x} refl = PosetStr.⊑-refl (strₚ P) x

≡⇒⊒ : (P : Poset ℓ ℓ′) → (x y : ∣ P ∣ₚ) → x ≡ y → rel P y x holds
≡⇒⊒ P x x refl = PosetStr.⊑-refl (strₚ P) x

IsMonotonic : (P Q : Poset ℓ ℓ′) → (∣ P ∣ₚ → ∣ Q ∣ₚ) → Set (ℓ ⊔ ℓ′)
IsMonotonic (X , posetstr _⊑₀_ _ _ _ _) (Y , posetstr _⊑₁_ _ _ _ _) f =
  (x y : X) → x ⊑₀ y holds → (f x) ⊑₁ (f y) holds

-- Monotonic functions.
_─m→_ : Poset ℓ ℓ′ → Poset ℓ ℓ′ → Set (ℓ ⊔ ℓ′)
_─m→_ P Q = Σ[ f ∈ (∣ P ∣ₚ → ∣ Q ∣ₚ) ] IsMonotonic P Q f

-- Projection for the underlying function of a monotonic map.
_$ₘ_ = proj₁

-- Monotonic function composition.
_∘m_ : {P Q R : Poset ℓ ℓ′} → (Q ─m→ R) → (P ─m→ Q) → (P ─m→ R)
(g , pg) ∘m (f , pf) = g ∘ f , λ x y p → pg (f x) (f y) (pf x y p)

𝟏m : (P : Poset ℓ ℓ′) → P ─m→ P
𝟏m P = id , λ x y x⊑y → x⊑y

_≃m≃_ : Poset ℓ ℓ′ → Poset ℓ ℓ′ → Set (ℓ ⊔ ℓ′)
_≃m≃_ P Q =
  Σ[ m₁ ∈ (P ─m→ Q) ]
  Σ[ m₂ ∈ (Q ─m→ P) ] ((proj₁ m₁ ∘ proj₁ m₂) ~ id) × ((proj₁ m₂ ∘ proj₁ m₁) ~ id)

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
