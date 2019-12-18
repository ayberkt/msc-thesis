{-# OPTIONS --without-K --cubical --safe #-}

module Poset where

open import Basis
open import Powerset

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
    ⊑-refl    : (x     : A) → x ⊑ x is-true
    ⊑-trans   : (x y z : A) → x ⊑ y is-true → y ⊑ z is-true → x ⊑ z is-true
    ⊑-antisym : (x y   : A) → x ⊑ y is-true → y ⊑ x is-true → x ≡ y

  _⊑⟨_⟩_ : (x : A) {y z : A} → x ⊑ y is-true → y ⊑ z is-true → x ⊑ z is-true
  _ ⊑⟨ p ⟩ q = ⊑-trans _ _ _ p q

  _■ : (x : A) → x ⊑ x is-true
  _■ = ⊑-refl

  infixr 0 _⊑⟨_⟩_
  infix  1 _■

Poset : (ℓ ℓ′ : Level) → Set (suc ℓ ⊔ suc ℓ′)
Poset ℓ ℓ′ = Σ (Set ℓ) (PosetStr ℓ ℓ′)

∣_∣ₚ : {ℓ ℓ′ : Level} → Poset ℓ ℓ′ → Set ℓ
∣ X , _ ∣ₚ = X

strₚ : {ℓ ℓ′ : Level} → (P : Poset ℓ ℓ′) → PosetStr ℓ ℓ′ ∣ P ∣ₚ
strₚ (_ , s) = s

rel : (P : Poset ℓ₀ ℓ₁) → ∣ P ∣ₚ → ∣ P ∣ₚ → Ω ℓ₁
rel P = PosetStr._⊑_ (π₁ P)

-- A convenient notation for referring to the relation of a poset.
syntax rel P x y = x ⊑[ P ] y

≡⇒⊑ : (P : Poset ℓ₀ ℓ₁) → {x y : ∣ P ∣ₚ} → x ≡ y → rel P x y is-true
≡⇒⊑ P {x = x} p = subst (λ z → rel P x z is-true) p (⊑-refl x)
  where
    open PosetStr (strₚ P) using (⊑-refl)

IsMonotonic : (P Q : Poset ℓ₀ ℓ₁) → (∣ P ∣ₚ → ∣ Q ∣ₚ) → Set (ℓ₀ ⊔ ℓ₁)
IsMonotonic (X , posetstr _⊑₀_ _ _ _ _) (Y , posetstr _⊑₁_ _ _ _ _) f =
  (x y : X) → x ⊑₀ y is-true → (f x) ⊑₁ (f y) is-true

-- Monotonic functions.
-- TODO: levels might have to generalised.
_─m→_ : Poset ℓ₀ ℓ₁ → Poset ℓ₀ ℓ₁ → Set (ℓ₀ ⊔ ℓ₁)
_─m→_ P Q = Σ (∣ P ∣ₚ → ∣ Q ∣ₚ) (IsMonotonic P Q)

-- Projection for the underlying function of a monotonic map.
_$ₘ_ = π₀

-- Monotonic function composition.
_∘m_ : {P Q R : Poset ℓ₀ ℓ₁} → (Q ─m→ R) → (P ─m→ Q) → (P ─m→ R)
(g , pg) ∘m (f , pf) = g ∘ f , λ x y p → pg (f x) (f y) (pf x y p)

𝟏m : (P : Poset ℓ₀ ℓ₁) → P ─m→ P
𝟏m P = id , (λ x y x⊑y → x⊑y)

↓[_]_ : (P : Poset ℓ₀ ℓ₁) → ∣ P ∣ₚ → Set (ℓ₀ ⊔ ℓ₁)
↓[ P ] a = Σ ∣ P ∣ₚ (λ b → b ⊑[ P ] a is-true)

IsDownwardClosed : (P : Poset ℓ₀ ℓ₁) → (𝒫 ∣ P ∣ₚ) → Ω (ℓ₀ ⊔ ℓ₁)
IsDownwardClosed P@(X , _) D =
  ((x y : X) → D x is-true → y ⊑[ P ] x is-true → D y is-true) , prop
  where
    prop : IsProp ((x y : X) → D x is-true → y ⊑[ P ] x is-true → D y is-true)
    prop = ∏-prop λ _ → ∏-prop λ x → ∏-prop λ _ → ∏-prop λ _ → is-true-prop (D x)

DownwardClosedSubset : (P : Poset ℓ₀ ℓ₁) → Set (suc ℓ₀ ⊔ ℓ₁)
DownwardClosedSubset P = Σ (𝒫 ∣ P ∣ₚ) (λ S → IsDownwardClosed P S is-true)

-- DownwardClosedSubset-set : (P : Poset ℓ ℓ′) → IsSet (DownwardClosedSubset P)
-- DownwardClosedSubset-set P = Σ-set 𝒫-set (prop⇒set ∘ proj₂ ∘ IsDownwardClosed P)
