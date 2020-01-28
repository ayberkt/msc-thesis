```
{-# OPTIONS --without-K --cubical --safe #-}

module Poset where

open import Basis
open import Powerset
```

```
record PosetStr (ℓ₁ : Level) (A : Set ℓ₀) : Set (ℓ₀ ⊔ suc ℓ₁) where
  constructor posetstr

  -- Data.
  field
    _⊑_  : A → A → Ω ℓ₁

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
Poset ℓ ℓ′ = Σ (Set ℓ) (PosetStr ℓ′)

∣_∣ₚ : {ℓ ℓ′ : Level} → Poset ℓ ℓ′ → Set ℓ
∣ X , _ ∣ₚ = X

strₚ : {ℓ ℓ′ : Level} → (P : Poset ℓ ℓ′) → PosetStr ℓ′ ∣ P ∣ₚ
strₚ (_ , s) = s
```

```
rel : (P : Poset ℓ₀ ℓ₁) → ∣ P ∣ₚ → ∣ P ∣ₚ → Ω ℓ₁
rel P = PosetStr._⊑_ (π₁ P)

syntax rel P x y = x ⊑[ P ] y
```

```
≡⇒⊑ : (P : Poset ℓ₀ ℓ₁) → {x y : ∣ P ∣ₚ} → x ≡ y → rel P x y is-true
≡⇒⊑ P {x = x} p = subst (λ z → rel P x z is-true) p (⊑-refl x)
  where
    open PosetStr (strₚ P) using (⊑-refl)

IsMonotonic : (P Q : Poset ℓ₀ ℓ₁) → (∣ P ∣ₚ → ∣ Q ∣ₚ) → Set (ℓ₀ ⊔ ℓ₁)
IsMonotonic (X , posetstr _⊑₀_ _ _ _ _) (Y , posetstr _⊑₁_ _ _ _ _) f =
  (x y : X) → x ⊑₀ y is-true → (f x) ⊑₁ (f y) is-true
```

## Monotonic functions

```
-- TODO: levels might have to generalised.
_─m→_ : Poset ℓ₀ ℓ₁ → Poset ℓ₀ ℓ₁ → Set (ℓ₀ ⊔ ℓ₁)
_─m→_ P Q = Σ (∣ P ∣ₚ → ∣ Q ∣ₚ) (IsMonotonic P Q)
```

Projection for the underlying function of a monotonic map.

```
_$ₘ_ = π₀
```

Monotonic function composition.

```
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

DownwardClosedSubset-set : (P : Poset ℓ₀ ℓ₁) → IsSet (DownwardClosedSubset P)
DownwardClosedSubset-set P =
  Σ-set (𝒫-set ∣ P ∣ₚ) λ x → prop⇒set (is-true-prop (IsDownwardClosed P x))
```

```
raw-poset-str : Type ℓ → Type (suc ℓ)
raw-poset-str {ℓ = ℓ} A = A → A → Ω ℓ

raw-poset-iso : (M N : Σ (Type ℓ) raw-poset-str) → π₀ M ≃ π₀ N → Type ℓ
raw-poset-iso (A , _⊑₀_) (B , _⊑₁_) eq = (x y : A) → ((x ⊑₀ y) ⇔ (f x ⊑₁ f y)) is-true
  where
    f = equivFun eq

××=× : (A B : Type ℓ) → (A × B) ≡ A ×× B
××=× A B = isoToPath {A = A × B} {B = A ×× B} (iso f g sec ret)
  where
    f : A × B → A ×× B
    f = λ { (x , y ) → (x , y) }

    g : A ×× B → A × B
    g = λ { (x , y ) → (x , y) }

    sec : section f g
    sec (x , y) = refl

    ret : retract f g
    ret (x , y) = refl

raw-poset-is-SNS : SNS {ℓ = ℓ} raw-poset-str raw-poset-iso
raw-poset-is-SNS {X = X} _⊑₀_ _⊑₁_ = invEquiv (f , f-equiv)
  where
    f : raw-poset-iso (X , _⊑₀_) (X , _⊑₁_) (idEquiv X) → _⊑₀_ ≡ _⊑₁_
    f i = fn-ext _⊑₀_ _⊑₁_ (λ x → fn-ext (_⊑₀_ x) (_⊑₁_ x) (λ y → ⇔toPath (proj₁ (i x y)) (proj₂ (i x y))))

    f-equiv : isEquiv f
    f-equiv = record { equiv-proof = λ eq → (g eq , right-inv eq) , h eq }
      where
        g : (eq : _⊑₀_ ≡ _⊑₁_)
          → (x y : X)
          → (x ⊑₀ y is-true → x ⊑₁ y is-true) ×× (x ⊑₁ y is-true → x ⊑₀ y is-true)
        g eq x y = (λ x⊑₀y → subst (λ _⊑⋆_ → x ⊑⋆ y is-true) eq x⊑₀y) , λ x⊑₁y → subst (λ _⊑⋆_ → (x ⊑⋆ y) is-true) (sym eq) x⊑₁y

        rel-set : IsSet (X → X → Ω ℓ)
        rel-set = ∏-set (λ _ → ∏-set λ _ → isSetHProp)

        something-prop : IsProp ((x y : X) → ((x ⊑₀ y) is-true → (x ⊑₁ y) is-true) ×× ((x ⊑₁ y) is-true → (x ⊑₀ y) is-true))
        something-prop = ∏-prop (λ x → ∏-prop λ y → subst IsProp (××=× (x ⊑₀ y is-true → x ⊑₁ y is-true) (x ⊑₁ y is-true → x ⊑₀ y is-true))
                           (isOfHLevelΣ 1 (∏-prop (λ z → is-true-prop (x ⊑₁ y))) λ p → ∏-prop (λ q → is-true-prop (x ⊑₀ y))))

        right-inv : (eq : _⊑₀_ ≡ _⊑₁_) → f (g eq) ≡ eq
        right-inv eq = rel-set _⊑₀_ _⊑₁_ (f (g eq)) eq

        h : (eq : _⊑₀_ ≡ _⊑₁_) → (fib : fiber f eq) → (g eq , right-inv eq) ≡ fib
        h eq (i , snd) = ΣProp≡ (λ i → hLevelSuc 2 (X → X → Ω _) rel-set _⊑₀_ _⊑₁_ (f i) eq) (something-prop (g eq) i)

raw-poset-is-SNS' : SNS' {ℓ = ℓ} raw-poset-str raw-poset-iso
raw-poset-is-SNS' = SNS→SNS' raw-poset-str raw-poset-iso raw-poset-is-SNS

poset-axioms : (A : Type ℓ) → raw-poset-str A → Type ℓ
poset-axioms A _⊑_ = ((x : A) → x ⊑ x is-true)
                   × ((x y z : A) → x ⊑ y is-true → y ⊑ z is-true → x ⊑ z is-true)
                   × ((x y : A) → x ⊑ y is-true → y ⊑ x is-true → x ≡ y)
                   × (IsSet A)

poset-str : Type ℓ → Type (suc ℓ)
poset-str = add-to-structure raw-poset-str poset-axioms


poset-iso : (M N : Σ (Type ℓ) poset-str) → π₀ M ≃ π₀ N → Type ℓ
poset-iso = add-to-iso raw-poset-str raw-poset-iso poset-axioms

{--

poset-axioms-props : (X : Type ℓ) (X-set : IsSet X) (str : raw-poset-str X)
                   → IsProp (poset-axioms X str)
poset-axioms-props X X-set _⊑_ = isOfHLevelΣ 1 refl-prop λ _ → isOfHLevelΣ 1 trans-prop λ _ →  isOfHLevelΣ 1 antisym-prop λ _ → IsSet-prop
  where
    refl-prop : IsProp ((x : X) → (x ⊑ x) is-true)
    refl-prop = ∏-prop λ x → is-true-prop (x ⊑ x)

    trans-prop : IsProp ((x y z : X) → (x ⊑ y) is-true → (y ⊑ z) is-true → (x ⊑ z) is-true)
    trans-prop = ∏-prop λ x → ∏-prop λ _ → ∏-prop λ z → ∏-prop λ _ → ∏-prop λ _ → is-true-prop (x ⊑ z)

    antisym-prop : IsProp ((x y : X) → x ⊑ y is-true → y ⊑ x is-true → x ≡ y)
    antisym-prop = ∏-prop λ x → ∏-prop λ y → ∏-prop λ p → ∏-prop λ q → X-set x y

    IsSet-prop : IsProp (IsSet X)
    IsSet-prop = {!SetHProp!}


poset-is-SNS' : SNS' {ℓ = ℓ} poset-str poset-iso
poset-is-SNS' =
  add-axioms-SNS' raw-poset-str raw-poset-iso poset-axioms {!!} {!!}

-- --}
-- --}
-- --}
```
