```
{-# OPTIONS --without-K --cubical --safe #-}

module Poset where

open import Basis
open import Powerset
```

## Definition of poset

```
Order : (ℓ₁ : Level) → Type ℓ → Type (ℓ ⊔ suc ℓ₁)
Order {ℓ = ℓ} ℓ₁ A = (A → A → hProp ℓ₁)

isReflexive : {A : Type ℓ₀} → Order ℓ₁ A → hProp (ℓ₀ ⊔ ℓ₁)
isReflexive {A = X} _⊑_ =
  ((x : X) → (x ⊑ x) is-true) , ∏-prop (λ x → is-true-prop (x ⊑ x))

isTransitive : {A : Type ℓ₀} → Order ℓ₁ A → hProp (ℓ₀ ⊔ ℓ₁)
isTransitive {ℓ₀ = ℓ₀} {ℓ₁ = ℓ₁} {A = X} _⊑_ = φ , φ-prop
  where
    φ      : Type (ℓ₀ ⊔ ℓ₁)
    φ      = ((x y z : X) → (x ⊑ y ⇒ y ⊑ z ⇒ x ⊑ z) is-true)
    φ-prop : IsProp φ
    φ-prop = ∏-prop λ x → ∏-prop λ y → ∏-prop λ z → is-true-prop (x ⊑ y ⇒ y ⊑ z ⇒ x ⊑ z)

isAntisym : {A : Type ℓ₀} → IsSet A → Order ℓ₁ A → hProp (ℓ₀ ⊔ ℓ₁)
isAntisym {ℓ₀ = ℓ₀} {ℓ₁ = ℓ₁} {A = X} A-set _⊑_ = φ , φ-prop
  where
    φ      : Type (ℓ₀ ⊔ ℓ₁)
    φ      = ((x y : X) → (x ⊑ y) is-true → (y ⊑ x) is-true → x ≡ y)
    φ-prop : IsProp φ
    φ-prop = ∏-prop λ x → ∏-prop λ y →
              ∏-prop λ p → ∏-prop λ q → A-set x y

PosetAx : (ℓ₁ : Level) (A : Type ℓ₀) → Order ℓ₁ A → hProp (ℓ₀ ⊔ ℓ₁)
PosetAx {ℓ₀ = ℓ₀} ℓ₁ A _⊑_ = φ , φ-prop
  where
    isPartial : IsSet A → hProp (ℓ₀ ⊔ ℓ₁)
    isPartial = λ A-set → isReflexive _⊑_ ∧ isTransitive _⊑_ ∧ isAntisym A-set _⊑_
    φ         = Σ[ A-set ∈ IsSet A ] (isPartial A-set) is-true
    φ-prop    = isOfHLevelΣ 1 isPropIsSet (is-true-prop ∘ isPartial)

```

A poset structure with level `ℓ₁`.

```
PosetStr : (ℓ₁ : Level) → Type ℓ → Type (ℓ ⊔ suc ℓ₁)
PosetStr ℓ₁ = add-to-structure (Order ℓ₁) (λ A RP → PosetAx ℓ₁ A RP is-true)

PosetStr-set : (ℓ₁ : Level) (A : Type ℓ₀) → IsSet (PosetStr ℓ₁ A)
PosetStr-set ℓ₁ A =
  Σ-set (∏-set λ _ → ∏-set λ _ → isSetHProp) λ _⊑_ →
  Σ-set (prop⇒set isPropIsSet) λ A-set →
    prop⇒set
      (is-true-prop (isReflexive {A = A} _⊑_  ∧ isTransitive _⊑_ ∧ isAntisym A-set _⊑_))
```

A poset with carrier level `ℓ₀` and relation level `ℓ₁`.

```
Poset : (ℓ₀ ℓ₁ : Level) → Type (suc ℓ₀ ⊔ suc ℓ₁)
Poset ℓ₀ ℓ₁ = Σ (Type ℓ₀) (PosetStr ℓ₁)
```

## Projections

Given a poset `P`, `∣ P ∣ₚ` denotes its carrier set and `strₚ P` its order structure.

```
∣_∣ₚ : Poset ℓ₀ ℓ₁ → Type ℓ₀
∣ X , _ ∣ₚ = X

strₚ : (P : Poset ℓ₀ ℓ₁) → PosetStr ℓ₁ ∣ P ∣ₚ
strₚ (_ , s) = s
```

```
rel : (P : Poset ℓ₀ ℓ₁) → ∣ P ∣ₚ → ∣ P ∣ₚ → hProp ℓ₁
rel (_ , _⊑_ , _) = _⊑_

syntax rel P x y = x ⊑[ P ] y
```

Similarly, we define projections for the poset properties.

```
⊑[_]-refl : (P : Poset ℓ₀ ℓ₁) → (x : ∣ P ∣ₚ) → x ⊑[ P ] x is-true
⊑[_]-refl (_ , _ , _ , ⊑-refl , _) = ⊑-refl

⊑[_]-trans : (P : Poset ℓ₀ ℓ₁) (x y z : ∣ P ∣ₚ)
           → x ⊑[ P ] y is-true → y ⊑[ P ] z is-true → x ⊑[ P ] z is-true
⊑[_]-trans (_ , _ , _ , _ , ⊑-trans , _) = ⊑-trans

⊑[_]-antisym : (P : Poset ℓ₀ ℓ₁) (x y : ∣ P ∣ₚ)
             → x ⊑[ P ] y is-true → y ⊑[ P ] x is-true → x ≡ y
⊑[_]-antisym (_ , _ , _ , _ , _ , ⊑-antisym) = ⊑-antisym

carrier-is-set : (P : Poset ℓ₀ ℓ₁) → IsSet ∣ P ∣ₚ
carrier-is-set (_ , _ , is-set , _) = is-set
```

## Partial order reasoning

```
module PosetReasoning (P : Poset ℓ₀ ℓ₁) where

  _⊑⟨_⟩_ : (x : ∣ P ∣ₚ) {y z : ∣ P ∣ₚ}
         → x ⊑[ P ] y is-true → y ⊑[ P ] z is-true → x ⊑[ P ] z is-true
  _ ⊑⟨ p ⟩ q = ⊑[ P ]-trans _ _ _ p q

  _■ : (x : ∣ P ∣ₚ) → x ⊑[ P ] x is-true
  _■ = ⊑[ P ]-refl

  infixr 0 _⊑⟨_⟩_
  infix  1 _■
```

```
≡⇒⊑ : (P : Poset ℓ₀ ℓ₁) → {x y : ∣ P ∣ₚ} → x ≡ y → rel P x y is-true
≡⇒⊑ P {x = x} p = subst (λ z → x ⊑[ P ] z is-true) p (⊑[ P ]-refl x)

IsMonotonic : (P : Poset ℓ₀ ℓ₁) (Q : Poset ℓ₂ ℓ₃)
            → (∣ P ∣ₚ → ∣ Q ∣ₚ) → Type (ℓ₀ ⊔ ℓ₁ ⊔ ℓ₃)
IsMonotonic P Q f =
  (x y : ∣ P ∣ₚ) → x ⊑[ P ] y is-true → (f x) ⊑[ Q ] (f y) is-true

IsMonotonic-prop : (P : Poset ℓ₀ ℓ₁) (Q : Poset ℓ₀′ ℓ₁′) (f : ∣ P ∣ₚ → ∣ Q ∣ₚ)
                 → IsProp (IsMonotonic P Q f)
IsMonotonic-prop P Q f =
  ∏-prop (λ x → ∏-prop λ y → ∏-prop λ _ → is-true-prop (f x ⊑[ Q ] f y))
```

## Monotonic functions

```
_─m→_ : Poset ℓ₀ ℓ₁ → Poset ℓ₀′ ℓ₁′ → Type (ℓ₀ ⊔ ℓ₁ ⊔ ℓ₀′ ⊔ ℓ₁′)
_─m→_ P Q = Σ (∣ P ∣ₚ → ∣ Q ∣ₚ) (IsMonotonic P Q)
```

Projection for the underlying function of a monotonic map.

```
_$ₘ_ = π₀
```

Monotonic function composition.

```
_∘m_ : {P : Poset ℓ₀ ℓ₁} {Q : Poset ℓ₀′ ℓ₁′} {R : Poset ℓ₀′′ ℓ₁′′}
     → (Q ─m→ R) → (P ─m→ Q) → (P ─m→ R)
(g , pg) ∘m (f , pf) = g ∘ f , λ x y p → pg (f x) (f y) (pf x y p)

𝟏m : (P : Poset ℓ₀ ℓ₁) → P ─m→ P
𝟏m P = id , (λ x y x⊑y → x⊑y)

↓[_]_ : (P : Poset ℓ₀ ℓ₁) → ∣ P ∣ₚ → Type (ℓ₀ ⊔ ℓ₁)
↓[ P ] a = Σ ∣ P ∣ₚ (λ b → b ⊑[ P ] a is-true)
```

## Downward-closure

```
IsDownwardClosed : (P : Poset ℓ₀ ℓ₁) → (𝒫 ∣ P ∣ₚ) → hProp (ℓ₀ ⊔ ℓ₁)
IsDownwardClosed P@(X , _) D =
  ((x y : X) → D x is-true → y ⊑[ P ] x is-true → D y is-true) , prop
  where
    prop : IsProp ((x y : X) → D x is-true → y ⊑[ P ] x is-true → D y is-true)
    prop = ∏-prop λ _ → ∏-prop λ x → ∏-prop λ _ → ∏-prop λ _ →
           is-true-prop (D x)

DownwardClosedSubset : (P : Poset ℓ₀ ℓ₁) → Type (suc ℓ₀ ⊔ ℓ₁)
DownwardClosedSubset P = Σ (𝒫 ∣ P ∣ₚ) (λ S → IsDownwardClosed P S is-true)

DownwardClosedSubset-set : (P : Poset ℓ₀ ℓ₁) → IsSet (DownwardClosedSubset P)
DownwardClosedSubset-set P =
  Σ-set (𝒫-set ∣ P ∣ₚ) λ x → prop⇒set (is-true-prop (IsDownwardClosed P x))
```

## Product of two posets

```
_×ₚ_ : (P : Poset ℓ₀ ℓ₁) (Q : Poset ℓ₀′ ℓ₁′) → Poset (ℓ₀ ⊔ ℓ₀′) (ℓ₁ ⊔ ℓ₁′)
P ×ₚ Q = (∣ P ∣ₚ × ∣ Q ∣ₚ) , _⊑_ , carrier-set , (⊑-refl , ⊑-trans , ⊑-antisym)
  where
    _⊑_ : ∣ P ∣ₚ × ∣ Q ∣ₚ → ∣ P ∣ₚ × ∣ Q ∣ₚ → hProp _
    _⊑_ (x₀ , y₀) (x₁ , y₁) = x₀ ⊑[ P ] x₁ ∧ y₀ ⊑[ Q ] y₁

    carrier-set : IsSet (∣ P ∣ₚ × ∣ Q ∣ₚ)
    carrier-set = isOfHLevelΣ 2 (carrier-is-set P) λ _ → (carrier-is-set Q)

    ⊑-refl : (p : ∣ P ∣ₚ × ∣ Q ∣ₚ) → p ⊑ p is-true
    ⊑-refl (x , y) = (⊑[ P ]-refl x) , (⊑[ Q ]-refl y)

    ⊑-trans : (p q r : ∣ P ∣ₚ × ∣ Q ∣ₚ) → p ⊑ q is-true → q ⊑ r is-true → p ⊑ r is-true
    ⊑-trans (x₀ , y₀) (x₁ , y₁) (x₂ , y₂) (x₀⊑x₁ , y₀⊑y₁) (x₁⊑x₂ , y₁⊑y₂) =
      ⊑[ P ]-trans _ _ _ x₀⊑x₁ x₁⊑x₂ , ⊑[ Q ]-trans _ _ _ y₀⊑y₁ y₁⊑y₂

    ⊑-antisym : (p q : ∣ P ∣ₚ × ∣ Q ∣ₚ) → p ⊑ q is-true → q ⊑ p is-true → p ≡ q
    ⊑-antisym (x₀ , y₀) (x₁ , y₁) (x₀⊑x₁ , y₀⊑y₁) (x₁⊑x₀ , y₁⊑y₀) =
      sigmaPath→pathSigma (x₀ , y₀) (x₁ , y₁) (⊑[ P ]-antisym _ _ x₀⊑x₁ x₁⊑x₀ , sym NTS)
      where
        NTS : y₁ ≡ transport refl y₀
        NTS = subst (_≡_ y₁) (sym (transportRefl y₀)) (⊑[ Q ]-antisym _ _ y₁⊑y₀ y₀⊑y₁)
```

## Equality of isomorphic posets

```
order-iso : (M N : Σ (Type ℓ₀) (Order ℓ₁)) → π₀ M ≃ π₀ N → Type (ℓ₀ ⊔ ℓ₁)
order-iso (A , _⊑₀_) (B , _⊑₁_) eqv =
  (x y : A) → (x ⊑₀ y ⇔ f x ⊑₁ f y) is-true
  where
    f = equivFun eqv

RP-iso-prop : (P Q : Σ (Type ℓ₀) (Order ℓ₁))
            → (i : π₀ P ≃ π₀ Q) → IsProp (order-iso P Q i)
RP-iso-prop (A , _⊑₀_) (B , _⊑₁_) i =
  ∏-prop λ x → ∏-prop λ y → is-true-prop (x ⊑₀ y ⇔ f x ⊑₁ f y)
  where
    f = equivFun i

-- TODO: they already have this result in `cubical`.
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

raw-poset-is-SNS : SNS {ℓ = ℓ} (Order ℓ₁) order-iso
raw-poset-is-SNS {ℓ₁ = ℓ₁} {X = X} _⊑₀_ _⊑₁_ = invEquiv (f , f-equiv)
  where
    f : order-iso (X , _⊑₀_) (X , _⊑₁_) (idEquiv X) → _⊑₀_ ≡ _⊑₁_
    f i = fn-ext _ _ λ x → fn-ext _ _ λ y → ⇔toPath (proj₁ (i x y)) (proj₂ (i x y))

    f-equiv : isEquiv f
    f-equiv = record { equiv-proof = λ eq → (g eq , right-inv eq) , h eq }
      where
        g : (eq : _⊑₀_ ≡ _⊑₁_)
          → (x y : X)
          → (x ⊑₀ y is-true → x ⊑₁ y is-true)
            ×× (x ⊑₁ y is-true → x ⊑₀ y is-true)
        g eq x y =
            (λ x⊑₀y → subst (λ { _⊑⋆_ → x ⊑⋆ y is-true }) eq x⊑₀y)
          , λ x⊑₁y → subst (λ { _⊑⋆_ → (x ⊑⋆ y) is-true }) (sym eq) x⊑₁y

        rel-set : IsSet (X → X → hProp ℓ)
        rel-set = ∏-set λ _ → ∏-set λ _ → isSetHProp

        iff-prop : IsProp ((x y : X) → (x ⊑₀ y ⇔ x ⊑₁ y) is-true)
        iff-prop = ∏-prop λ x → ∏-prop λ y → is-true-prop (x ⊑₀ y ⇔ x ⊑₁ y)

        right-inv : (eq : _⊑₀_ ≡ _⊑₁_) → f (g eq) ≡ eq
        right-inv eq = rel-set _⊑₀_ _⊑₁_ (f (g eq)) eq

        h : (eq : _⊑₀_ ≡ _⊑₁_)
          → (fib : fiber f eq) → (g eq , right-inv eq) ≡ fib
        h eq (i , snd) = ΣProp≡
                           (λ x → hLevelSuc 2 (Order ℓ₁ X) rel-set _⊑₀_ _⊑₁_ (f x) eq)
                           (iff-prop (g eq) i)

raw-poset-is-SNS' : SNS' {ℓ = ℓ} (Order ℓ₁) order-iso
raw-poset-is-SNS' {ℓ₁ = ℓ₁} = SNS→SNS' (Order ℓ₁) order-iso raw-poset-is-SNS

poset-iso : (P Q : Poset ℓ₀ ℓ₁) → ∣ P ∣ₚ ≃ ∣ Q ∣ₚ → Type (ℓ₀ ⊔ ℓ₁)
poset-iso {ℓ₁ = ℓ₁} = add-to-iso _ order-iso λ A str → PosetAx ℓ₁ A str is-true

poset-axioms-props : (A : Type ℓ₀) (str : Order ℓ₁ A)
                   → IsProp (PosetAx ℓ₁ A str is-true)
poset-axioms-props {ℓ₁ = ℓ₁} A str = is-true-prop (PosetAx ℓ₁ A str)

poset-is-SNS' : SNS' {ℓ = ℓ} (PosetStr ℓ₁) poset-iso
poset-is-SNS' {ℓ₁ = ℓ₁} =
  add-axioms-SNS' _ _
    (λ A str → PosetAx ℓ₁ A str is-true)
    poset-axioms-props
    raw-poset-is-SNS'

poset-is-SNS'' : SNS'' {ℓ = ℓ} (PosetStr ℓ₁) poset-iso
poset-is-SNS'' = subst id (sym (SNS'≡SNS'' _ poset-iso)) poset-is-SNS'

poset-is-SNS''' : SNS''' {ℓ = ℓ₀} (PosetStr ℓ₁) poset-iso
poset-is-SNS''' = SNS''→SNS''' poset-is-SNS''

poset-SIP : (A : Type ℓ₀) (B : Type ℓ₀) (eqv : A ≃ B)
            (P : PosetStr ℓ₁ A) (Q : PosetStr ℓ₁ B)
          → poset-iso (A , P) (B , Q) eqv
          → (A , P) ≡ (B , Q)
poset-SIP {ℓ₁ = ℓ₁} A B eqv P Q i = foo (eqv , i)
  where
    foo : (A , P) ≃[ poset-iso ] (B , Q) → (A , P) ≡ (B , Q)
    foo = equivFun (SIP (PosetStr ℓ₁) poset-iso poset-is-SNS''' (A , P) (B , Q))

_≃ₚ_ : Poset ℓ₀ ℓ₁ → Poset ℓ₀ ℓ₁ → Type (ℓ₀ ⊔ ℓ₁)
_≃ₚ_ P Q = Σ[ i ∈ (∣ P ∣ₚ ≃ ∣ Q ∣ₚ) ] poset-iso P Q i

pos-iso-to-eq : (P Q : Poset ℓ₀ ℓ₁) → P ≃ₚ Q → P ≡ Q
pos-iso-to-eq (A , A-pos) (B , B-pos) (eqv , i) = poset-SIP A B eqv A-pos B-pos i

-- --}
-- --}
-- --}
```
