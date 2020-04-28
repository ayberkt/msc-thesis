```
{-# OPTIONS --without-K --cubical --safe #-}

module Poset where

open import Basis
open import Cubical.Foundations.SIP renaming (SNS-≡ to SNS)
open import Powerset
```

## Definition of poset

```
Order : (ℓ₁ : Level) → Type ℓ → Type (ℓ ⊔ suc ℓ₁)
Order {ℓ = ℓ} ℓ₁ A = A → A → hProp ℓ₁

order-iso : (M N : Σ (Type ℓ₀) (Order ℓ₁)) → π₀ M ≃ π₀ N → Type (ℓ₀ ⊔ ℓ₁)
order-iso (A , _⊑₀_) (B , _⊑₁_) eqv =
  (x y : A) → [ x ⊑₀ y ⇔ f x ⊑₁ f y ]
  where
    f = equivFun eqv

isSet-Order : (ℓ₁ : Level) (A : Type ℓ₀) → isSet (Order ℓ₁ A)
isSet-Order ℓ₁ A = ∏-set λ _ → ∏-set λ _ → isSetHProp

Order-is-SNS : SNS {ℓ} (Order ℓ₁) order-iso
Order-is-SNS {ℓ₁ = ℓ₁} {X = X}  _⊑₀_ _⊑₁_ = f , f-equiv
  where
    f : order-iso (X , _⊑₀_) (X , _⊑₁_) (idEquiv X) → _⊑₀_ ≡ _⊑₁_
    f i = fn-ext _ _ λ x → fn-ext _ _ λ y → ⇔toPath (π₀ (i x y)) (π₁ (i x y))

    ⇔-prop : isProp ((x y : X) → [ x ⊑₀ y ⇔ x ⊑₁ y ])
    ⇔-prop = ∏-prop λ x → ∏-prop λ y → is-true-prop (x ⊑₀ y ⇔ x ⊑₁ y)

    f-equiv : isEquiv f
    f-equiv = record { equiv-proof = λ eq → (g eq , sec eq) , h eq }
      where
        g : (eq : _⊑₀_ ≡ _⊑₁_)
          → (x y : X)
          → ([ x ⊑₀ y ] → [ x ⊑₁ y ]) × ([ x ⊑₁ y ] → [ x ⊑₀ y ])
        g eq x y = subst (λ { _⊑⋆_ → [ x ⊑⋆ y ] }) eq
                 , subst (λ { _⊑⋆_ → [ x ⊑⋆ y ] }) (sym eq)

        sec : section f g
        sec p = isSet-Order _ X _⊑₀_ _⊑₁_ (f (g p)) p

        h : (p : _⊑₀_ ≡ _⊑₁_) → (fib : fiber f p) → (g p , sec p) ≡ fib
        h p (i , _) = ΣProp≡
                        (λ i′ → isOfHLevelSuc 2 (isSet-Order ℓ₁ X) _⊑₀_ _⊑₁_ (f i′) p)
                        (⇔-prop (g p) i)

isReflexive : {A : Type ℓ₀} → Order ℓ₁ A → hProp (ℓ₀ ⊔ ℓ₁)
isReflexive {A = X} _⊑_ =
  ((x : X) → [ x ⊑ x ]) , ∏-prop (λ x → is-true-prop (x ⊑ x))

isTransitive : {A : Type ℓ₀} → Order ℓ₁ A → hProp (ℓ₀ ⊔ ℓ₁)
isTransitive {ℓ₀ = ℓ₀} {ℓ₁ = ℓ₁} {A = X} _⊑_ = φ , φ-prop
  where
    φ      : Type (ℓ₀ ⊔ ℓ₁)
    φ      = ((x y z : X) → [ x ⊑ y ⇒ y ⊑ z ⇒ x ⊑ z ])
    φ-prop : isProp φ
    φ-prop = ∏-prop λ x → ∏-prop λ y → ∏-prop λ z → is-true-prop (x ⊑ y ⇒ y ⊑ z ⇒ x ⊑ z)

isAntisym : {A : Type ℓ₀} → isSet A → Order ℓ₁ A → hProp (ℓ₀ ⊔ ℓ₁)
isAntisym {ℓ₀ = ℓ₀} {ℓ₁ = ℓ₁} {A = X} A-set _⊑_ = φ , φ-prop
  where
    φ      : Type (ℓ₀ ⊔ ℓ₁)
    φ      = ((x y : X) → [ x ⊑ y ] → [ y ⊑ x ] → x ≡ y)
    φ-prop : isProp φ
    φ-prop = ∏-prop λ x → ∏-prop λ y →
              ∏-prop λ p → ∏-prop λ q → A-set x y

PosetAx : (ℓ₁ : Level) (A : Type ℓ₀) → Order ℓ₁ A → hProp (ℓ₀ ⊔ ℓ₁)
PosetAx {ℓ₀ = ℓ₀} ℓ₁ A _⊑_ = φ , φ-prop
  where
    isPartial : isSet A → hProp (ℓ₀ ⊔ ℓ₁)
    isPartial = λ A-set → isReflexive _⊑_ ⊓ isTransitive _⊑_ ⊓ isAntisym A-set _⊑_
    φ         = Σ[ A-set ∈ isSet A ] [ isPartial A-set ]
    φ-prop    = isOfHLevelΣ 1 isPropIsSet (is-true-prop ∘ isPartial)

```

A poset structure with level `ℓ₁`.

```
PosetStr : (ℓ₁ : Level) → Type ℓ → Type (ℓ ⊔ suc ℓ₁)
PosetStr ℓ₁ = add-to-structure (Order ℓ₁) λ A _⊑_ → [ PosetAx ℓ₁ A _⊑_ ]


PosetStr-set : (ℓ₁ : Level) (A : Type ℓ₀) → isSet (PosetStr ℓ₁ A)
PosetStr-set ℓ₁ A =
  Σ-set (∏-set λ _ → ∏-set λ _ → isSetHProp) λ _⊑_ →
  Σ-set (isProp→isSet isPropIsSet) λ A-set →
    isProp→isSet
      (is-true-prop (isReflexive {A = A} _⊑_ ⊓ isTransitive _⊑_ ⊓ isAntisym A-set _⊑_))
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

infix 9 rel

syntax rel P x y = x ⊑[ P ] y

```

Similarly, we define projections for the poset properties.

```
⊑[_]-refl : (P : Poset ℓ₀ ℓ₁) → (x : ∣ P ∣ₚ) → [ x ⊑[ P ] x ]
⊑[_]-refl (_ , _ , _ , ⊑-refl , _) = ⊑-refl

⊑[_]-trans : (P : Poset ℓ₀ ℓ₁) (x y z : ∣ P ∣ₚ)
           → [ x ⊑[ P ] y ] → [ y ⊑[ P ] z ] → [ x ⊑[ P ] z ]
⊑[_]-trans (_ , _ , _ , _ , ⊑-trans , _) = ⊑-trans

⊑[_]-antisym : (P : Poset ℓ₀ ℓ₁) (x y : ∣ P ∣ₚ)
             → [ x ⊑[ P ] y ] → [ y ⊑[ P ] x ] → x ≡ y
⊑[_]-antisym (_ , _ , _ , _ , _ , ⊑-antisym) = ⊑-antisym

carrier-is-set : (P : Poset ℓ₀ ℓ₁) → isSet ∣ P ∣ₚ
carrier-is-set (_ , _ , is-set , _) = is-set
```

## Partial order reasoning

```
module PosetReasoning (P : Poset ℓ₀ ℓ₁) where

  _⊑⟨_⟩_ : (x : ∣ P ∣ₚ) {y z : ∣ P ∣ₚ}
         → [ x ⊑[ P ] y ] → [ y ⊑[ P ] z ] → [ x ⊑[ P ] z ]
  _ ⊑⟨ p ⟩ q = ⊑[ P ]-trans _ _ _ p q

  _■ : (x : ∣ P ∣ₚ) → [ x ⊑[ P ] x ]
  _■ = ⊑[ P ]-refl

  infixr 0 _⊑⟨_⟩_
  infix  1 _■
```

```
≡⇒⊑ : (P : Poset ℓ₀ ℓ₁) → {x y : ∣ P ∣ₚ} → x ≡ y → [ x ⊑[ P ] y ]
≡⇒⊑ P {x = x} p = subst (λ z → [ x ⊑[ P ] z ]) p (⊑[ P ]-refl x)

IsMonotonic : (P : Poset ℓ₀ ℓ₁) (Q : Poset ℓ₂ ℓ₃)
            → (∣ P ∣ₚ → ∣ Q ∣ₚ) → Type (ℓ₀ ⊔ ℓ₁ ⊔ ℓ₃)
IsMonotonic P Q f =
  (x y : ∣ P ∣ₚ) → [ x ⊑[ P ] y ] → [ (f x) ⊑[ Q ] (f y) ]

IsMonotonic-prop : (P : Poset ℓ₀ ℓ₁) (Q : Poset ℓ₀′ ℓ₁′) (f : ∣ P ∣ₚ → ∣ Q ∣ₚ)
                 → isProp (IsMonotonic P Q f)
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

The identity monotonic map and composition of monotonic maps.

```
𝟏m : (P : Poset ℓ₀ ℓ₁) → P ─m→ P
𝟏m P = id , (λ x y x⊑y → x⊑y)

_∘m_ : {P : Poset ℓ₀ ℓ₁} {Q : Poset ℓ₀′ ℓ₁′} {R : Poset ℓ₀′′ ℓ₁′′}
     → (Q ─m→ R) → (P ─m→ Q) → (P ─m→ R)
(g , pg) ∘m (f , pf) = g ∘ f , λ x y p → pg (f x) (f y) (pf x y p)
```

## Downward-closure

We denote by `↓[ P ] x` the type of everything in `P` that is below `x`.

```
↓[_]_ : (P : Poset ℓ₀ ℓ₁) → ∣ P ∣ₚ → Type (ℓ₀ ⊔ ℓ₁)
↓[ P ] a = Σ[ b ∈ ∣ P ∣ₚ ] [ b ⊑[ P ] a ]
```

```
IsDownwardClosed : (P : Poset ℓ₀ ℓ₁) → 𝒫 ∣ P ∣ₚ → hProp (ℓ₀ ⊔ ℓ₁)
IsDownwardClosed P U =
  ((x y : ∣ P ∣ₚ) → [ x ∈ U ] → [ y ⊑[ P ] x ] → [ y ∈ U ]) , prop
  where
    prop : isProp ((x y : ∣ P ∣ₚ) → [ U x ] → [ y ⊑[ P ] x ] → [ U y ])
    prop = ∏-prop λ _ → ∏-prop λ x → ∏-prop λ _ → ∏-prop λ _ → is-true-prop (x ∈ U)

DownwardClosedSubset : (P : Poset ℓ₀ ℓ₁) → Type (suc ℓ₀ ⊔ ℓ₁)
DownwardClosedSubset P = Σ[ U ∈ 𝒫 ∣ P ∣ₚ ] [ IsDownwardClosed P U ]

DownwardClosedSubset-set : (P : Poset ℓ₀ ℓ₁) → isSet (DownwardClosedSubset P)
DownwardClosedSubset-set P =
  Σ-set (𝒫-set ∣ P ∣ₚ) λ U → isProp→isSet (is-true-prop (IsDownwardClosed P U))
```

## Product of two posets

```
_×ₚ_ : (P : Poset ℓ₀ ℓ₁) (Q : Poset ℓ₀′ ℓ₁′) → Poset (ℓ₀ ⊔ ℓ₀′) (ℓ₁ ⊔ ℓ₁′)
P ×ₚ Q = (∣ P ∣ₚ × ∣ Q ∣ₚ) , _⊑_ , carrier-set , (⊑-refl , ⊑-trans , ⊑-antisym)
  where
    _⊑_ : ∣ P ∣ₚ × ∣ Q ∣ₚ → ∣ P ∣ₚ × ∣ Q ∣ₚ → hProp _
    _⊑_ (x₀ , y₀) (x₁ , y₁) = x₀ ⊑[ P ] x₁ ⊓ y₀ ⊑[ Q ] y₁

    carrier-set : isSet (∣ P ∣ₚ × ∣ Q ∣ₚ)
    carrier-set = isOfHLevelΣ 2 (carrier-is-set P) λ _ → (carrier-is-set Q)

    ⊑-refl : (p : ∣ P ∣ₚ × ∣ Q ∣ₚ) → [ p ⊑ p ]
    ⊑-refl (x , y) = (⊑[ P ]-refl x) , (⊑[ Q ]-refl y)

    ⊑-trans : (p q r : ∣ P ∣ₚ × ∣ Q ∣ₚ) → [ p ⊑ q ] → [ q ⊑ r ] → [ p ⊑ r ]
    ⊑-trans (x₀ , y₀) (x₁ , y₁) (x₂ , y₂) (x₀⊑x₁ , y₀⊑y₁) (x₁⊑x₂ , y₁⊑y₂) =
      ⊑[ P ]-trans _ _ _ x₀⊑x₁ x₁⊑x₂ , ⊑[ Q ]-trans _ _ _ y₀⊑y₁ y₁⊑y₂

    ⊑-antisym : (p q : ∣ P ∣ₚ × ∣ Q ∣ₚ) → [ p ⊑ q ] → [ q ⊑ p ] → p ≡ q
    ⊑-antisym (x₀ , y₀) (x₁ , y₁) (x₀⊑x₁ , y₀⊑y₁) (x₁⊑x₀ , y₁⊑y₀) =
      sigmaPath→pathSigma (x₀ , y₀) (x₁ , y₁) (⊑[ P ]-antisym _ _ x₀⊑x₁ x₁⊑x₀ , sym NTS)
      where
        NTS : y₁ ≡ transport refl y₀
        NTS = subst (_≡_ y₁) (sym (transportRefl y₀)) (⊑[ Q ]-antisym _ _ y₁⊑y₀ y₀⊑y₁)
```

## Equality of isomorphic posets

```

RP-iso-prop : (P Q : Σ (Type ℓ₀) (Order ℓ₁))
            → (i : π₀ P ≃ π₀ Q) → isProp (order-iso P Q i)
RP-iso-prop (A , _⊑₀_) (B , _⊑₁_) i =
  ∏-prop λ x → ∏-prop λ y → is-true-prop (x ⊑₀ y ⇔ f x ⊑₁ f y)
  where
    f = equivFun i

poset-iso : (P Q : Poset ℓ₀ ℓ₁) → ∣ P ∣ₚ ≃ ∣ Q ∣ₚ → Type (ℓ₀ ⊔ ℓ₁)
poset-iso {ℓ₁ = ℓ₁} = add-to-iso order-iso λ A _⊑_ → [ PosetAx ℓ₁ A _⊑_ ]

poset-axioms-props : (A : Type ℓ₀) (str : Order ℓ₁ A)
                   → isProp [ PosetAx ℓ₁ A str ]
poset-axioms-props {ℓ₁ = ℓ₁} A str = is-true-prop (PosetAx ℓ₁ A str)


poset-is-SNS : SNS {ℓ} (PosetStr ℓ₁) poset-iso
poset-is-SNS {ℓ₁ = ℓ₁} =
  SNS-PathP→SNS-≡
    (PosetStr ℓ₁)
    poset-iso
    (add-axioms-SNS _ poset-axioms-props (SNS-≡→SNS-PathP order-iso Order-is-SNS))

poset-is-SNS-PathP : SNS-PathP {ℓ} (PosetStr ℓ₁) poset-iso
poset-is-SNS-PathP = SNS-≡→SNS-PathP poset-iso poset-is-SNS

poset-SIP : (A : Type ℓ₀) (B : Type ℓ₀) (eqv : A ≃ B)
            (P : PosetStr ℓ₁ A) (Q : PosetStr ℓ₁ B)
          → poset-iso (A , P) (B , Q) eqv
          → (A , P) ≡ (B , Q)
poset-SIP {ℓ₁ = ℓ₁} A B eqv P Q i = foo (eqv , i)
  where
    foo : (A , P) ≃[ poset-iso ] (B , Q) → (A , P) ≡ (B , Q)
    foo = equivFun (SIP poset-is-SNS-PathP (A , P) (B , Q))

_≃ₚ_ : Poset ℓ₀ ℓ₁ → Poset ℓ₀ ℓ₁ → Type (ℓ₀ ⊔ ℓ₁)
_≃ₚ_ P Q = Σ[ i ∈ (∣ P ∣ₚ ≃ ∣ Q ∣ₚ) ] poset-iso P Q i

pos-iso-to-eq : (P Q : Poset ℓ₀ ℓ₁) → P ≃ₚ Q → P ≡ Q
pos-iso-to-eq (A , A-pos) (B , B-pos) (eqv , i) = poset-SIP A B eqv A-pos B-pos i

-- --}
-- --}
-- --}
```
