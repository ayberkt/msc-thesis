```
{-# OPTIONS --without-K --cubical --safe #-}

module Poset where

open import Basis
open import Cubical.Foundations.SIP renaming (SNS-≡ to SNS)
open import Cubical.Foundations.Equiv using (_≃⟨_⟩_) renaming (_■ to _QED)
open import Powerset
open import Function using (_∘_; id)
```

## Definition of poset

```
Order : (ℓ₁ : Level) → Type ℓ → Type (ℓ ⊔ suc ℓ₁)
Order ℓ₁ A = A → A → hProp ℓ₁

isReflexive : {A : Type ℓ₀} → Order ℓ₁ A → hProp (ℓ₀ ⊔ ℓ₁)
isReflexive {A = X} _⊑_ =
  ((x : X) → [ x ⊑ x ]) , isPropΠ (λ x → is-true-prop (x ⊑ x))

isTransitive : {A : Type ℓ₀} → Order ℓ₁ A → hProp (ℓ₀ ⊔ ℓ₁)
isTransitive {ℓ₀ = ℓ₀} {ℓ₁ = ℓ₁} {A = X} _⊑_ = ⊑-trans , ⊑-trans-prop
  where
    ⊑-trans : Type (ℓ₀ ⊔ ℓ₁)
    ⊑-trans = ((x y z : X) → [ x ⊑ y ⇒ y ⊑ z ⇒ x ⊑ z ])

    ⊑-trans-prop : isProp  ⊑-trans
    ⊑-trans-prop = isPropΠ3 λ x y z → is-true-prop (x ⊑ y ⇒ y ⊑ z ⇒ x ⊑ z)

isAntisym : {A : Type ℓ₀} → isSet A → Order ℓ₁ A → hProp (ℓ₀ ⊔ ℓ₁)
isAntisym {A = A} A-set _⊑_ = ⊑-antisym , ⊑-antisym-prop
  where
    ⊑-antisym = (x y : A) → [ x ⊑ y ] → [ y ⊑ x ] → x ≡ y

    ⊑-antisym-prop : isProp ⊑-antisym
    ⊑-antisym-prop = isPropΠ2 λ x y → isPropΠ2 λ _ _ → A-set x y

PosetAx : (A : Type ℓ₀) → Order ℓ₁ A → hProp (ℓ₀ ⊔ ℓ₁)
PosetAx {ℓ₀ = ℓ₀} {ℓ₁ = ℓ₁} A _⊑_ = isAPartialSet , isAPartialSet-prop
  where
    isAPartialSet =
      Σ[ A-set ∈ isSet A ] [ isReflexive _⊑_ ⊓ isTransitive _⊑_ ⊓ isAntisym A-set _⊑_ ]

    isAPartialSet-prop =
      isPropΣ isPropIsSet λ A-set →
        is-true-prop (isReflexive _⊑_ ⊓ isTransitive _⊑_ ⊓ isAntisym A-set _⊑_)
```

A poset structure with level `ℓ₁`.

```
PosetStr : (ℓ₁ : Level) → Type ℓ → Type (ℓ ⊔ suc ℓ₁)
PosetStr ℓ₁ = add-to-structure (Order ℓ₁) λ A _⊑_ → [ PosetAx A _⊑_ ]

PosetStr-set : (ℓ₁ : Level) (A : Type ℓ₀) → isSet (PosetStr ℓ₁ A)
PosetStr-set ℓ₁ A =
  isSetΣ (isSetΠ λ _ → isSetΠ λ _ → isSetHProp) λ _⊑_ →
  isSetΣ (isProp→isSet isPropIsSet) λ A-set →
    isProp→isSet (is-true-prop (isReflexive _⊑_ ⊓ isTransitive _⊑_ ⊓ isAntisym A-set _⊑_))
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

We refer to to the order of `P` as `_⊑[ P ]_`.

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
```

## Monotonic functions

```
isMonotonic : (P : Poset ℓ₀ ℓ₁) (Q : Poset ℓ₂ ℓ₃)
            → (∣ P ∣ₚ → ∣ Q ∣ₚ) → Type (ℓ₀ ⊔ ℓ₁ ⊔ ℓ₃)
isMonotonic P Q f = (x y : ∣ P ∣ₚ) → [ x ⊑[ P ] y ] → [ (f x) ⊑[ Q ] (f y) ]

isMonotonic-prop : (P : Poset ℓ₀ ℓ₁) (Q : Poset ℓ₀′ ℓ₁′) (f : ∣ P ∣ₚ → ∣ Q ∣ₚ)
                 → isProp (isMonotonic P Q f)
isMonotonic-prop P Q f = isPropΠ3 λ x y _ → is-true-prop (f x ⊑[ Q ] f y)
```

We collect monotonic functions in the following type.

```
_─m→_ : Poset ℓ₀ ℓ₁ → Poset ℓ₀′ ℓ₁′ → Type (ℓ₀ ⊔ ℓ₁ ⊔ ℓ₀′ ⊔ ℓ₁′)
_─m→_ P Q = Σ (∣ P ∣ₚ → ∣ Q ∣ₚ) (isMonotonic P Q)

forget-mono : (P : Poset ℓ₀ ℓ₁) (Q : Poset ℓ₀′ ℓ₁′) ((f , f-mono) (g , g-mono) : P ─m→ Q)
            → f ≡ g
            → (f , f-mono) ≡ (g , g-mono)
forget-mono P Q (f , f-mono) (g , g-mono) =
  ΣProp≡ (λ f → isPropΠ3 λ x y x⊑y → is-true-prop (f x ⊑[ Q ] f y))
```

```
isAMonotonicEqv : (P Q : Poset ℓ₀ ℓ₁) → ∣ P ∣ₚ ≃ ∣ Q ∣ₚ → Type (ℓ₀ ⊔ ℓ₁)
isAMonotonicEqv P Q e@(f , _) = isMonotonic P Q f × isMonotonic Q P g
  where
    g = equivFun (invEquiv e)

isAMonotonicEqv-prop : (P Q : Poset ℓ₀ ℓ₁) (eqv : ∣ P ∣ₚ ≃ ∣ Q ∣ₚ)
                     → isProp (isAMonotonicEqv P Q eqv)
isAMonotonicEqv-prop P Q e@(f , _) =
  isPropΣ (isMonotonic-prop P Q f) λ _ → isMonotonic-prop Q P g
  where
    g = equivFun (invEquiv e)

isPosetIso : (P Q : Poset ℓ₀ ℓ₁) → (P ─m→ Q) → Type (ℓ₀ ⊔ ℓ₁)
isPosetIso P Q (f , _) = Σ[ (g , _) ∈ (Q ─m→ P) ] section f g × retract f g

isPosetIso-prop : (P Q : Poset ℓ₀ ℓ₁) (f : P ─m→ Q)
                → isProp (isPosetIso P Q f)
isPosetIso-prop P Q (f , f-mono) (g₀ , sec₀ , ret₀) (g₁ , sec₁ , ret₁) =
  ΣProp≡ NTS g₀=g₁
  where
    NTS : ((g , _) : Q ─m→ P) → isProp (section f g × retract f g)
    NTS (g , g-mono) = isPropΣ
                         (isPropΠ λ x → carrier-is-set Q (f (g x)) x) λ _ →
                          isPropΠ λ x → carrier-is-set P (g (f x)) x

    g₀=g₁ : g₀ ≡ g₁
    g₀=g₁ =
      forget-mono Q P g₀ g₁ (funExt λ x →
        π₀ g₀ x             ≡⟨ sym (cong (λ - → π₀ g₀ -) (sec₁ x)) ⟩
        π₀ g₀ (f (π₀ g₁ x)) ≡⟨ ret₀ (π₀ g₁ x) ⟩
        π₀ g₁ x             ∎)
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
isDownwardsClosed : (P : Poset ℓ₀ ℓ₁) → 𝒫 ∣ P ∣ₚ → hProp (ℓ₀ ⊔ ℓ₁)
isDownwardsClosed P U =
  ((x y : ∣ P ∣ₚ) → [ x ∈ U ] → [ y ⊑[ P ] x ] → [ y ∈ U ]) , prop
  where
    prop : isProp ((x y : ∣ P ∣ₚ) → [ U x ] → [ y ⊑[ P ] x ] → [ U y ])
    prop = isPropΠ λ _ → isPropΠ λ x → isPropΠ λ _ → isPropΠ λ _ → is-true-prop (x ∈ U)

DCSubset : (P : Poset ℓ₀ ℓ₁) → Type (suc ℓ₀ ⊔ ℓ₁)
DCSubset P = Σ[ U ∈ 𝒫 ∣ P ∣ₚ ] [ isDownwardsClosed P U ]

DCSubset-set : (P : Poset ℓ₀ ℓ₁) → isSet (DCSubset P)
DCSubset-set P =
  isSetΣ (𝒫-set ∣ P ∣ₚ) λ U → isProp→isSet (is-true-prop (isDownwardsClosed P U))
```

## Product of two posets

```
_×ₚ_ : (P : Poset ℓ₀ ℓ₁) (Q : Poset ℓ₀′ ℓ₁′) → Poset (ℓ₀ ⊔ ℓ₀′) (ℓ₁ ⊔ ℓ₁′)
P ×ₚ Q = (∣ P ∣ₚ × ∣ Q ∣ₚ) , _⊑_ , carrier-set , (⊑-refl , ⊑-trans , ⊑-antisym)
  where
    _⊑_ : ∣ P ∣ₚ × ∣ Q ∣ₚ → ∣ P ∣ₚ × ∣ Q ∣ₚ → hProp _
    _⊑_ (x₀ , y₀) (x₁ , y₁) = x₀ ⊑[ P ] x₁ ⊓ y₀ ⊑[ Q ] y₁

    carrier-set : isSet (∣ P ∣ₚ × ∣ Q ∣ₚ)
    carrier-set = isSetΣ (carrier-is-set P) λ _ → (carrier-is-set Q)

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
isOrderPreserving : (M N : Σ (Type ℓ₀) (Order ℓ₁)) → (π₀ M → π₀ N) → Type (ℓ₀ ⊔ ℓ₁)
isOrderPreserving (A , _⊑₀_) (B , _⊑₁_) f = (x y : A) → [ x ⊑₀ y ] → [ (f x) ⊑₁ (f y) ]

isOrderPreserving-prop : (M N : Σ (Type ℓ₀) (Order ℓ₁)) (f : π₀ M → π₀ N)
                       → isProp (isOrderPreserving M N f)
isOrderPreserving-prop M (_ , _⊑₁_) f = isPropΠ3 λ x y p → is-true-prop ((f x) ⊑₁ (f y))

isAnOrderPreservingEqv : (M N : Σ (Type ℓ₀) (Order ℓ₁)) → π₀ M ≃ π₀ N → Type (ℓ₀ ⊔ ℓ₁)
isAnOrderPreservingEqv M N e@(f , _) =
  isOrderPreserving M N f × isOrderPreserving N M g
  where
    g = equivFun (invEquiv e)

id-order-preserving : (A : Type ℓ₀) (s : Order ℓ₁ A)
                    → isOrderPreserving (A , s) (A , s) (λ x → x)
id-order-preserving A _⊑₀_ _⊑₁_ _ p = p

Order-set : (ℓ₁ : Level) (A : Type ℓ₀) → isSet (Order ℓ₁ A)
Order-set ℓ₁ A = isSetΠ λ _ → isSetΠ λ _ → isSetHProp

Order-is-SNS : SNS {ℓ} (Order ℓ₁) isAnOrderPreservingEqv
Order-is-SNS {ℓ = ℓ} {ℓ₁ = ℓ₁} {X = X}  _⊑₀_ _⊑₁_ = f , record { equiv-proof = f-equiv }
  where
    f : isAnOrderPreservingEqv (X , _⊑₀_) (X , _⊑₁_) (idEquiv X) → _⊑₀_ ≡ _⊑₁_
    f e@(φ , ψ) = funExt2 (λ x y → ⇔toPath (φ x y) (ψ x y))

    g : _⊑₀_ ≡ _⊑₁_ → isAnOrderPreservingEqv (X , _⊑₀_) (X , _⊑₁_) (idEquiv X)
    g p =
      subst
        (λ _⊑_ → isAnOrderPreservingEqv (X , _⊑₀_) (X , _⊑_) (idEquiv X))
        p
        ((λ _ _ x⊑₁y → x⊑₁y) , λ _ _ x⊑₁y → x⊑₁y)

    ret-f-g : retract f g
    ret-f-g (φ , ψ) =
      isPropΣ (isOrderPreserving-prop (X , _⊑₀_) (X , _⊑₁_) id) (λ _ → isOrderPreserving-prop (X , _⊑₁_) (X , _⊑₀_) id) (g (f (φ , ψ))) (φ , ψ)

    ⇔-prop : isProp ((x y : X) → [ x ⊑₀ y ⇔ x ⊑₁ y ])
    ⇔-prop = isPropΠ λ x → isPropΠ λ y → is-true-prop (x ⊑₀ y ⇔ x ⊑₁ y)

    f-equiv : (p : _⊑₀_ ≡ _⊑₁_) → isContr (fiber f p)
    f-equiv p = ((to , from) , eq) , NTS
      where
        to : isOrderPreserving (X , _⊑₀_) (X , _⊑₁_) id
        to x y = subst (λ _⊑_ → [ x ⊑₀ y ] → [ x ⊑ y ]) p id

        from : isOrderPreserving (X , _⊑₁_) (X , _⊑₀_) id
        from x y = subst (λ _⊑_ → [ x ⊑ y ] → [ x ⊑₀ y ]) p id

        eq : f (to , from) ≡ p
        eq = Order-set ℓ₁ X _⊑₀_ _⊑₁_ (f (to , from)) p

        NTS : (fib : fiber f p) → ((to , from) , eq) ≡ fib
        NTS ((φ , ψ) , eq) =
          ΣProp≡
            (λ i′ → isOfHLevelSuc 2 (Order-set ℓ₁ X) _⊑₀_ _⊑₁_ (f i′) p)
            (ΣProp≡
               (λ _ → isOrderPreserving-prop (X , _⊑₁_) (X , _⊑₀_) id)
               (isOrderPreserving-prop (X , _⊑₀_) (X , _⊑₁_) id to φ))

RP-iso-prop : (P Q : Σ (Type ℓ₀) (Order ℓ₁))
            → (i : π₀ P ≃ π₀ Q) → isProp (isAnOrderPreservingEqv P Q i)
RP-iso-prop M N e@(f , _) =
  isPropΣ (isOrderPreserving-prop M N f) λ _ → isOrderPreserving-prop N M g
  where
    g = equivFun (invEquiv e)

poset-axioms-props : (A : Type ℓ₀) (str : Order ℓ₁ A)
                   → isProp [ PosetAx A str ]
poset-axioms-props {ℓ₁ = ℓ₁} A str = is-true-prop (PosetAx A str)

poset-is-SNS : SNS {ℓ} (PosetStr ℓ₁) isAMonotonicEqv
poset-is-SNS {ℓ₁ = ℓ₁} =
  SNS-PathP→SNS-≡
    (PosetStr ℓ₁)
    isAMonotonicEqv
    (add-axioms-SNS _ poset-axioms-props (SNS-≡→SNS-PathP isAnOrderPreservingEqv Order-is-SNS))

poset-is-SNS-PathP : SNS-PathP {ℓ} (PosetStr ℓ₁) isAMonotonicEqv
poset-is-SNS-PathP = SNS-≡→SNS-PathP isAMonotonicEqv poset-is-SNS

poset-SIP : (A : Type ℓ₀) (B : Type ℓ₀) (eqv : A ≃ B)
            (P : PosetStr ℓ₁ A) (Q : PosetStr ℓ₁ B)
          → isAMonotonicEqv (A , P) (B , Q) eqv
          → (A , P) ≡ (B , Q)
poset-SIP {ℓ₁ = ℓ₁} A B eqv P Q i = foo (eqv , i)
  where
    foo : (A , P) ≃[ isAMonotonicEqv ] (B , Q) → (A , P) ≡ (B , Q)
    foo = equivFun (SIP poset-is-SNS-PathP (A , P) (B , Q))

_≃ₚ_ : Poset ℓ₀ ℓ₁ → Poset ℓ₀ ℓ₁ → Type (ℓ₀ ⊔ ℓ₁)
_≃ₚ_ P Q = Σ[ i ∈ ∣ P ∣ₚ ≃ ∣ Q ∣ₚ ] isAMonotonicEqv P Q i

_≅ₚ_ : Poset ℓ₀ ℓ₁ → Poset ℓ₀ ℓ₁ → Type (ℓ₀ ⊔ ℓ₁)
P ≅ₚ Q = Σ[ f ∈ P ─m→ Q ] isPosetIso P Q f

≃ₚ≃≅ₚ : (P Q : Poset ℓ₀ ℓ₁) → (P ≃ₚ Q) ≃ (P ≅ₚ Q)
≃ₚ≃≅ₚ P Q = isoToEquiv (iso to from sec ret)
  where
    to : P ≃ₚ Q → P ≅ₚ Q
    to (e@(f , _) , (f-mono , g-mono)) =
      (f , f-mono) , (g , g-mono) , (Iso.rightInv (equivToIso e)) , (Iso.leftInv (equivToIso e))
      where
        g = equivFun (invEquiv e)

    from : P ≅ₚ Q → P ≃ₚ Q
    from ((f , f-mono) , ((g , g-mono) , sec , ret)) = isoToEquiv is , f-mono , g-mono
      where
        is : Iso ∣ P ∣ₚ ∣ Q ∣ₚ
        is = iso f g sec ret

    sec : section to from
    sec (f , _) = ΣProp≡ (isPosetIso-prop P Q) refl

    ret : retract to from
    ret (e , _) = ΣProp≡ (isAMonotonicEqv-prop P Q) (ΣProp≡ isPropIsEquiv refl)
```

The main result is the following: *the category of posets is univalent*.

```
poset-univ : (P Q : Poset ℓ₀ ℓ₁) → (P ≅ₚ Q) ≃ (P ≡ Q)
poset-univ P Q =
  P ≅ₚ Q   ≃⟨ invEquiv (≃ₚ≃≅ₚ P Q) ⟩
  P ≃ₚ Q   ≃⟨ SIP poset-is-SNS-PathP P Q ⟩ P ≡ Q QED

pos-iso-to-eq : (P Q : Poset ℓ₀ ℓ₁) → P ≃ₚ Q → P ≡ Q
pos-iso-to-eq (A , A-pos) (B , B-pos) (eqv , i) = poset-SIP A B eqv A-pos B-pos i

≃⋆→≃ₚ′ : (P Q : Poset ℓ₀ ℓ₁) → P ≅ₚ Q → P ≃ₚ Q
≃⋆→≃ₚ′ P Q ((f , f-mono) , (g , g-mono) , sec , ret) =
  isoToEquiv (iso f g sec ret) , f-mono , g-mono

-- --}
-- --}
-- --}
```
