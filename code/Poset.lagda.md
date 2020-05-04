```
{-# OPTIONS --without-K --cubical --safe #-}

module Poset where

open import Basis
open import Cubical.Foundations.SIP renaming (SNS-≡ to SNS)
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
isMonotonic-prop P Q f =
  isPropΠ (λ x → isPropΠ λ y → isPropΠ λ _ → is-true-prop (f x ⊑[ Q ] f y))

```

We collect monotonic functions in the following type.

```
_─m→_ : Poset ℓ₀ ℓ₁ → Poset ℓ₀′ ℓ₁′ → Type (ℓ₀ ⊔ ℓ₁ ⊔ ℓ₀′ ⊔ ℓ₁′)
_─m→_ P Q = Σ (∣ P ∣ₚ → ∣ Q ∣ₚ) (isMonotonic P Q)
```

```
poset-iso′ : (P Q : Poset ℓ₀ ℓ₁) → ∣ P ∣ₚ ≃ ∣ Q ∣ₚ → Type (ℓ₀ ⊔ ℓ₁)
poset-iso′ P Q e = isMonotonic P Q f × isMonotonic Q P g
  where
    f = π₀ (equiv→HAEquiv e)
    g = isHAEquiv.g (π₁ (equiv→HAEquiv e))

poset-iso′′ : (P Q : Poset ℓ₀ ℓ₁) → (P ─m→ Q) → Type (ℓ₀ ⊔ ℓ₁)
poset-iso′′ P Q (f , _) = Σ[ (g , _) ∈ (Q ─m→ P) ] section f g × retract f g
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
order-iso : (M N : Σ (Type ℓ₀) (Order ℓ₁)) → π₀ M ≃ π₀ N → Type (ℓ₀ ⊔ ℓ₁)
order-iso (A , _⊑₀_) (B , _⊑₁_) eqv =
  (x y : A) → [ x ⊑₀ y ⇔ f x ⊑₁ f y ]
  where
    f = equivFun eqv

isSet-Order : (ℓ₁ : Level) (A : Type ℓ₀) → isSet (Order ℓ₁ A)
isSet-Order ℓ₁ A = isSetΠ λ _ → isSetΠ λ _ → isSetHProp

Order-is-SNS : SNS {ℓ} (Order ℓ₁) order-iso
Order-is-SNS {ℓ₁ = ℓ₁} {X = X}  _⊑₀_ _⊑₁_ = f , f-equiv
  where
    f : order-iso (X , _⊑₀_) (X , _⊑₁_) (idEquiv X) → _⊑₀_ ≡ _⊑₁_
    f i = funExt λ x → funExt λ y → ⇔toPath (π₀ (i x y)) (π₁ (i x y))

    ⇔-prop : isProp ((x y : X) → [ x ⊑₀ y ⇔ x ⊑₁ y ])
    ⇔-prop = isPropΠ λ x → isPropΠ λ y → is-true-prop (x ⊑₀ y ⇔ x ⊑₁ y)

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


RP-iso-prop : (P Q : Σ (Type ℓ₀) (Order ℓ₁))
            → (i : π₀ P ≃ π₀ Q) → isProp (order-iso P Q i)
RP-iso-prop (A , _⊑₀_) (B , _⊑₁_) i =
  isPropΠ λ x → isPropΠ λ y → is-true-prop (x ⊑₀ y ⇔ f x ⊑₁ f y)
  where
    f = equivFun i

poset-iso : (P Q : Poset ℓ₀ ℓ₁) → ∣ P ∣ₚ ≃ ∣ Q ∣ₚ → Type (ℓ₀ ⊔ ℓ₁)
poset-iso {ℓ₁ = ℓ₁} = add-to-iso order-iso λ A _⊑_ → [ PosetAx A _⊑_ ]

poset-iso⇔poset-iso′ : (P Q : Poset ℓ₀ ℓ₁) (e : ∣ P ∣ₚ ≃ ∣ Q ∣ₚ)
                     → (poset-iso P Q e → poset-iso′ P Q e)
                     × (poset-iso′ P Q e → poset-iso P Q e)
poset-iso⇔poset-iso′ P Q e = to , from
  where
    f   = π₀ (equiv→HAEquiv e)
    g   = isHAEquiv.g (π₁ (equiv→HAEquiv e))
    sec : section f g
    sec = isHAEquiv.ret (π₁ (equiv→HAEquiv e))
    ret : retract f g
    ret = isHAEquiv.sec (π₁ (equiv→HAEquiv e))

    to : poset-iso P Q e → poset-iso′ P Q e
    to i = f-mono , g-mono
      where

        f-mono : isMonotonic P Q f
        f-mono x y x⊑y = π₀ (i x y) x⊑y
        g-mono : isMonotonic Q P g
        g-mono x y x⊑y =  π₁ (i (g x) (g y)) NTS
          where
            NTS : [ f (g x) ⊑[ Q ] (f (g y)) ]
            NTS = subst (λ - → [ rel Q (- x) (- y) ]) (sym (funExt sec)) x⊑y

    from : poset-iso′ P Q e → poset-iso P Q e
    from i x y = φ , ψ
      where
        φ : [ x ⊑[ P ] y ] → [ f x ⊑[ Q ] f y ]
        φ x⊑y = π₀ i x y x⊑y
        ψ : [ f x ⊑[ Q ] f y ] → [ x ⊑[ P ] y ]
        ψ fx⊑fy = subst (λ - → [ - x ⊑[ P ] - y ]) (funExt ret) (π₁ i (f x) (f y) fx⊑fy)

poset-axioms-props : (A : Type ℓ₀) (str : Order ℓ₁ A)
                   → isProp [ PosetAx A str ]
poset-axioms-props {ℓ₁ = ℓ₁} A str = is-true-prop (PosetAx A str)


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

_≃ₚ′_ : Poset ℓ₀ ℓ₁ → Poset ℓ₀ ℓ₁ → Type (ℓ₀ ⊔ ℓ₁)
P ≃ₚ′ Q = Σ[ eqv ∈ (∣ P ∣ₚ ≃ ∣ Q ∣ₚ) ] poset-iso′ P Q eqv

_≃⋆_ : Poset ℓ₀ ℓ₁ → Poset ℓ₀ ℓ₁ → Type (ℓ₀ ⊔ ℓ₁)
P ≃⋆ Q = Σ[ f ∈ (P ─m→ Q) ] poset-iso′′ P Q f

pos-iso-to-eq : (P Q : Poset ℓ₀ ℓ₁) → P ≃ₚ Q → P ≡ Q
pos-iso-to-eq (A , A-pos) (B , B-pos) (eqv , i) = poset-SIP A B eqv A-pos B-pos i

pos-iso-to-eq′ : (P Q : Poset ℓ₀ ℓ₁) → P ≃ₚ′ Q → P ≡ Q
pos-iso-to-eq′ P Q (eqv , i-homo) =
  pos-iso-to-eq P Q (eqv , π₁ (poset-iso⇔poset-iso′ P Q eqv) i-homo)

≃⋆→≃ₚ′ : (P Q : Poset ℓ₀ ℓ₁) → P ≃⋆ Q → P ≃ₚ′ Q
≃⋆→≃ₚ′ P Q ((f , f-mono) , (g , g-mono) , sec , ret) =
  isoToEquiv (iso f g sec ret) , f-mono , g-mono

-- --}
-- --}
-- --}
```
