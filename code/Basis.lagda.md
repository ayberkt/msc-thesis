```
{-# OPTIONS --without-K --cubical --safe #-}

module Basis where

open import Cubical.Core.Everything         public using    (_≡_; Type; Σ; _,_)
open import Cubical.Foundations.Prelude     public using    (J; subst; cong; refl)
open import Cubical.Foundations.Univalence  public using    (ua)
open import Cubical.Foundations.Isomorphism public using    (isoToPath; iso; section)
open import Data.Product                    public using    (_×_)
                                                   renaming (proj₁ to π₀; proj₂ to π₁)
open import Function                        public using    (_∘_; id)
open import Level                           public
```

```
variable
  ℓ ℓ₀ ℓ₁ ℓ₂ : Level

variable
  A    : Type ℓ₀
  A₀   : Type ℓ₁
  B    : A → Type ℓ₁
```

## Function extensionality

```
fn-ext : (f g : (x : A) → B x) → ((x : A) → f x ≡ g x) → f ≡ g
fn-ext f g f~g i x = f~g x i
```

## Propositions

```
IsProp : Type ℓ → Type ℓ
IsProp A = (x y : A) → x ≡ y

Ω : (ℓ : Level) → Set (suc ℓ)
Ω ℓ = Σ (Type ℓ) IsProp

_is-true : Ω ℓ → Type ℓ
(P , _) is-true = P

is-true-prop : (P : Ω ℓ) → IsProp (P is-true)
is-true-prop (P , P-prop) = P-prop

infix 5 _is-true
```

```
∏-prop : ((x : A) → IsProp (B x)) → IsProp ((x : A) → B x)
∏-prop B-prop x y = fn-ext x y λ x′ → B-prop x′ (x x′) (y x′)
```

## Sets

```
IsSet : Type ℓ → Type ℓ
IsSet A = (x y : A) → IsProp (x ≡ y)
```

```
path-abs : A → A
path-abs x = x

syntax path-abs (λ i → e) = ⟨ i ⟩ e
```

## Univalence

## Extensional equality

```
_~_ : (f g : (x : A) → B x) → Type _
_~_ {A = A} f g = (x : A) → f x ≡ g x
```

```
id-∏ : (f g : (x : A) → B x) → (f ~ g) ≡ (f ≡ g)
id-∏ f g = isoToPath (iso F G (λ _ → refl) (λ _ → refl))
  where
    F : f ~ g → f ≡ g
    F f~g = ⟨ i ⟩ λ x → f~g x i

    G : f ≡ g → f ~ g
    G f=g = λ x → ⟨ i ⟩ f=g i x
```

```
∏-set : ((x : A) → IsSet (B x)) → IsSet ((x : A) → B x)
∏-set {A = A} B-set f g = NTS
  where
    rem1 : IsProp (f ~ g)
    rem1 p q = ⟨ i ⟩ λ x → B-set x (f x) (g x) (p x) (q x) i

    NTS : IsProp (f ≡ g)
    NTS p q = subst IsProp (id-∏ f g) rem1 p q
```
