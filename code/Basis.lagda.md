```
{-# OPTIONS --without-K --cubical --safe #-}

module Basis where

open import Cubical.Core.Everything public  using    (_≡_; Type; Σ; _,_)
open import Cubical.Foundations.Prelude public using (J; subst)
open import Data.Product            public  using    ()
                                            renaming (proj₁ to π₀; proj₂ to π₁)
open import Function                public  using    (_∘_; id)
open import Level                   public
```

```
variable
  ℓ ℓ₀ ℓ₁ ℓ₂ : Level

variable
  A : Type ℓ₀
  B : A → Type ℓ₁
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
IsSet : Type ℓ → Type ℓ
IsSet A = (x y : A) → IsProp (x ≡ y)
```

```
∏-prop : ((x : A) → IsProp (B x)) → IsProp ((x : A) → B x)
∏-prop B-prop x y = fn-ext x y λ x′ → B-prop x′ (x x′) (y x′)
```
