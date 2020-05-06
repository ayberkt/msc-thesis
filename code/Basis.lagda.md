```
{-# OPTIONS --without-K --cubical --safe #-}

module Basis where

open import Level public

import Cubical.Core.Everything               as CE
import Cubical.Data.Sigma                    as DS
import Cubical.Foundations.Prelude           as FP
import Cubical.Foundations.Equiv             as FE
import Cubical.Foundations.Logic             as FL
import Cubical.Foundations.HLevels           as FH
import Cubical.Foundations.Isomorphism       as FI
import Cubical.Foundations.Equiv.HalfAdjoint as HAE

open CE  public using    (_≡_; Type; Σ; Σ-syntax; _,_; _≃_; equivFun; isEquiv)
open DS  public using    (ΣProp≡; sigmaPath→pathSigma; pathSigma→sigmaPath; _×_; _,_)
                renaming (fst to π₀; snd to π₁)
open FP  public using    (funExt; subst; isContr; isProp; isSet; isProp→isSet; cong; refl;
                          sym; _≡⟨_⟩_; _∎; transport; transportRefl)
open FE  public using    (idEquiv; invEquiv; secEq; retEq; fiber)
open FL  public using    ( _⇔_ ; _⇒_ ; ⇔toPath ; _⊓_ ; [_] )
open FH  public using    (hProp; isSetHProp; isPropIsSet; isPropΣ; isOfHLevelSuc; isSetΣ;
                          isSetΠ; isPropΠ; isPropΠ2; isPropΠ3)
open FI  public using    (isoToPath; isoToEquiv; iso; section; retract )
open HAE public using    (isHAEquiv; equiv→HAEquiv)

```

```
variable
  ℓ ℓ′ ℓ₀ ℓ₁ ℓ₂ ℓ₃ ℓ₀′ ℓ₁′ ℓ₂′ ℓ₀′′ ℓ₁′′ ℓ₂′′ : Level

variable
  A    : Type ℓ₀
  B    : A → Type ℓ₀
  A₀   : Type ℓ₁
```

## The unit type

```
data Unit (ℓ : Level) : Type ℓ where
  tt : Unit ℓ

Unit-prop : {ℓ : Level} → isProp (Unit ℓ)
Unit-prop tt tt = refl
```

## Propositions

```
is-true-prop : (P : hProp ℓ) → isProp [ P ]
is-true-prop (P , P-prop) = P-prop
```

```
∃_ : {A : Type ℓ₀} → (A → hProp ℓ₁) → Type (ℓ₀ ⊔ ℓ₁)
∃_ {A = A} P = Σ[ x ∈ A ] [ P x ]
```

## Extensional equality

```
_~_ : (f g : (x : A) → B x) → Type _
_~_ {A = A} f g = (x : A) → f x ≡ g x
```

```
funExt2 : {A₀ : Type ℓ₀} {A₁ : Type ℓ₂} {B : A₀ → A₁ → Type ℓ₃}
        → {f g : (x : A₀) (y : A₁) → B x y} → ((x : A₀) (y : A₁) → f x y ≡ g x y) → f ≡ g
funExt2 eq = funExt λ x → funExt λ y → eq x y
```

## Truncation

```
data ∥_∥ (A : Type ℓ) : Type ℓ where
  ∣_∣    : A → ∥ A ∥
  squash : (x y : ∥ A ∥) → x ≡ y

∥∥-prop : (A : Type ℓ) → isProp ∥ A ∥
∥∥-prop _ = squash

∥∥-rec : {X Y : Type ℓ} → isProp Y → (X → Y) → ∥ X ∥ → Y
∥∥-rec Y-prop f ∣ x ∣                = f x
∥∥-rec Y-prop f (squash ∣x∣₀ ∣x∣₁ i) =
  Y-prop (∥∥-rec Y-prop f ∣x∣₀) (∥∥-rec Y-prop f ∣x∣₁) i
```
