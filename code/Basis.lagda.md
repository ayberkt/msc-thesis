```
{-# OPTIONS --without-K --cubical --safe #-}

module Basis where

import Cubical.Core.Everything         as CE
import Cubical.Data.Sigma              as DS
import Cubical.Foundations.Prelude     as FP
import Cubical.Foundations.Equiv       as FE
import Cubical.Foundations.Logic       as FL
import Cubical.Foundations.HLevels     as FH
import Cubical.Foundations.Isomorphism as FI

open CE public using    (_≡_; Type; Σ; Σ-syntax; _,_; _≃_; equivFun; isEquiv)
open DS public using    (ΣProp≡; sigmaPath→pathSigma; pathSigma→sigmaPath; _×_; _,_)
               renaming (fst to π₀; snd to π₁)
open FP public using    (funExt; subst; isContr; isProp; isSet; isProp→isSet)
open FE public using    (idEquiv; invEquiv; secEq; retEq; fiber)
open FL public using    ( _⇔_ ; _⇒_ ; ⇔toPath ; _⊓_ ; [_] )
open FH public using    (hProp; isSetHProp; isPropIsSet; isPropΣ; isOfHLevelSuc; isSetΣ; isSetΠ; isPropΠ)
open FI public using    (isoToPath; isoToEquiv; iso; section; retract )
  
open import Cubical.Foundations.Prelude     public using    ( cong; refl; sym
                                                            ; _≡⟨_⟩_; _∎
                                                            ; transport
                                                            ; transportRefl )

open import Cubical.Foundations.Equiv.HalfAdjoint public using (isHAEquiv; equiv→HAEquiv )


open import Level                           public
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
