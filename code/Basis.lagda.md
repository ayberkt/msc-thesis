```
{-# OPTIONS --without-K --cubical --safe #-}

module Basis where

open import Cubical.Core.Everything         public using    ( _≡_
                                                            ; Type
                                                            ; Σ
                                                            ; Σ-syntax
                                                            ; _,_
                                                            ; _≃_
                                                            ; equivFun
                                                            ; isEquiv
                                                            ; equivProof
                                                            )
open import Cubical.Data.Sigma.Properties   public using    ( ΣProp≡ )
open import Cubical.Foundations.Prelude     public using    ( J
                                                            ; funExt
                                                            ; subst
                                                            ; isProp
                                                            ; isSet
                                                            ; isProp→isSet
                                                            ; cong; refl; sym
                                                            ; _≡⟨_⟩_; _∎
                                                            ; transport
                                                            ; transportRefl
                                                            ; isContr)
open import Cubical.Foundations.Transport   public using    ( transportEquiv )
open import Cubical.Foundations.Equiv       public using    ( idEquiv
                                                            ; invEquiv
                                                            ; secEq
                                                            ; retEq
                                                            ; fiber
                                                            )
open import Cubical.Foundations.Equiv.HalfAdjoint public using
  ( isHAEquiv ; equiv→HAEquiv )
open import Cubical.Foundations.Univalence  public using    ( ua )
open import Cubical.Foundations.HLevels     public using    ( hProp
                                                            ; isSetHProp
                                                            ; isPropIsSet
                                                            ; isOfHLevelΣ
                                                            ; isOfHLevelSuc
                                                            ; isSetΣ
                                                            ; isSetΠ
                                                            ; isPropΠ
                                                            )
open import Cubical.Data.Sigma              public using    ( sigmaPath→pathSigma
                                                            ; pathSigma→sigmaPath
                                                            ; _×_
                                                            ; _,_
                                                            )
                                                   renaming ( fst to π₀
                                                            ; snd to π₁
                                                            )
open import Cubical.Foundations.Isomorphism public using    ( isoToPath
                                                            ; isoToEquiv
                                                            ; iso
                                                            ; section
                                                            ; retract
                                                            )
open import Cubical.Foundations.Logic       public using    ( _⇔_
                                                            ; _⇒_
                                                            ; ⇔toPath
                                                            ; _⊓_
                                                            ; [_]
                                                            )
open import Function                        public using    ( _∘_
                                                            ; id
                                                            )
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
