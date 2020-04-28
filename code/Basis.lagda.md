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
open import Cubical.Data.Sigma.Properties   public using    ( Σ≡; ΣProp≡ )
open import Cubical.Foundations.Prelude     public using    ( J
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
open import Cubical.Foundations.Univalence  public using    ( ua )
open import Cubical.Foundations.HLevels     public using    ( hProp
                                                            ; isSetHProp
                                                            ; isPropIsSet
                                                            ; isOfHLevelΣ
                                                            ; isOfHLevelSuc
                                                            )
open import Cubical.Data.Sigma              public using    ( sigmaPath→pathSigma
                                                            ; pathSigma→sigmaPath
                                                            ; _×_
                                                            ; _,_
                                                            )
                                                   renaming ( fst to π₀
                                                            ; snd to π₁ )
open import Cubical.Foundations.Isomorphism public using    ( isoToPath
                                                            ; iso
                                                            ; section
                                                            ; retract)
open import Cubical.Foundations.Logic       public using    ( _⇔_; _⇒_; ⇔toPath ; _⊓_ ; [_])
open import Function                        public using    ( _∘_; id )
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

## Function extensionality

```
fn-ext : (f g : (x : A) → B x) → ((x : A) → f x ≡ g x) → f ≡ g
fn-ext f g f~g i x = f~g x i
```

## Propositions

```
IsProp-prop : isProp (isProp A)
IsProp-prop {A = A} A-prop₀ A-prop₁ =
  fn-ext A-prop₀ A-prop₁ rem
  where
    rem : (x : A) → A-prop₀ x ≡ A-prop₁ x
    rem = λ x → fn-ext (A-prop₀ x) (A-prop₁ x) λ y →
            isProp→isSet A-prop₀ x y (A-prop₀ x y) (A-prop₁ x y)

is-true-prop : (P : hProp ℓ) → isProp [ P ]
is-true-prop (P , P-prop) = P-prop
```

```
∏-prop : ((x : A) → isProp (B x)) → isProp ((x : A) → B x)
∏-prop B-prop x y = fn-ext x y λ x′ → B-prop x′ (x x′) (y x′)
```

```
∃_ : {A : Type ℓ₀} → (A → hProp ℓ₁) → Type (ℓ₀ ⊔ ℓ₁)
∃_ {A = A} P = Σ[ x ∈ A ] [ P x ]
```

## Sets

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
∏-set : ((x : A) → isSet (B x)) → isSet ((x : A) → B x)
∏-set {A = A} B-set f g = NTS
  where
    rem1 : isProp (f ~ g)
    rem1 p q = ⟨ i ⟩ λ x → B-set x (f x) (g x) (p x) (q x) i

    NTS : isProp (f ≡ g)
    NTS p q = subst isProp (id-∏ f g) rem1 p q
```

```
Σ-set : isSet A → ((x : A) → isSet (B x)) → isSet (Σ A B)
Σ-set = isOfHLevelΣ 2
```

```
to-subtype-≡ : (p q : Σ A B)
             → ((x : A) → isProp (B x))
             → π₀ p ≡ π₀ q → p ≡ q
to-subtype-≡ _ _ B-prop eq = ΣProp≡ B-prop eq
```
