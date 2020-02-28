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
open import Cubical.Data.Prod               public using    (_,_; proj₁; proj₂)
                                                   renaming (_×_ to _××_)
open import Cubical.Data.Sigma.Properties   public using    ( Σ≡)
open import Cubical.Foundations.Prelude     public using    ( J
                                                            ; subst
                                                            ; cong; refl; sym
                                                            ; _≡⟨_⟩_; _∎
                                                            ; transport
                                                            ; transportRefl
                                                            ; isContr)
                                                   renaming ( isProp       to IsProp
                                                            ; isSet        to IsSet
                                                            ; isProp→isSet to prop⇒set )
open import Cubical.Foundations.Transport   public using    ( transportEquiv )
open import Cubical.Foundations.Equiv       public using    ( idEquiv; invEquiv; secEq; retEq; fiber )
open import Cubical.Foundations.SIP         public using    ( SNS; SNS'; join-SNS'
                                                            ; SNS''
                                                            ; SNS'''
                                                            ; SNS'≡SNS''
                                                            ; SNS→SNS'
                                                            ; SNS''→SNS'''
                                                            ; add-to-structure
                                                            ; add-to-iso
                                                            ; add-axioms-SNS'
                                                            ; pointed-structure
                                                            ; Pointed-Type
                                                            ; pointed-iso
                                                            ; pointed-is-SNS'
                                                            ; sip
                                                            ; SIP
                                                            ; _≃[_]_)
open import Cubical.Foundations.Univalence  public using    ( ua )
open import Cubical.Foundations.HLevels     public using    ( hProp
                                                            ; isSetHProp
                                                            ; isPropIsSet
                                                            ; isOfHLevelΣ
                                                            ; ΣProp≡
                                                            ; hLevelSuc )
open import Cubical.Data.Sigma              public using    ( sigmaPath→pathSigma
                                                            ; pathSigma→sigmaPath )
open import Cubical.Foundations.Isomorphism public using    ( isoToPath; iso; section; retract)
open import Cubical.Foundations.Logic       public using    ( _⇔_; _⇒_; ⇔toPath )
                                                   renaming ( _⊓_ to _∧_)
open import Data.Product                    public using    ( _×_; uncurry)
                                                   renaming ( proj₁ to π₀
                                                            ; proj₂ to π₁)
open import Function                        public using    (_∘_; id)
open import Level                           public
```

```
variable
  ℓ ℓ₀ ℓ₁ ℓ₂ ℓ₃ ℓ₀′ ℓ₁′ ℓ₂′ ℓ₀′′ ℓ₁′′ ℓ₂′′ : Level

variable
  A    : Type ℓ₀
  B    : A → Type ℓ₀
  A₀   : Type ℓ₁
```

## Function extensionality

```
fn-ext : (f g : (x : A) → B x) → ((x : A) → f x ≡ g x) → f ≡ g
fn-ext f g f~g i x = f~g x i
```

## Propositions

```
IsProp-prop : IsProp (IsProp A)
IsProp-prop {A = A} A-prop₀ A-prop₁ =
  fn-ext A-prop₀ A-prop₁ rem
  where
    rem : (x : A) → A-prop₀ x ≡ A-prop₁ x
    rem = λ x → fn-ext (A-prop₀ x) (A-prop₁ x) λ y →
            prop⇒set A-prop₀ x y (A-prop₀ x y) (A-prop₁ x y)

Ω : (ℓ : Level) → Set (suc ℓ)
Ω ℓ = hProp ℓ

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

```
Σ-set : IsSet A → ((x : A) → IsSet (B x)) → IsSet (Σ A B)
Σ-set = isOfHLevelΣ 2
```

```
to-subtype-≡ : (p q : Σ A B)
             → ((x : A) → IsProp (B x))
             → π₀ p ≡ π₀ q → p ≡ q
to-subtype-≡ _ _ B-prop eq = ΣProp≡ B-prop eq
```
