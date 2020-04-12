{-# OPTIONS --cubical #-}

module Writing where

open import Cubical.Core.Everything  hiding   (_≃_; isEquiv)
open import Cubical.Foundations.Prelude   using    (_≡⟨_⟩_; _∎; subst; refl)
open import Data.Product             using    (Σ; _,_; _×_)
                                     renaming (proj₁ to pr₁; proj₂ to pr₂)
open import Data.Nat                 using    (ℕ; suc; zero)
open import Function                 using    (_∘_)
open import Level

variable
  ℓ ℓ′ ℓ₀ ℓ₁ : Level
  A          : Type ℓ₀
  B          : Type ℓ₁

isContr : (A : Type ℓ) → Type ℓ
isContr A = Σ[ c ∈ A ] ((x : A) → c ≡ x)

isOfHLevel : ℕ → (A : Type ℓ) → Type ℓ
isOfHLevel zero    A = isContr A
isOfHLevel (suc n) A = (x y : A) → isContr (x ≡ y)

isProp : (A : Type ℓ) → Type ℓ
isProp = isOfHLevel 1

isProp′ : (A : Type ℓ) → Type ℓ
isProp′ A = (x y : A) → x ≡ y

fiber : {A : Type ℓ₀} {B : Type ℓ₁} → (A → B) → B → Type (ℓ-max ℓ₀ ℓ₁)
fiber {A = A} f y = Σ[ x ∈ A ] f x ≡ y

isEquiv : {A : Type ℓ₀} {B : Type ℓ₁} (f : A → B) → Type (ℓ-max ℓ₀ ℓ₁)
isEquiv {B = B} f = (y : B) → isContr (fiber f y)

_≃_ : (A : Type ℓ₀) (B : Type ℓ₁) → Type (ℓ-max ℓ₀ ℓ₁)
A ≃ B = Σ[ f ∈ (A → B) ] (isEquiv f)

_↔_ : (A : Type ℓ₀) (B : Type ℓ₁) → Type (ℓ-max ℓ₀ ℓ₁)
A ↔ B = (A → B) × (B → A)

postulate isProp↔isProp′ : (A : Type ℓ) → isProp A ↔ isProp′ A

↔⇒≃-for-props : (A : Type ℓ₀) (B : Type ℓ₁) → isProp A → isProp B → A ↔ B → A ≃ B
↔⇒≃-for-props A B A-prop B-prop (f , g) =
    f
  , (λ y → (g y , pr₁ (isProp↔isProp′ B) B-prop (f (g y)) y)
           , {!λ { (c , eq) → ? }!})
