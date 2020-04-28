{-# OPTIONS --without-K --cubical --safe #-}

module Powerset where

open import Basis

𝒫 : Type ℓ → Type (suc ℓ)
𝒫 {ℓ} A = A → hProp ℓ

_∈_ : A → 𝒫 A → hProp _
x ∈ U = U x

𝒫-set : (A : Type ℓ) → isSet (𝒫 A)
𝒫-set A = isSetΠ λ _ → isSetHProp

variable
  U V : 𝒫 A

_⊆⊆_ : {A : Type ℓ} → (A → Type ℓ₀) → (A → Type ℓ₁) → Type (ℓ ⊔ ℓ₀ ⊔ ℓ₁)
_⊆⊆_ {A = A} U V =  (x : A) → U x → V x

_⊆_ : {A : Type ℓ} → 𝒫 A → 𝒫 A → hProp ℓ
_⊆_ {A = A} U V = ((λ - → [ U - ]) ⊆⊆ (λ - → [ V - ])) , prop
  where
    prop : isProp ((x : A) → [ U x ] → [ V x ])
    prop = ∏-prop λ x → ∏-prop λ _ → is-true-prop (V x)

⊆-antisym : [ U ⊆ V ] → [ V ⊆ U ] → U ≡ V
⊆-antisym {U = U} {V} U⊆V V⊆V = funExt (λ x → ⇔toPath (U⊆V x) (V⊆V x))

_∩_ : 𝒫 A → 𝒫 A → 𝒫 A
_∩_ {A = A} U V = λ x → ([ U x ] × [ V x ]) , prop x
  where
    prop : (x : A) → isProp ([ U x ] × [ V x ])
    prop x = isOfHLevelΣ 1 (is-true-prop (U x)) λ _ → is-true-prop (V x)
