{-# OPTIONS --without-K --cubical --safe #-}

module Powerset where

open import Basis

𝒫 : Type ℓ → Type (suc ℓ)
𝒫 {ℓ} A = A → Ω ℓ

𝒫-set : (A : Type ℓ) → IsSet (𝒫 A)
𝒫-set A = ∏-set λ _ → isSetHProp

variable
  U V : 𝒫 A

_⊆_ : 𝒫 A → 𝒫 A → Ω _
_⊆_ {A = A} U V = ((x : A) → U x is-true → V x is-true) , prop
  where
    prop : IsProp ((x : A) → U x is-true → V x is-true)
    prop = ∏-prop λ x → ∏-prop λ _ → is-true-prop (V x)

⊆-antisym : U ⊆ V is-true → V ⊆ U is-true → U ≡ V
⊆-antisym {U = U} {V} U⊆V V⊆V = fn-ext U V (λ x → ⇔toPath (U⊆V x) (V⊆V x))

_∩_ : 𝒫 A → 𝒫 A → 𝒫 A
_∩_ {A = A} U V = λ x → (U x is-true × V x is-true) , prop x
  where
    prop : (x : A) → IsProp (U x is-true × V x is-true)
    prop x = isOfHLevelΣ 1 (is-true-prop (U x)) λ _ → is-true-prop (V x)
