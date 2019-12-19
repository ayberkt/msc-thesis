{-# OPTIONS --without-K --cubical --safe #-}

module Powerset where

open import Basis

𝒫 : Type ℓ → Type (suc ℓ)
𝒫 {ℓ} A = A → Ω ℓ

𝒫-set : (A : Type ℓ) → IsSet (𝒫 A)
𝒫-set A = {!!}

_⊆_ : 𝒫 A → 𝒫 A → Ω _
_⊆_ {A = A} U V = ((x : A) → U x is-true → V x is-true) , prop
  where
    prop : IsProp ((x : A) → U x is-true → V x is-true)
    prop = ∏-prop λ x → ∏-prop λ _ → is-true-prop (V x)
