{-# OPTIONS --without-K --cubical --safe #-}

module Powerset where

open import Basis

𝒫 : Type ℓ → Type (suc ℓ)
𝒫 {ℓ} A = A → Ω ℓ

_⊆_ : 𝒫 A → 𝒫 A → Type _
_⊆_ {A = A} U V = (x : A) → U x is-true → V x is-true
