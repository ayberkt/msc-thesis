{-# OPTIONS --cubical --safe #-}

module Unit where

open import Basis

data Unit (ℓ : Level) : Type ℓ where
  tt : Unit ℓ

Unit-prop : {ℓ : Level} → IsProp (Unit ℓ)
Unit-prop tt tt = refl
