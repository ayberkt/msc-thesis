{-# OPTIONS --cubical --safe #-}

module Unit where

open import Basis

data N₁ {ℓ : Level} : Set ℓ where
  tt : N₁

N₁-prop : {ℓ : Level} → IsProp {ℓ = ℓ} N₁
N₁-prop tt tt = refl
