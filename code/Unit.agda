{-# OPTIONS --without-K #-}

module Unit where

open import HLevels
open import Common

data ⊤ {ℓ : Level} : Set ℓ where
  tt : ⊤

⊤-prop : {ℓ : Level} → IsProp {ℓ = ℓ} ⊤
⊤-prop tt tt = refl
