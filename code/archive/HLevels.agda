{-# OPTIONS --without-K #-}

module HLevels where

open import Common

private
  variable
    ℓ ℓ′ : Level

-- Contractibility.
IsContractible : Set ℓ → Set ℓ
IsContractible X = Σ X (λ c → (x : X) → c ≡ x)

-- Propositionality.
IsProp : Set ℓ → Set ℓ
IsProp A = (x y : A) → x ≡ y

-- Set-ness.
IsSet : Set ℓ → Set ℓ
IsSet A = (x y : A) → (p q : x ≡ y) → p ≡ q
