module Truncation where

open import Common

data ∥_∥ {ℓ : Level} (A : Set ℓ) : Set ℓ where
  ∣_∣ : A → ∥ A ∥

postulate
  squash : {ℓ : Level} {A : Set ℓ} → (x y : ∥ A ∥) → x ≡ y
