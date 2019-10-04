module PostSystem where

open import Common
open import Homotopy

variable
  ℓ : Level

PostSystemStr : Set ℓ → Set (suc (suc ℓ))
PostSystemStr X = X → 𝒫 (𝒫 X)

PostSystem : (ℓ : Level) → Set (suc (suc ℓ))
PostSystem ℓ = Σ (Set ℓ) PostSystemStr

∣_∣ : PostSystem ℓ → Set ℓ
∣ X , _ ∣ = X

Cov : (PS : PostSystem ℓ) → PostSystemStr ∣ PS ∣
Cov (_ , c) = c

module _ (PS : PostSystem ℓ) where

  mutual

    data _◀_ : ∣ PS ∣ → 𝒫 ∣ PS ∣ → Set (suc ℓ) where
      C₁ : (U   : 𝒫 ∣ PS ∣) (u : ∣ PS ∣) → u ∈ U                 → u ◀ U
      C₂ : (U S : 𝒫 ∣ PS ∣) (u : ∣ PS ∣) → S ∈ Cov PS u → S ◀ₛ U → u ◀ U

    _◀ₛ_ : 𝒫 ∣ PS ∣ → 𝒫 ∣ PS ∣ → Set (suc ℓ)
    _◀ₛ_ S U = (s : ∣ PS ∣) → s ∈ S → s ◀ U
