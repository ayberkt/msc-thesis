module PostSystem where

open import Common
open import Subset using (SubP; _∈_; family)

variable
  ℓ : Level

PostSystemStr : Set ℓ → Set (suc (suc ℓ))
PostSystemStr X = X → SubP (SubP X)

PostSystem : (ℓ : Level) → Set (suc (suc ℓ))
PostSystem ℓ = Σ (Set ℓ) PostSystemStr

∣_∣ : PostSystem ℓ → Set ℓ
∣ X , _ ∣ = X

Cov : (PS : PostSystem ℓ) → PostSystemStr ∣ PS ∣
Cov (_ , c) = c

module _ (PS : PostSystem ℓ) where

  mutual

    data _◀_ : ∣ PS ∣ → SubP ∣ PS ∣ → Set (suc ℓ) where
      C₁ : (U   : SubP ∣ PS ∣) (u : ∣ PS ∣) → u ∈ U                 → u ◀ U
      C₂ : (U S : SubP ∣ PS ∣) (u : ∣ PS ∣) → S ∈ Cov PS u → S ◀ₛ U → u ◀ U

    _◀ₛ_ : SubP ∣ PS ∣ → SubP ∣ PS ∣ → Set (suc ℓ)
    _◀ₛ_ S U = (s : ∣ PS ∣) → s ∈ S → s ◀ U
