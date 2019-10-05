module PostSystem where

open import Common
open import Poset    renaming (∣_∣ to ∣_∣P)
open import Homotopy

variable
  ℓ ℓ′ : Level

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

ext : {X : Set ℓ} (_⊑_ : X → X → Set ℓ′)
     → 𝒫 X → 𝒫 X → Set (ℓ ⊔ ℓ′)
ext {X = X} _⊑_ S T = (t : X) → t ∈ T → Σ[ s ∈ X ] (s ∈ S × t ⊑ s)

CompletePosetStr : (ℓ ℓ′ : Level) → Set ℓ → Set (suc (suc ℓ) ⊔ suc ℓ′)
CompletePosetStr ℓ ℓ′ X = PosetStr ℓ ℓ′ X × PostSystemStr X
