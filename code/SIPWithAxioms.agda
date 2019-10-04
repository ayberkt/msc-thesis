{-# OPTIONS --without-K #-}

module SIPWithAxioms where

open import Common
open import Homotopy
open import SIP

private
  variable
    ℓ ℓ′ ℓ₀ ℓ₁ ℓ₂ ℓ₃ : Level

∣_∣S : {S : Set ℓ₀ → Set ℓ₁} {axioms : (X : Set ℓ₀) → S X → Set ℓ₂}
    → (Σ (Set ℓ₀) λ X → Σ (S X) λ s → axioms X s) → Σ _ S
∣ X , s , ax ∣S = X , s

⟪_⟫ : {S : Set ℓ₀ → Set ℓ₁} {axioms : (X : Set ℓ₀) → S X → Set ℓ₂}
    → (Σ (Set ℓ₀) λ X → Σ (S X) λ s → axioms X s) → Set ℓ₀
⟪ X , _ , _ ⟫ = X

postulate
  add-axioms : {S : Set ℓ₀ → Set ℓ₁}
             → (axioms : (X : Set ℓ₀) → S X → Set ℓ₂)
             → ((X : Set ℓ₀) → (s : S X) → IsProp (axioms X s))
             → SNS S ℓ₃
             → SNS (λ X → Σ (S X) λ s → axioms X s) ℓ₃

postulate
  characterisation-of-≡-with-axioms : {S : Set ℓ₀ → Set ℓ₁}
                                    → (σ : SNS S ℓ₃)
                                    → (axioms : (X : Set ℓ₀) → S X → Set ℓ₂)
                                    → ((X : Set ℓ₀) → (s : S X) → IsProp (axioms X s))
                                    → (A B : Σ (Set ℓ₀) λ X → Σ (S X) λ s → axioms X s)
                                    → (A ≡ B) ≃ (∣ A ∣S ≃[ σ ] ∣ B ∣S)
