{-# OPTIONS --without-K #-}

module SIP where

open import Common
open import Homotopy

private
  variable
    ℓ ℓ′ ℓ₀ ℓ₁ ℓ₂ : Level

∣_∣ : {S : Set ℓ → Set ℓ′} → Σ _ S → Set ℓ
∣ X , s ∣ = X

structure : {S : Set ℓ → Set ℓ′} → (A : Σ _ S) → S ∣ A ∣
structure (X , s) = s

canonical-map : {S : Set ℓ₀ → Set ℓ₁}
              → (ι : (A B : Σ _ S) → ∣ A ∣ ≃ ∣ B ∣ → Set ℓ₂)
              → (ρ : (A : Σ _ S) → ι A A (id-≃ ∣ A ∣))
              → {X : Set ℓ₀}
              → (s t : S X) → s ≡ t → ι (X , s) (X , t) (id-≃ X)
canonical-map ι ρ {X} s s refl = ρ (X , s)


SNS : (Set ℓ₀ → Set ℓ₁) → (ℓ₂ : Level) → Set ((suc ℓ₀) ⊔ ℓ₁ ⊔ (suc ℓ₂))
SNS {ℓ₀ = ℓ₀} {ℓ₁} S ℓ₂ =
  Σ ((A B : Σ _ S) → ∣ A ∣ ≃ ∣ B ∣ → Set ℓ₂) λ ι →
  Σ ((A   : Σ _ S) → ι A A (id-≃ ∣ A ∣))     λ ρ →
  {X : Set ℓ₀} (s t : S X) → isequiv (canonical-map ι ρ s t)

homomorphic : {S : Set ℓ₀ → Set ℓ₁} → SNS S ℓ₂
            → (A B : Σ _ S) → ∣ A ∣ ≃ ∣ B ∣ → Set ℓ₂
homomorphic (ι , _ , _) = ι

-- The type of equivalences of A and B with respect to the notion of homomorphism
-- specified by ι
_≃[_]_ : {S : Set ℓ₀ → Set ℓ₁} → Σ _ S → SNS S ℓ₂ → Σ _ S → Set (ℓ₀ ⊔ ℓ₂)
A ≃[ σ ] B = Σ (∣ A ∣ → ∣ B ∣) λ f → Σ (isequiv f) λ i → homomorphic σ A B (f , i)

id⇒homEq : {S : Set ℓ₀ → Set ℓ₁ } (σ : SNS S ℓ₂) → (A B : Σ _ S) → (A ≡ B) → (A ≃[ σ ] B)
id⇒homEq (_ , ρ , _) A A refl = id , proj₂ (id-≃ ∣ A ∣) , ρ A

postulate
  id⇒homEq-equiv : {S : Set ℓ₀ → Set ℓ₁}
                 → (σ : SNS S ℓ₂) → (A B : Σ _ S) → isequiv (id⇒homEq σ A B)

postulate
  homomorphism-lemma : {S : Set ℓ₀ → Set ℓ₁}
                    → (σ : SNS S ℓ₂) → (A B : Σ _ S) → (p : ∣ A ∣ ≡ ∣ B ∣)
                    → (transport S p (structure A) ≡ (structure B))
                      ≃ homomorphic σ A B (idtoeqv {A = ∣ A ∣} {∣ B ∣} p)
  -- homomorphism-lemma (ι , ρ , θ) (X , s) (X , t) refl = {!γ!}

postulate
  characterisation-of-≡ : {S : Set ℓ₀ → Set ℓ₁}
                        → (σ : SNS S ℓ₂)
                        → (A B : Σ _ S)
                        → (A ≡ B) ≃ (A ≃[ σ ] B)

postulate
  canonical-map-charac : {S : Set ℓ₀ → Set ℓ₁ }
                         (ι : (A B : Σ _ S) → ∣ A ∣ ≃ ∣ B ∣ → Set ℓ₂)
                         (ρ : (A : Σ _ S) → ι A A (id-≃ ∣ A ∣))
                         {X : Set ℓ₀}
                         (s t : S X)
                         (p : s ≡ t)
                       → canonical-map ι ρ s t p
                         ≡ transport (λ - → ι (X , s) (X , -) (id-≃ X)) p (ρ (X , s))

-- -}
-- -}
-- -}
