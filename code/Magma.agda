module Magma where

open import Homotopy
open import Common
open import IsomorphismReasoning

variable
  ℓ ℓ′ ℓ′′ : Level

Magma : (Set ℓ → Set ℓ′) → Set (suc ℓ ⊔ ℓ′)
Magma {ℓ} {ℓ′} S = Σ (Set ℓ) S

∣_∣ : {S : Set ℓ → Set ℓ′} → Σ (Set ℓ) S → Set ℓ
∣ X , s ∣ = X

structure : {S : Set ℓ → Set ℓ′} → (A : Σ (Set ℓ) S) → S ∣ A ∣
structure (X , s) = s

Σ′ : {X : Set ℓ} (Y : X → Set ℓ′) → Set (ℓ ⊔ ℓ′)
Σ′ {X = X} Y = Σ X Y

canonical-map : {S : Set ℓ → Set ℓ′}
              → (ι : (A B : Σ′ S) → ∣ A ∣ ≃ ∣ B ∣ → Set ℓ′′)
              → (ρ : (A : Σ′ S) → ι A A (id-≃ ∣ A ∣))
              → {X : Set ℓ}
              → (s t : S X)
              → s ≡ t → ι (X , s) (X , t) (id-≃ X)
canonical-map ι ρ {X} s _ refl = ρ (X , s)

SNS : (Set ℓ → Set ℓ′) → (ℓ′′ : Level) → Set (suc ℓ ⊔ ℓ′ ⊔ suc ℓ′′)
SNS {ℓ} {ℓ′} S ℓ′′ =
  Σ′ λ (ι : (A B : Σ′ S) → ∣ A ∣ ≃ ∣ B ∣ → Set ℓ′′) →
  Σ′ λ (ρ : (A   : Σ′ S) → ι A A (id-≃ ∣ A ∣)) →
  {X : Set ℓ} (s t : S X) → isequiv (canonical-map {S = S} ι ρ s t)

homomorphic : {S : Set ℓ → Set ℓ′} → SNS S ℓ′′ → (A B : Σ′ S)
            → ∣ A ∣ ≃ ∣ B ∣ → Set ℓ′′
homomorphic (ι , _ , _) = ι

_≃[_]_ : {S : Set ℓ → Set ℓ′} → Σ′ S → SNS S ℓ′′ → Σ′ S → Set (ℓ ⊔ ℓ′′)
A ≃[ σ ] B = Σ′ λ (f : ∣ A ∣ → ∣ B ∣) → Σ′ λ (i : isequiv f) → homomorphic σ A B (f , i)

idtoiso : {S : Set ℓ → Set ℓ′′} (σ : SNS S ℓ′′)
        → (A B : Σ′ S) → (A ≡ B) → A ≃[ σ ] B
idtoiso (_ , ρ , _) A A refl = id , ((id , λ _ → refl) , id , (λ _ → refl)) , ρ A

homomorphism-lemma : {S : Set ℓ → Set ℓ′} (σ : SNS S ℓ′)
                     (A B : Σ′ S) (p : ∣ A ∣ ≡ ∣ B ∣)
                   → (transport S p (structure A) ≡ (structure B))
                     ≃ homomorphic σ A B (idtoeqv {A = ∣ A ∣} {B = ∣ B ∣} p)
homomorphism-lemma (ι , ρ , θ) (X , s) (X , t) refl = γ
  where
    γ : (s ≡ t) ≃ ι (X , s) (X , t) (id-≃ X)
    γ = canonical-map ι ρ s t , θ s t
