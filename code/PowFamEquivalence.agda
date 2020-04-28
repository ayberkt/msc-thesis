{-# OPTIONS --cubical --safe #-}

module PowFamEquivalence where

open import Basis
open import Powerset
open import Family
open import Data.Sum using (_⊎_; inj₁; inj₂)

idToEquiv : {A B : Type ℓ} → A ≡ B → A ≃ B
idToEquiv {A = A} {B = B} p = subst (λ A′ → A′ ≃ B) (sym p) (idEquiv B)

⟪_⟫ : {A : Type ℓ₀} → (A → hProp ℓ₁) → Sub (ℓ₀ ⊔ ℓ₁) A
⟪_⟫ {A = A} U = (Σ[ x ∈ A ] [ U x ]) , π₀

{--

lemma-4-8-1 : (A : Type ℓ₀) (B : A → hProp ℓ₁) (a : A) → fiber {A = Σ A (_is-true ∘ B)} π₀ a ≃ (B a is-true)
lemma-4-8-1 A B a =
  fiber π₀ a                              ≃⟨ idToEquiv refl ⟩
  Σ[ u ∈ (Σ A (_is-true ∘ B)) ] π₀ u ≡ a  ≃⟨ {!!} ⟩
  Σ[ x ∈ A ] Σ[ p ∈ (x ≡ a) ] B x is-true ≃⟨ ψ ⟩
  B a is-true                             ■
  where
    f : Σ[ x ∈ A ] Σ[ p ∈ (x ≡ a) ] B x is-true → B a is-true
    f (x , p , b) = subst (_is-true ∘ B) p b

    ψ : (Σ[ x ∈ A ] Σ[ p ∈ (x ≡ a) ] B x is-true) ≃ B a is-true
    ψ = f , record { equiv-proof = NTS }
      where
        NTS : (b : B a is-true) → isContr (fiber f b)
        NTS b = ((a , (refl , b)) , transportRefl b) , NTS′
          where
            NTS′ : (y : fiber f b) → ((a , (λ _ → a) , b) , transportRefl b) ≡ y
            NTS′ = {!!}

-- --}
-- --}
-- --}
