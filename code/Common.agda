module Common where

import Relation.Binary.PropositionalEquality as Eq

open Eq                  public using (_≡_; refl)
open import Data.Product public using (Σ; Σ-syntax; _,_; _×_; proj₁; proj₂)
open import Level        public

Σ!-syntax : {ℓ ℓ′ : Level} (A : Set ℓ) → (A → Set ℓ′) → Set (ℓ ⊔ ℓ′)
Σ!-syntax A p = Σ A (λ a → (p a) × ((b : A) → p b → a ≡ b))

syntax Σ!-syntax A (λ x → B) = Σ![ x ∈ A ] B
