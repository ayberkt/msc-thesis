{-# OPTIONS --without-K #-}

module Common where

import Relation.Binary.PropositionalEquality as Eq

open Eq                  public using    (_≡_; refl; cong; sym)
                                renaming (subst to transport; trans to _>>>_)
open Eq.≡-Reasoning      public
open import Data.Product public using (Σ; Σ-syntax; _,_; _×_; proj₁; proj₂)
open import Function     public using (_∘_; id)
open import Level        public

Σ!-syntax : {ℓ ℓ′ : Level} (A : Set ℓ) → (A → Set ℓ′) → Set (ℓ ⊔ ℓ′)
Σ!-syntax A p = Σ A (λ a → (p a) × ((b : A) → p b → a ≡ b))

syntax Σ!-syntax A (λ x → B) = Σ![ x ∈ A ] B

×-resp₀ : {ℓ ℓ′ : Level} {X : Set ℓ} {Y : Set ℓ′} {x₀ x₁ : X} {y₀ y₁ : Y}
        → (x₀ , y₀) ≡ (x₁ , y₁) → x₀ ≡ x₁
×-resp₀ refl = refl

Σ-resp₀ : {ℓ ℓ′ : Level} {X : Set ℓ} {Y : X → Set ℓ′} (x : X) {x₀ x₁ : X}
        → (y₀ : Y x₀) → (y₁ : Y x₁) → (x₀ , y₀) ≡ (x₁ , y₁) → x₀ ≡ x₁
Σ-resp₀ x y₀ y₁ refl = refl
