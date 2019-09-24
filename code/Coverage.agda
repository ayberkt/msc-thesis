module Coverage where

open import Level
open import Data.Product           using (Σ; Σ-syntax; _,_)
open import Semilattice
open import Poset

Sub : {ℓ : Level} → Set ℓ → Set (suc ℓ)
Sub {ℓ} A = Σ[ I ∈ Set ℓ ] (I → A)

CoverRelation : Set → Set₁
CoverRelation A =
  {S : AlgMeetSemilatticeStr A} → (a : A) → (Sub (↓ (A , poset-of S) a)) → Set
