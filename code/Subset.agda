module Subset where

open import Data.Product using (Σ-syntax; _×_)
open import Level

Subset : {ℓ : Level} → Set ℓ → Set (suc ℓ)
Subset {ℓ} S = S → Set ℓ

_∈_ : {ℓ : Level} {S : Set ℓ} → S → Subset S → Set ℓ
x ∈ U = U x

_⊆_ : {S : Set} → Subset S → Subset S → Set
_⊆_ {S} U V = (s : S) → s ∈ U → s ∈ V

_∩_ : {S : Set} → Subset S → Subset S → Subset S
U ∩ V = λ s → (s ∈ U) × (s ∈ V)

⋃[_]_ : {S X : Set} → (U : Subset S) → (F : X → Subset S)→ Subset S
⋃[_]_ {_} {X} U F = λ a → Σ[ i ∈ X ] (a ∈ U) × (F i a)
