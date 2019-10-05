{-# OPTIONS --without-K #-}

module Subset where

open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Common
open import Homotopy
open import Level

variable
  ℓ ℓ′ : Level

Pred : Set ℓ → Set (suc ℓ)
Pred {ℓ} X = Σ[ S ∈ (X → Set ℓ) ] ((s : X) → IsProp (S s))

SubsetP : (ℓ : Level) → Set (suc ℓ)
SubsetP ℓ = Σ[ X ∈ (Set ℓ) ] (Pred X)

container : SubsetP ℓ → Set ℓ
container (X , _) = X

predicate : (S : SubsetP ℓ) → container S → Set ℓ
predicate {ℓ} (_ , P , _) = P

injective : {X : Set ℓ} {Y : Set ℓ′} → (X → Y) → Set (ℓ ⊔ ℓ′)
injective {X = X} f = {x x′ : X} → f x ≡ f x′ → x ≡ x′

-- _⊆_ : {ℓ : Level} {S : Set ℓ} → SubP S → SubP S → Proposition ℓ
-- _⊆_ {S} U V = (s : S) → s ∈ U → s ∈ V

-- _∩_ : {ℓ : Level} {S : Set ℓ} → SubP S → SubP S → SubP S
-- U ∩ V = λ s → (s ∈ U) ×p (s ∈ V)

  -- ⋃[_]_ : {S X : Set} → (U : SubP S) → (F : X → SubP S)→ SubP S
-- ⋃[_]_ {_} {X} U F = λ a → Σ[ i ∈ X ] (a ∈ U) × (F i a)

IsMono : {A : Set ℓ} {B : Set ℓ′} → (A → B) → Set (suc ℓ ⊔ ℓ′)
IsMono {ℓ} {ℓ′} {A} {B} f = ((C : Set ℓ) → (g₁ g₂ : C → A) → f ∘ g₁ ≡ f ∘ g₂ → g₁ ≡ g₂)

-- The type of monomorphic functions.
Mono : Set ℓ → Set ℓ′ → Set (suc ℓ ⊔ ℓ′)
Mono {ℓ} {ℓ′} A B = Σ[ f ∈ (A → B) ] (IsMono f)

SubF : Set ℓ → Set (suc ℓ)
SubF {ℓ} A = Σ[ I ∈ Set ℓ ] (IsSet I × Mono I A)

index : {X : Set ℓ} → SubF X → Set ℓ
index (I , _) = I

family : {X : Set ℓ} → (S : SubF X) → index S → X
family (S , S-set , f , f-mono) = f

-- -}
-- -}
-- -}
