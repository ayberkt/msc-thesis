```
{-# OPTIONS --cubical #-}

module HITCoverage where

open import Level
open import Agda.Primitive.Cubical
open import Agda.Builtin.Cubical.Path
open import Data.Empty   using (⊥) renaming (⊥-elim to explode)
open import Data.Product using (Σ; _,_) renaming (proj₁ to π₀; proj₂ to π₁)

Type₀  = Set zero

Type : (ℓ : Level) → Set (suc ℓ)
Type ℓ = Set ℓ
```

```
variable
  ℓ ℓ′ ℓ₀ ℓ₁ ℓ₂ : Level
  A B           : Type ℓ

IsProposition : Type ℓ → Type ℓ
IsProposition A = (a b : A) → a ≡ b
```

```
record IsPreOrder (P : Type ℓ) : Type (suc ℓ) where
  field
    _⊑_   : P → P → Type ℓ

    -- Laws
    refl  : (a        : P) → a ⊑ a
    trans : (a₀ a₁ a₂ : P) → a₀ ⊑ a₁ → a₁ ⊑ a₂ → a₀ ⊑ a₂

-- Pre-ordered set.
Proset : (ℓ : Level) → Type (suc ℓ)
Proset ℓ = Σ (Type ℓ) IsPreOrder

∣_∣ : Proset ℓ → Type ℓ
∣ P , _ ∣ = P

variable
  PR : Proset ℓ

rel-of : ∣ PR ∣ → ∣ PR ∣ → Type _
rel-of {PR = PR} a₀ a₁ = a₀ ⊑ a₁
  where
    open IsPreOrder (π₁ PR) using (_⊑_)

syntax rel-of {PR = PR} a₀ a₁ = a₀ ⊑[ PR ] a₁

module Test (PR : Proset ℓ)
            (exp  : ∣ PR ∣ → Type ℓ′)
            (out  : (a : ∣ PR ∣) → exp a → Type ℓ′)
            (rev  : (a : ∣ PR ∣) → (b : exp a) → out a b → ∣ PR ∣)
            (mono : (a : ∣ PR ∣) → (b : exp a) → (c : out a b) → rev a b c ⊑[ PR ] a)
            (sim  : (a₀ a : ∣ PR ∣)
                  → a₀ ⊑[ PR ] a
                  → (b : exp a)
                  → Σ (exp a₀) (λ b₀ → (c₀ : out a₀ b₀) → Σ (out a b) (λ c → (rev a₀ b₀ c₀) ⊑[ PR ] (rev a b c))))
            where

  P = ∣ PR ∣

  IsDownwardClosed : (∣ PR ∣ → Type ℓ′) → Type (ℓ ⊔ ℓ′)
  IsDownwardClosed U = (a₀ a : P) → U a → a₀ ⊑[ PR ] a → U a₀

  data _<|_ (a : P) (U : P → Type ℓ′) : Type (ℓ ⊔ suc ℓ′) where
    dir    : U a → a <| U
    branch : (b : exp a) → (f : (c : out a b) → rev a b c <| U) → a <| U
    squash : (p₀ p₁ : a <| U) → p₀ ≡ p₁

```
