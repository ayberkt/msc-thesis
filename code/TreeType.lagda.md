<!--
```
{-# OPTIONS --without-K #-}

module TreeType where

open import Variables
open import Data.Empty  using (⊥; ⊥-elim)
open import Data.Unit   using (⊤; tt)
open import Data.Bool   using (Bool; true; false)
open import Data.List   using (List; _∷_; [])
open import Data.Nat    using (ℕ) renaming (zero to nzero; suc to nsuc)
open import Common
open import Poset
open import Family
open import Homotopy
```
-->

# Introduction

```
IsADiscipline : (A : Set ℓ) → Set (suc ℓ)
IsADiscipline {ℓ = ℓ} A =
  Σ[ B ∈ (A → Set ℓ) ]
  Σ[ C ∈ ((x : A) → B x → Set ℓ) ]
  Σ[ d ∈ ((x : A) → (y : B x) → C x y → A)] A

Discipline : (ℓ : Level) → Set (suc ℓ)
Discipline ℓ = Σ[ A ∈ (Set ℓ) ] (IsADiscipline A)

stage : Discipline ℓ → Set ℓ
stage (A , _) = A

exp : (D : Discipline ℓ) → stage D → Set ℓ
exp (_ , B , _) = B

outcome : (D : Discipline ℓ) → (x : stage D) → exp D x → Set ℓ
outcome (_ , _ , C , _) = C

next : (D : Discipline ℓ) → (x : stage D) → (y : exp D x) → outcome D x y → stage D
next (_ , _ , _ , d , _) = d

start : (D : Discipline ℓ) → stage D
start (_ , _ , _ , _ , s) = s
```

```
record Tree (D : Discipline ℓ) : Set (suc ℓ) where
  constructor tree
  inductive

  𝒯 = λ x → Tree (stage D , exp D , outcome D , next D , x)

  field
    a : stage D
    b : exp D a
    c : (z : outcome D a b) → 𝒯 (next D a b z)
```

# Elimination

```
{--
treerec : (A : Set ℓ)
          (B : A → Set ℓ)
          (C : (x : A) → B x → Set ℓ)
          (d : (x : A) → (y : B x) → C x y → A)
        → (D : (x : A) → Tree A B C d x → Set ℓ)
        → (a : A)
        → (t : Tree A B C d a)
        → (f : (x : A)
             → (y : B x)
             → (z : (v : C x y) → Tree A B C d (d x y v))
             → (u : (v : C x y) → D (d x y v) (z v))
             → D x (tree x y z))
        → D a t
treerec A B C d D a′ (tree a b c) f = {!!}
--}
```

# Stump

```
data Stump (D : Discipline ℓ) (a : stage D) : Set ℓ where
  leaf   : Stump D a
  branch : (b : exp D a) → ((c : outcome D a b) → Stump D (next D a b c)) → Stump D a
```

# Progressiveness

```
IsProgressive : (P : Poset ℓ₀ ℓ₁) → IsADiscipline ∣ P ∣ₚ → Set (ℓ₀ ⊔ ℓ₁)
IsProgressive P (B , C , d , s) =
  (x : ∣ P ∣ₚ) (y : B x) (z : C x y) → d x y z ⊑[ P ] x holds

Discipline⁺ : (ℓ₀ ℓ₁ : Level) → Set (suc ℓ₀ ⊔ suc ℓ₁)
Discipline⁺ ℓ₀ ℓ₁ =
  Σ[ P ∈ (Poset ℓ₀ ℓ₁) ] Σ[ P-disc ∈ (IsADiscipline ∣ P ∣ₚ) ] IsProgressive P P-disc

stage⁺ : Discipline⁺ ℓ₀ ℓ₁ → Set ℓ₀
stage⁺ (P , _) = ∣ P ∣ₚ

exp⁺ : (D : Discipline⁺ ℓ₀ ℓ₁) → stage⁺ D → Set ℓ₀
exp⁺ (P , D , _) = exp (∣ P ∣ₚ , D)

outcome⁺ : (D : Discipline⁺ ℓ₀ ℓ₁) → (x : stage⁺ D) → exp⁺ D x → Set ℓ₀
outcome⁺ (P , D , _) = outcome (∣ P ∣ₚ , D)
```
