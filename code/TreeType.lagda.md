<!--
```
{-# OPTIONS --without-K #-}

open import Truncation

module TreeType (pt : TruncationExists) where

open import Variables
open import Data.Empty  using (⊥; ⊥-elim)
open import Unit
open import Data.Bool   using (Bool; true; false)
open import Data.List   using (List; _∷_; [])
open import Data.Nat    using (ℕ) renaming (zero to nzero; suc to nsuc)
open import Common
open import Poset
open import Family
open import Homotopy    hiding (_⊆_)

open TruncationExists pt
```
-->

# Introduction

```
IsADiscipline : (A : Set ℓ) → Set (suc ℓ)
IsADiscipline {ℓ = ℓ} A =
  Σ[ B ∈ (A → Set ℓ) ] Σ[ C ∈ ((x : A) → B x → Set ℓ) ] ((x : A) → (y : B x) → C x y → A)

Discipline : (ℓ : Level) → Set (suc ℓ)
Discipline ℓ = Σ[ A ∈ (Set ℓ) ] (IsADiscipline A)

stage : Discipline ℓ → Set ℓ
stage (A , _) = A

exp : (D : Discipline ℓ) → stage D → Set ℓ
exp (_ , B , _) = B

outcome : (D : Discipline ℓ) → (x : stage D) → exp D x → Set ℓ
outcome (_ , _ , C , _) = C

-- outcome and next together define an enumeration on the stages.

next : (D : Discipline ℓ) → (x : stage D) → (y : exp D x) → outcome D x y → stage D
next (_ , _ , _ , d) = d
```

```
record Tree (D : Discipline ℓ) (s : stage D) : Set (suc ℓ) where
  constructor tree
  inductive

  field
    a : stage D
    b : exp D a
    c : (z : outcome D a b) → Tree D (next D a b z)
```

# Elimination

```
{--
treerec : (ds : Discipline ℓ)
        → (D : (x : stage ds) → Tree ds x → Set ℓ)
        → (t : Tree ds a)
        → (f : (x : stage ds)
             → (y : exp ds x)
             → (z : (v : outcome ds x y) → Tree ds (next ds x y v))
             → (u : (v : outcome ds x y) → D (next ds x y v) (z v))
             → D x (tree x y z))
        → D a t
treerec ds D (tree a b c) f = {!f a′ !}
--}
```

# Stump

```
data Experiment⋆ (D : Discipline ℓ) : stage D → Set ℓ where
  Leaf   : (a : stage D) → Experiment⋆ D a
  Branch : (a : stage D) (b : exp D a)
         → ((c : outcome D a b) → Experiment⋆ D (next D a b c))
         → Experiment⋆ D a

outcome⋆ : (D : Discipline ℓ) → (s : stage D) → Experiment⋆ D s → Set ℓ
outcome⋆ {ℓ} D s (Leaf   s) = ⊤ {ℓ}
outcome⋆ D s (Branch s b f) = Σ[ o ∈ (outcome D s b) ] outcome⋆ D (next D s b o) (f o)

-- Arbitrary covering.

next⋆ : (D : Discipline ℓ) → (s : stage D) → (t : Experiment⋆ D s) → outcome⋆ D s t → stage D
next⋆ D s (Leaf   s)     i       = s
next⋆ D s (Branch s b f) (c , y) = next⋆ D (next D s b c) (f c) y

branch : (D : Discipline ℓ) → (a : stage D)
       → (t : Experiment⋆ D a)
       → (g : (e : outcome⋆ D a t) → Experiment⋆ D (next⋆ D a t e))
       → Experiment⋆ D a
branch D a (Leaf   a)     g = g tt
branch D a (Branch a b f) g =
  Branch a b λ c → branch D (next D a b c) (f c) (λ - → g (c , -))
```

# Progressiveness

```
IsProgressive : (P : Poset ℓ₀ ℓ₁) → IsADiscipline ∣ P ∣ₚ → Set (ℓ₀ ⊔ ℓ₁)
IsProgressive P (B , C , d) =
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

next⁺ : (D : Discipline⁺ ℓ₀ ℓ₁)
      → (a : stage⁺ D) → (b : exp⁺ D a) → outcome⁺ D a b → stage⁺ D
next⁺ (P , D , _) = next (∣ P ∣ₚ , D)

pos : Discipline⁺ ℓ₀ ℓ₁ → Poset ℓ₀ ℓ₁
pos (P , _) = P

raw : (D : Discipline⁺ ℓ₀ ℓ₁) → Discipline ℓ₀
raw (P , P-disc , _) = ∣ P ∣ₚ , P-disc
```

# Simulation

`down P ℱ a` denotes the restriction of family `ℱ` of stages to those above the stage `a`.

```
down : (P : Poset ℓ₀ ℓ₁) → Sub ℓ ∣ P ∣ₚ → ∣ P ∣ₚ → Ω (ℓ₁ ⊔ ℓ)
down P ℱ@(I , F) a = ∥ (Σ[ i ∈ I ] a ⊑[ P ] F i holds) ∥ , ∥∥-prop _

syntax down P ℱ a = ℱ ↓[ P ] a
```

Ad-hoc notion of subset since there are some universe problems with `𝒫`. _This should be
replaced with `𝒫` once it is properly generalised._

```
_⊆_ : {X : Set ℓ} → (X → Ω ℓ′) → (X → Ω ℓ′) → Set (ℓ ⊔ ℓ′)
_⊆_ {X = X} U V = (x : X) → U x holds → V x holds
```

The refinement relation.

```
refines : (D : Discipline⁺ ℓ₀ ℓ₁) {s s′ : stage⁺ D}
        → Experiment⋆ (raw D) s′ → Experiment⋆ (raw D) s → Set (ℓ₀ ⊔ ℓ₁)
refines D@(P , _) {s} {s′} e d = (λ - → ℱ ↓[ P ] -) ⊆ (λ - → 𝒢 ↓[ P ] -)
  where
    ℱ = outcome⋆ (raw D) s  d , next⋆ (raw D) s d
    𝒢 = outcome⋆ (raw D) s′ e , next⋆ (raw D) s′ e

syntax refines D e d = e ℛ[ D ] d
```

The notion of simulation. It says: at any point, we can simulate what we could do before.

```
IsSimulation : (D : Discipline⁺ ℓ₀ ℓ₁) → Set (ℓ₀ ⊔ ℓ₁)
IsSimulation D@(P , _) =
  (a a′ : stage⁺ D) → a′ ⊑[ P ] a holds → (b : exp⁺ D a) →
    Σ[ b′ ∈ (exp⁺ D a′) ](λ - → (out a′ b′ , next⁺ D a′ b′) ↓[ P ] -) ⊆ (λ - → (out a b , next⁺ D a b) ↓[ P ] -)
  where
    out  = outcome⁺ D

-- We can localise any covering.
IsSimulation⋆ : (D : Discipline⁺ ℓ₀ ℓ₁) → Set (ℓ₀ ⊔ ℓ₁)
IsSimulation⋆ D@(P , _) =
  (a₀ a₁ : stage⁺ D) → a₁ ⊑[ P ] a₀ holds →
    (E : Experiment⋆ (raw D) a₀) → Σ[ E′ ∈ (Experiment⋆ (raw D) a₁) ] (E ℛ[ D ] E′)
```

# Formal Topology

A _formal topology_ is a **(1) progressive discipline** whose relation **(2) is a
simulation**, that is equipped with a **(3) cover relation**.

```
-- IsFormalTopology : Discipline⁺ ℓ₀ ℓ₁ → Set {!!}
-- IsFormalTopology D@(P , P-disc , _) = IsSimulation D × ∥ {!!} ∥
  -- where
    -- _◀_ : stage⁺ D → Sub ℓ′ (stage⁺ D) → Set {!!}
    -- a ◀ U = ∥ (Σ[ t ∈ (Experiment⋆ (stage⁺ D , P-disc) a) ] {!!}) ∥
```
