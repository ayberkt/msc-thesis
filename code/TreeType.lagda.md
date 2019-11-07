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
open import Family     hiding (_⊆_)
open import Homotopy

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
  leaf   : (a : stage D) → Experiment⋆ D a
  branch : (a : stage D) (b : exp D a)
         → ((c : outcome D a b) → Experiment⋆ D (next D a b c))
         → Experiment⋆ D a

ind : (D : Discipline ℓ) → (s : stage D) → Experiment⋆ D s → Set ℓ
ind {ℓ} D s (leaf   s) = ⊤ {ℓ}
ind D s (branch s b f) = Σ[ o ∈ (outcome D s b) ] ind D (next D s b o) (f o)

enum : (D : Discipline ℓ) → (s : stage D) → (t : Experiment⋆ D s) → ind D s t → stage D
enum D s (leaf   s)     i       = s
enum D s (branch s b f) (c , y) = enum D (next D s b c) (f c) y
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
```

# Bisimulation

```
less : (P : Poset ℓ ℓ′) → (∣ P ∣ₚ → Set ℓ₀) → (∣ P ∣ₚ → Set ℓ₁) → Set (ℓ ⊔ ℓ′ ⊔ ℓ₀ ⊔ ℓ₁)
less P T S = (t : ∣ P ∣ₚ) → T t → Σ[ s ∈ ∣ P ∣ₚ ](S s × t ⊑[ P ] s holds)

syntax less P T S = T <<<[ P ] S

_⇓_ : {P : Poset ℓ₀ ℓ₁} → Sub ℓ ∣ P ∣ₚ → ∣ P ∣ₚ → Ω (ℓ₁ ⊔ ℓ)
_⇓_ {P = P} ℱ@(I , F) a = ∥ (Σ[ i ∈ I ] a ⊑[ P ] F i holds) ∥ , ∥∥-prop _

Bisim : (D : Discipline⁺ ℓ₀ ℓ₁) → Set (ℓ₀ ⊔ ℓ₁)
Bisim D@(P , _) =
  (a a′ : stage⁺ D) → a ⊑[ P ] a′ holds → (b : exp⁺ D a) → (b′ : exp⁺ D a′) →
    (x : stage⁺ D) → ((_⇓_ {P = P} ((outcome⁺ D a′ b′) , next⁺ D a′ b′)) x) holds → ((_⇓_ {P = P} ((outcome⁺ D a b) , (next⁺ D a b))) x) holds
```
