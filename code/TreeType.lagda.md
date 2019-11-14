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
IsAPostSystem : (A : Set ℓ) → Set (suc ℓ)
IsAPostSystem {ℓ = ℓ} A =
  Σ[ B ∈ (A → Set ℓ) ] Σ[ C ∈ ({x : A} → B x → Set ℓ) ]({x : A} → {y : B x} → C y → A)

PostSystem : (ℓ : Level) → Set (suc ℓ)
PostSystem ℓ = Σ (Set ℓ) IsAPostSystem

nonterminal : PostSystem ℓ → Set ℓ
nonterminal (A , _) = A

alternative : (D : PostSystem ℓ) → nonterminal D → Set ℓ
alternative (_ , B , _) = B

position : (D : PostSystem ℓ) → {x : nonterminal D} → alternative D x → Set ℓ
position (_ , _ , C , _) = C

proceed : (D : PostSystem ℓ)
        → {x : nonterminal D} → {y : alternative D x} → position D y → nonterminal D
proceed (_ , _ , _ , d) = d
```

```
record Tree (D : PostSystem ℓ) (s : nonterminal D) : Set (suc ℓ) where
  constructor tree
  inductive

  field
    a : nonterminal D
    b : alternative D a
    c : (z : position D b) → Tree D (proceed D z)
```

# Stump

```
data Experiment⋆ (D : PostSystem ℓ) : nonterminal D → Set ℓ where
  Leaf   : (a : nonterminal D) → Experiment⋆ D a
  Branch : {a : nonterminal D} (b : alternative D a)
         → ((c : position D b) → Experiment⋆ D (proceed D c))
         → Experiment⋆ D a

outcome⋆ : {D : PostSystem ℓ} {s : nonterminal D} → Experiment⋆ D s → Set ℓ
outcome⋆ {ℓ} (Leaf   a)   = ⊤ {ℓ}
outcome⋆ {_} {D = D} (Branch b f) = Σ[ o ∈ (position D b) ] outcome⋆ (f o)

-- Arbitrary covering.

next⋆ : {D : PostSystem ℓ} {s : nonterminal D} (t : Experiment⋆ D s) → outcome⋆ t → nonterminal D
next⋆ (Leaf   s)     _       = s
next⋆ {D = D} (Branch b f) (c , y) = next⋆ (f c) y

branch : (D : PostSystem ℓ) → (a : nonterminal D)
       → (t : Experiment⋆ D a)
       → (g : (e : outcome⋆ t) → Experiment⋆ D (next⋆ t e))
       → Experiment⋆ D a
branch D a (Leaf   a)     g = g tt
branch D a (Branch b f) g =
  Branch b λ c → branch D (proceed D c) (f c) (λ - → g (c , -))
```

# Progressiveness

```
IsProgressive : (P : Poset ℓ₀ ℓ₁) → IsAPostSystem ∣ P ∣ₚ → Set (ℓ₀ ⊔ ℓ₁)
IsProgressive {ℓ₀} P P-disc =
  (x : nonterminal D) (y : alternative D x) (z : position D y) → (proceed D z) ⊑[ P ] x holds
  where
    D : PostSystem ℓ₀
    D = (∣ P ∣ₚ , P-disc)

IsProgressive⋆ : (P : Poset ℓ₀ ℓ₁) → IsAPostSystem ∣ P ∣ₚ → Set (ℓ₀ ⊔ ℓ₁)
IsProgressive⋆ {ℓ₀} P P-disc =
  (a : nonterminal D) (t : Experiment⋆ D a) (o : outcome⋆ t) → next⋆ t o ⊑[ P ] a holds
  where
    D : PostSystem ℓ₀
    D = (∣ P ∣ₚ , P-disc)

Discipline⁺ : (ℓ₀ ℓ₁ : Level) → Set (suc ℓ₀ ⊔ suc ℓ₁)
Discipline⁺ ℓ₀ ℓ₁ =
  Σ[ P ∈ (Poset ℓ₀ ℓ₁) ] Σ[ P-disc ∈ (IsAPostSystem ∣ P ∣ₚ) ] IsProgressive P P-disc

stage⁺ : Discipline⁺ ℓ₀ ℓ₁ → Set ℓ₀
stage⁺ (P , _) = ∣ P ∣ₚ

exp⁺ : (D : Discipline⁺ ℓ₀ ℓ₁) → stage⁺ D → Set ℓ₀
exp⁺ (P , D , _) = alternative (∣ P ∣ₚ , D)

outcome⁺ : (D : Discipline⁺ ℓ₀ ℓ₁) → {x : stage⁺ D} → exp⁺ D x → Set ℓ₀
outcome⁺ (P , D , _) = position (∣ P ∣ₚ , D)

next⁺ : (D : Discipline⁺ ℓ₀ ℓ₁)
      → {a : stage⁺ D} → {b : exp⁺ D a} → outcome⁺ D b → stage⁺ D
next⁺ (P , D , _) = proceed (∣ P ∣ₚ , D)

pos : Discipline⁺ ℓ₀ ℓ₁ → Poset ℓ₀ ℓ₁
pos (P , _) = P

raw : (D : Discipline⁺ ℓ₀ ℓ₁) → PostSystem ℓ₀
raw (P , P-disc , _) = ∣ P ∣ₚ , P-disc

prog⇒prog⋆ : (D : Discipline⁺ ℓ₀ ℓ₁) → IsProgressive⋆ (pos D) (proj₁ (proj₂ D))
prog⇒prog⋆ D@(P , disc , IS) a (Leaf a)   o = ⊑-refl a
  where
    open PosetStr (proj₂ P) using (⊑-refl; _⊑⟨_⟩_; _■)
prog⇒prog⋆ D@(P , disc , IS) a (Branch b f) (o , os) = foo
  where
   open PosetStr (proj₂ P) using (⊑-refl; _⊑⟨_⟩_; _■)

   IH : next⋆ (f o) os ⊑[ P ] next⁺ D o holds
   IH = prog⇒prog⋆ D (proceed (∣ P ∣ₚ , disc) o) (f o) os

   foo : next⋆ (Branch b f) (o , os) ⊑[ P ] a holds
   foo = next⋆ (Branch b f) (o , os) ⊑⟨ IH ⟩ (proceed (raw D) o) ⊑⟨ IS a b o ⟩ a ■

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
conclusions⋆ : {D : PostSystem ℓ} {s : nonterminal D} → Experiment⋆ D s → Sub ℓ (nonterminal D)
conclusions⋆ {s = s} e = outcome⋆ e , next⋆ e

refines : (D : Discipline⁺ ℓ₀ ℓ₁) {s s′ : stage⁺ D}
        → Experiment⋆ (raw D) s′ → Experiment⋆ (raw D) s → Set (ℓ₀ ⊔ ℓ₁)
refines D@(P , _) e f =
  (λ - → conclusions⋆ e ↓[ P ] -) ⊆ (λ - → conclusions⋆ f ↓[ P ] -)

syntax refines D e f = e ℛ[ D ] f
```

The notion of simulation. It says: at any point, we can simulate what we could do before.

```
IsSimulation : (D : Discipline⁺ ℓ₀ ℓ₁) → Set (ℓ₀ ⊔ ℓ₁)
IsSimulation D@(P , _) =
  (a₀ a₁ : stage⁺ D) → a₁ ⊑[ P ] a₀ holds → (b₀ : exp⁺ D a₀) →
    Σ[ b₁ ∈ (exp⁺ D a₁) ]  (λ - → (outcome⁺ D b₁ , next⁺ D) ↓[ P ] -)
                         ⊆ (λ - → (outcome⁺ D b₀ , next⁺ D) ↓[ P ] -)

IsSimulation⋆ : (D : Discipline⁺ ℓ₀ ℓ₁) → Set (ℓ₀ ⊔ ℓ₁)
IsSimulation⋆ D@(P , _) =
  (a₀ a₁ : stage⁺ D) → a₁ ⊑[ P ] a₀ holds →
    (t₀ : Experiment⋆ (raw D) a₀) → Σ[ t₁ ∈ (Experiment⋆ (raw D) a₁) ] (t₁ ℛ[ D ] t₀)
```

Lemma

```
singleton : (D : Discipline⁺ ℓ₀ ℓ₁) {s : stage⁺ D} → exp⁺ D s → Experiment⋆ (raw D) s
singleton D e = Branch e (Leaf ∘ next⁺ D)

{--
sim⇒sim⋆ : (D : Discipline⁺ ℓ₀ ℓ₁) → IsSimulation D → IsSimulation⋆ D
sim⇒sim⋆ D@(P@(∣P∣ , P-str) , prog) D-sim a₀ a₁ a₁⊑a₀ (Leaf a₀) = (Leaf a₁) , ψ
  where
    open PosetStr P-str using (_⊑_; ⊑-refl; ⊑-trans)

    -- φ : (a : ∣P∣) → Σ ⊤ (λ _ → a ⊑ a₁ holds) → ∥ Σ ⊤ (λ _ → a ⊑ a₀ holds) ∥
    -- φ a (tt , a⊑a₁) = ∣ tt , ⊑-trans a a₁ a₀ a⊑a₁ a₁⊑a₀ ∣

    ψ : (x : ∣P∣)
      → down P (conclusions⋆ D (Leaf a₀)) x holds
      → down P (conclusions⋆ D (Leaf a₁)) x holds
    ψ a conc-a₀↓a = ∥∥-rec (∥∥-prop _) φ conc-a₀↓a
      where
        φ : Σ (proj₁ (conclusions⋆ D (Leaf a₀)))
              (λ i → (a ⊑ proj₂ (conclusions⋆ D (Leaf a₀)) i) holds)
          → ∥ Σ (proj₁ (conclusions⋆ D (Leaf a₁)))
              (λ i → (a ⊑ proj₂ (conclusions⋆ D (Leaf a₁)) i) holds) ∥
        φ (tt , snd) = {!!}

-- We can localise any covering.
sim⇒sim⋆ D@(P , _ , prog) D-sim a₀ a₁ a₀⊒a₁ (Branch b₀ f) =
  Branch b₁ {!!} , {!!}
  where
    open PosetStr (proj₂ P) using (_⊑_)

    𝒮 : Σ[ b₁ ∈ (exp⁺ D a₁) ]  (λ - → (outcome⁺ D b₁ , next⁺ D) ↓[ P ] -)
                             ⊆ (λ - → (outcome⁺ D b₀ , next⁺ D) ↓[ P ] -)
    𝒮 = D-sim a₀ a₁ a₀⊒a₁ b₀
    b₁ = proj₁ 𝒮
--}
```

# Formal Topology

A _formal topology_ is a **(1) progressive discipline** whose relation **(2) is a
simulation**, that is equipped with a **(3) cover relation**.

```
record IsFormalTopology (D : Discipline⁺ ℓ₀ ℓ₁) (ℓ₂ : Level) : Set (ℓ₀ ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    D-sim : IsSimulation⋆ D

  _◀_ : stage⁺ D → ((stage⁺ D) → Ω (ℓ₀ ⊔ ℓ₁)) → Set (ℓ₀ ⊔ ℓ₁)
  a ◀ U =
    ∥ Σ[ t ∈ (Experiment⋆ (raw D) a) ] (λ - → (conclusions⋆ t ) ↓[ pos D ] -) ⊆ U ∥

FormalTopology : (ℓ₀ ℓ₁ ℓ₂ : Level) → Set (suc ℓ₀ ⊔ suc ℓ₁ ⊔ ℓ₂)
FormalTopology ℓ₀ ℓ₁ ℓ₂ = Σ[ D ∈ (Discipline⁺ ℓ₀ ℓ₁) ] IsFormalTopology D ℓ₂

cover-of : (𝒯 : FormalTopology ℓ₀ ℓ₁ ℓ₂)
         → stage⁺ (proj₁ 𝒯) → (stage⁺ (proj₁ 𝒯) → Ω (ℓ₀ ⊔ ℓ₁)) → Set (ℓ₀ ⊔ ℓ₁)
cover-of 𝒯@(_ , topo) = _◀_
  where
    open IsFormalTopology topo using (_◀_)

syntax cover-of 𝒯 a U = a ◀[ 𝒯 ] U
```

```
lemma₁ : (𝒯 : FormalTopology ℓ₀ ℓ₁ ℓ₂) (U : stage⁺ (proj₁ 𝒯) → Ω (ℓ₀ ⊔ ℓ₁))
       → (a₀ a₁ : stage⁺ (proj₁ 𝒯)) → a₁ ⊑[ pos (proj₁ 𝒯) ] a₀ holds → a₀ ◀[ 𝒯 ] U
       → a₁ ◀[ 𝒯 ] U
lemma₁ 𝒯@(D , topo) U a₀ a₁ a₀⊒a₁ = ∥∥-rec (∥∥-prop _) (∣_∣ ∘ ψ)
  where
    open IsFormalTopology topo using (D-sim)

    ψ : Σ[ t₀ ∈ (Experiment⋆ (raw D) a₀) ]((λ - →  (conclusions⋆ t₀) ↓[ pos D ] -) ⊆ U)
      → Σ[ t₁ ∈ (Experiment⋆ (raw D) a₁) ] (λ - → (conclusions⋆ t₁) ↓[ pos D ] -) ⊆ U
    ψ (t , φ) = t₁ , conc-t₁↓⊆U
      where
        t₁ : Experiment⋆ (raw D) a₁
        t₁ = proj₁ (D-sim a₀ a₁ a₀⊒a₁ t)

        t₁-sim : refines D t₁ t
        t₁-sim = proj₂ (D-sim a₀ a₁ a₀⊒a₁ t)

        conc-t₁↓⊆U : (λ - → (conclusions⋆ t₁) ↓[ pos D ] -) ⊆ U
        conc-t₁↓⊆U a = φ a ∘ t₁-sim a
```

```
-- --}
-- --}
-- --}
```
