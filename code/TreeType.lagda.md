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
  Σ[ B ∈ (A → Set ℓ) ] Σ[ C ∈ ({x : A} → B x → Set ℓ) ] ({x : A} → {y : B x} → C y → A)

Discipline : (ℓ : Level) → Set (suc ℓ)
Discipline ℓ = Σ[ A ∈ (Set ℓ) ] (IsADiscipline A)

stage : Discipline ℓ → Set ℓ
stage (A , _) = A

exp : (D : Discipline ℓ) → stage D → Set ℓ
exp (_ , B , _) = B

outcome : (D : Discipline ℓ) → {x : stage D} → exp D x → Set ℓ
outcome (_ , _ , C , _) = C

-- outcome and next together define an enumeration on the stages.

next : (D : Discipline ℓ) → {x : stage D} → {y : exp D x} → outcome D y → stage D
next (_ , _ , _ , d) = d
```

```
record Tree (D : Discipline ℓ) (s : stage D) : Set (suc ℓ) where
  constructor tree
  inductive

  field
    a : stage D
    b : exp D a
    c : (z : outcome D b) → Tree D (next D z)
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
  Branch : {a : stage D} (b : exp D a)
         → ((c : outcome D b) → Experiment⋆ D (next D c))
         → Experiment⋆ D a

outcome⋆ : (D : Discipline ℓ) → (s : stage D) → Experiment⋆ D s → Set ℓ
outcome⋆ {ℓ} D s (Leaf   s) = ⊤ {ℓ}
outcome⋆ D s (Branch b f) = Σ[ o ∈ (outcome D b) ] outcome⋆ D (next D o) (f o)

-- Arbitrary covering.

next⋆ : (D : Discipline ℓ) → (s : stage D) → (t : Experiment⋆ D s) → outcome⋆ D s t → stage D
next⋆ D s (Leaf   s)     _       = s
next⋆ D s (Branch b f) (c , y) = next⋆ D (next D c) (f c) y

branch : (D : Discipline ℓ) → (a : stage D)
       → (t : Experiment⋆ D a)
       → (g : (e : outcome⋆ D a t) → Experiment⋆ D (next⋆ D a t e))
       → Experiment⋆ D a
branch D a (Leaf   a)     g = g tt
branch D a (Branch b f) g =
  Branch b λ c → branch D (next D c) (f c) (λ - → g (c , -))
```

# Progressiveness

```
IsProgressive : (P : Poset ℓ₀ ℓ₁) → IsADiscipline ∣ P ∣ₚ → Set (ℓ₀ ⊔ ℓ₁)
IsProgressive {ℓ₀} P P-disc =
  (x : stage D) (y : exp D x) (z : outcome D y) → next D z ⊑[ P ] x holds
  where
    D : Discipline ℓ₀
    D = (∣ P ∣ₚ , P-disc)

IsProgressive⋆ : (P : Poset ℓ₀ ℓ₁) → IsADiscipline ∣ P ∣ₚ → Set (ℓ₀ ⊔ ℓ₁)
IsProgressive⋆ {ℓ₀} P P-disc =
  (a : stage D) (t : Experiment⋆ D a) (o : outcome⋆ D a t) → next⋆ D a t o ⊑[ P ] a holds
  where
    D : Discipline ℓ₀
    D = (∣ P ∣ₚ , P-disc)

prog⇒prog⋆ : (P : Poset ℓ₀ ℓ₁) → (disc : IsADiscipline ∣ P ∣ₚ) → IsProgressive P disc → IsProgressive⋆ P disc
prog⇒prog⋆ P disc prog a (Leaf   a)   o = ⊑-refl a
  where
    open PosetStr (proj₂ P) using (⊑-refl; _⊑⟨_⟩_; _■)
prog⇒prog⋆ P disc prog a (Branch b f) (o , os) = foo
  where
    open PosetStr (proj₂ P) using (⊑-refl; _⊑⟨_⟩_; _■)

    D = ∣ P ∣ₚ , disc

    IH : next⋆ D (next D o) (f o) os ⊑[ P ] next D o holds
    IH = prog⇒prog⋆ P disc prog (next (∣ P ∣ₚ , disc) o) (f o) os

    foo : next⋆ D a (Branch b f) (o , os) ⊑[ P ] a holds
    foo = next⋆ D a (Branch b f) (o , os) ⊑⟨ IH ⟩ next D o ⊑⟨ prog a b o ⟩ a ■

Discipline⁺ : (ℓ₀ ℓ₁ : Level) → Set (suc ℓ₀ ⊔ suc ℓ₁)
Discipline⁺ ℓ₀ ℓ₁ =
  Σ[ P ∈ (Poset ℓ₀ ℓ₁) ] Σ[ P-disc ∈ (IsADiscipline ∣ P ∣ₚ) ] IsProgressive P P-disc

stage⁺ : Discipline⁺ ℓ₀ ℓ₁ → Set ℓ₀
stage⁺ (P , _) = ∣ P ∣ₚ

exp⁺ : (D : Discipline⁺ ℓ₀ ℓ₁) → stage⁺ D → Set ℓ₀
exp⁺ (P , D , _) = exp (∣ P ∣ₚ , D)

outcome⁺ : (D : Discipline⁺ ℓ₀ ℓ₁) → {x : stage⁺ D} → exp⁺ D x → Set ℓ₀
outcome⁺ (P , D , _) = outcome (∣ P ∣ₚ , D)

next⁺ : (D : Discipline⁺ ℓ₀ ℓ₁)
      → {a : stage⁺ D} → {b : exp⁺ D a} → outcome⁺ D b → stage⁺ D
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
conclusions⋆ : (D : Discipline⁺ ℓ₀ ℓ₁) {s : stage⁺ D}
             → Experiment⋆ (raw D) s → Sub ℓ₀ (stage⁺ D)
conclusions⋆ D {s} e = outcome⋆ (raw D) s e , next⋆ (raw D) s e

refines : (D : Discipline⁺ ℓ₀ ℓ₁) {s s′ : stage⁺ D}
        → Experiment⋆ (raw D) s′ → Experiment⋆ (raw D) s → Set (ℓ₀ ⊔ ℓ₁)
refines D@(P , _) e f =
  (λ - → conclusions⋆ D e ↓[ P ] -) ⊆ (λ - → conclusions⋆ D f ↓[ P ] -)

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
    (e : Experiment⋆ (raw D) a₀) → Σ[ f ∈ (Experiment⋆ (raw D) a₁) ] (e ℛ[ D ] f)
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
    ∥ Σ[ t ∈ (Experiment⋆ (raw D) a) ] (λ - → (conclusions⋆ D t ) ↓[ pos D ] -) ⊆ U ∥

FormalTopology : (ℓ₀ ℓ₁ ℓ₂ : Level) → Set (suc ℓ₀ ⊔ suc ℓ₁ ⊔ ℓ₂)
FormalTopology ℓ₀ ℓ₁ ℓ₂ = Σ[ D ∈ (Discipline⁺ ℓ₀ ℓ₁) ] IsFormalTopology D ℓ₂

cover-of : (𝒯@(D , _) : FormalTopology ℓ₀ ℓ₁ ℓ₂)
         → stage⁺ D → (stage⁺ D → Ω (ℓ₀ ⊔ ℓ₁)) → Set (ℓ₀ ⊔ ℓ₁)
cover-of 𝒯@(_ , topo) = _◀_
  where
    open IsFormalTopology topo using (_◀_)

syntax cover-of 𝒯 a U = a ◀[ 𝒯 ] U
```

```
lemma₁ : (𝒯@(D , _) : FormalTopology ℓ₀ ℓ₁ ℓ₂) (U : stage⁺ D → Ω (ℓ₀ ⊔ ℓ₁))
       → (a₀ a₁ : stage⁺ D) → a₁ ⊑[ pos D ] a₀ holds → a₀ ◀[ 𝒯 ] U
       → a₁ ◀[ 𝒯 ] U
lemma₁ 𝒯@(D@((A , _) , (B , C , d) , prog) , topo) U a₀ a₁ a₀⊒a₁ a₀◀U = ∥∥-rec (∥∥-prop _) foo a₀◀U
  where
    open IsFormalTopology topo using (D-sim)

    sim : IsSimulation⋆ D
    sim = D-sim

    foo : Σ[ t ∈ (Experiment⋆ (raw D) a₀) ] ((λ - →  (conclusions⋆ D t) ↓[ pos D ] -) ⊆ U)
        → ∥ Σ[ t₁ ∈ (Experiment⋆ (raw D) a₁) ] (λ - → (conclusions⋆ D t₁) ↓[ pos D ] -) ⊆ U ∥
    foo (Leaf   a   , conc-D↓⊆U) = ∣ proj₁ (D-sim a₀ a₁ a₀⊒a₁ (Leaf a))     , l0 ∣
      where
        open PosetStr (proj₂ (pos D)) using (⊑-trans)

        l0 : (λ - → down (pos D) (conclusions⋆ D  (proj₁ (D-sim a₀ a₁ a₀⊒a₁ (Leaf a₀)))) -) ⊆ U
        l0 x x₁ = conc-D↓⊆U x ∣ tt , l1 ∣
          where
            l1 : x ⊑[ pos D ] (proj₂ (conclusions⋆ D (Leaf a₀)) tt) holds
            l1 = ∥∥-rec (proj₂ (x ⊑[ pos D ] (proj₂ (conclusions⋆ D (Leaf a₀)) tt)))  l2 x₁
              where
                l2 : Σ (index (conclusions⋆ D (proj₁ (D-sim a₀ a₁ a₀⊒a₁ (Leaf a₀)))))
                       (λ o → x ⊑[ pos D ] (proj₂ (conclusions⋆ D  (proj₁ (D-sim a₀ a₁ a₀⊒a₁ (Leaf a₀)))) o) holds)
                   → (x ⊑[ pos D ] (conclusions⋆ D (Leaf a₀) € tt)) holds
                l2 (i , q) = ⊑-trans x a₁ _ (⊑-trans x (next⋆ (raw D) a₁ (proj₁ (D-sim a₀ a₁ a₀⊒a₁ (Leaf a₀))) i) a₁ q {!!}) a₀⊒a₁
    foo (Branch b x , conc-D↓⊆U) = ∣ proj₁ (D-sim a₀ a₁ a₀⊒a₁ (Branch b x)) , {!!} ∣
```

```
-- --}
-- --}
-- --}
```
