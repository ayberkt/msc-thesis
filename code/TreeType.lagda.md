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

prog⇒prog⋆ : (D@(P , P-disc , IS) : Discipline⁺ ℓ₀ ℓ₁) → IsProgressive⋆ P P-disc
prog⇒prog⋆ D@(P , disc , IS) a (Leaf a)   o = ⊑-refl a
  where
    open PosetStr (proj₂ P) using (⊑-refl; _⊑⟨_⟩_; _■)
prog⇒prog⋆ D@(P , disc , IS) a (Branch b f) (o , os) = foo
  where
   open PosetStr (proj₂ P) using (⊑-refl; _⊑⟨_⟩_; _■)

   IH : next⋆ (raw D) (next⁺ D o) (f o) os ⊑[ P ] next⁺ D o holds
   IH = prog⇒prog⋆ D (next (∣ P ∣ₚ , disc) o) (f o) os

   foo : next⋆ (raw D) a (Branch b f) (o , os) ⊑[ P ] a holds
   foo = next⋆ (raw D) a (Branch b f) (o , os) ⊑⟨ IH ⟩ next (raw D) o ⊑⟨ IS a b o ⟩ a ■

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
sublemma₁ : (D : Discipline⁺ ℓ₀ ℓ₁) (IS : IsSimulation⋆ D) (a₀ a₁ : stage⁺ D) (U : stage⁺ D → Ω (ℓ₀ ⊔ ℓ₁))
          → a₁ ⊑[ pos D ] a₀ holds
          → (t : Experiment⋆ (raw D) a₀) → ((λ - →  (conclusions⋆ D t) ↓[ pos D ] -) ⊆ U)
          → Σ[ t₁ ∈ (Experiment⋆ (raw D) a₁) ] (λ - → (conclusions⋆ D t₁) ↓[ pos D ] -) ⊆ U
sublemma₁ D IS a₀ a₁ U a₁⊑a₀ (Leaf a₀)   φ = t₁ , bar
  where
    open PosetStr (proj₂ (pos D)) using (_⊑⟨_⟩_; _■)

    t₁ : Experiment⋆ (raw D) a₁
    t₁ = proj₁ (IS a₀ a₁ a₁⊑a₀ (Leaf a₀))

    bar : (λ - → (conclusions⋆ D t₁) ↓[ pos D ] -) ⊆ U
    bar a conc-t₁↓a = ∥∥-rec (proj₂ (U a)) baz conc-t₁↓a
      where
        baz : Σ (index (conclusions⋆ D t₁)) (λ i → a ⊑[ pos D ] (proj₂ (conclusions⋆ D t₁) i) holds) → U a holds
        baz (o , a⊑next-o) = φ a ∣ tt , a⊑a₀ ∣
          where
            a⊑a₀ : a ⊑[ pos D ] a₀ holds
            a⊑a₀ = a                               ⊑⟨ a⊑next-o             ⟩
                   next⋆ (raw D) a₁ t₁ o           ⊑⟨ prog⇒prog⋆ D a₁ t₁ o ⟩
                   a₁                              ⊑⟨ a₁⊑a₀                ⟩
                   a₀                              ■
sublemma₁ D IS a₀ a₁ U a₁⊑a₀ (Branch b₀ f) φ = t₁ , foo
  where
    t₁ : Experiment⋆ (raw D) a₁
    t₁ = proj₁ (IS a₀ a₁ a₁⊑a₀ (Branch b₀ f))

    t₁-sim : refines D t₁ (Branch b₀ f)
    t₁-sim = proj₂ (IS a₀ a₁ a₁⊑a₀ (Branch b₀ f))

    l0 : (x : stage⁺ D)
       → ∥ Σ (outcome⋆ (raw D) a₁ t₁) (λ i → (x ⊑[ pos D ] (next⋆ (raw D) a₁ t₁ i)) holds) ∥
       → ∥ Σ (Σ (outcome⁺ D b₀) (λ o → outcome⋆ (raw D) (next⁺ D o) (f o)))
           (λ i → proj₁ (x ⊑[ pos D ] (next⋆ (raw D) (proj₂ (proj₂ (proj₁ (proj₂ D))) (proj₁ i)) (f (proj₁ i)) (proj₂ i)))) ∥
    l0 = t₁-sim

    IH : (t : Experiment⋆ (raw D) a₀) → down (pos D) (conclusions⋆ D t) ⊆ U → Σ-syntax (Experiment⋆ (raw D) a₁)
           (λ t₁ → down (pos D) (conclusions⋆ D t₁) ⊆ U)
    IH = sublemma₁ D IS a₀ a₁ U a₁⊑a₀

    foo : (λ - → conclusions⋆ D t₁ ↓[ pos D ] -) ⊆ U
    foo a conc-t₁↓a = ∥∥-rec (proj₂ (U a)) baz conc-t₁↓a
      where
        baz : Σ (proj₁ (conclusions⋆ D t₁)) (λ i → a ⊑[ pos D ] (proj₂ (conclusions⋆ D t₁) i) holds) → U a holds
        baz (o , snd) = φ a ∣ ({!!} , {!!}) , {!!} ∣

```

```
lemma₁ : (𝒯@(D , _) : FormalTopology ℓ₀ ℓ₁ ℓ₂) (U : stage⁺ D → Ω (ℓ₀ ⊔ ℓ₁))
       → (a₀ a₁ : stage⁺ D) → a₁ ⊑[ pos D ] a₀ holds → a₀ ◀[ 𝒯 ] U
       → a₁ ◀[ 𝒯 ] U
lemma₁ 𝒯@(D@((A , _) , (B , C , d) , prog) , topo) U a₀ a₁ a₀⊒a₁ a₀◀U = ∥∥-rec (∥∥-prop _) quux a₀◀U
  where
    open IsFormalTopology topo using (D-sim)

    sim : IsSimulation⋆ D
    sim = D-sim

    quux : Σ[ t ∈ (Experiment⋆ (raw D) a₀) ] ((λ - →  (conclusions⋆ D t) ↓[ pos D ] -) ⊆ U)
         → ∥ Σ[ t₁ ∈ (Experiment⋆ (raw D) a₁) ] (λ - → (conclusions⋆ D t₁) ↓[ pos D ] -) ⊆ U ∥
    quux (fst , snd) = ∣ sublemma₁ D D-sim a₀ a₁ U a₀⊒a₁ fst snd ∣

    foo : Σ[ t ∈ (Experiment⋆ (raw D) a₀) ] ((λ - →  (conclusions⋆ D t) ↓[ pos D ] -) ⊆ U)
        → ∥ Σ[ t₁ ∈ (Experiment⋆ (raw D) a₁) ] (λ - → (conclusions⋆ D t₁) ↓[ pos D ] -) ⊆ U ∥
    foo (t@(Leaf   _) , conc-D↓⊆U) = ∣ proj₁ (D-sim a₀ a₁ a₀⊒a₁ t)     , l0 ∣
      where
        open PosetStr (proj₂ (pos D)) using (⊑-trans)

        t₁ : Experiment⋆ (raw D) a₁
        t₁ = proj₁ (D-sim a₀ a₁ a₀⊒a₁ t)

        l0 : (a₁′ : A)
           → ∥ Σ (outcome⋆ (raw D) a₁ t₁) (λ i → a₁′ ⊑[ pos D ] (next⋆ (raw D) a₁ t₁ i) holds) ∥
           → (U a₁′) holds
        l0 a₁′ a₁′⊑conc-t₁ = conc-D↓⊆U a₁′ ∣ tt , l1 ∣
          where
            l1 : a₁′ ⊑[ pos D ] (proj₂ (conclusions⋆ D (Leaf a₀)) tt) holds
            l1 = ∥∥-rec (proj₂ (a₁′ ⊑[ pos D ] (proj₂ (conclusions⋆ D (Leaf a₀)) tt))) l2 a₁′⊑conc-t₁
              where
                l2 : Σ (index (conclusions⋆ D t₁)) (λ o → a₁′ ⊑[ pos D ] (proj₂ (conclusions⋆ D  t₁) o) holds)
                   → (a₁′ ⊑[ pos D ] (conclusions⋆ D (Leaf a₀) € tt)) holds
                l2 (i , q) = ⊑-trans a₁′ a₁ _ (⊑-trans a₁′ (next⋆ (raw D) a₁ t₁ i) a₁ q l3) a₀⊒a₁
                  where
                    l3 : next⋆ (raw D) a₁ t₁ i ⊑[ pos D ] a₁ holds
                    l3 = prog⇒prog⋆ D a₁ t₁ i
    foo (t@(Branch b f) , conc-D↓⊆U) = ∣ proj₁ (D-sim a₀ a₁ a₀⊒a₁ (Branch b f)) , l0 ∣
      where
        t₁ : Experiment⋆ (raw D) a₁
        t₁ = proj₁ (D-sim a₀ a₁ a₀⊒a₁ t)

        l0 : (a₁′ : A)
           → ∥ Σ (outcome⋆ (raw D) a₁ t₁) (λ i → a₁′ ⊑[ pos D ] (next⋆ (raw D) a₁ t₁ i) holds) ∥
           → (U a₁′) holds
        l0 a₁′ a₁′⊑conc-t₁ = ∥∥-rec (proj₂ (U a₁′)) l1 a₁′⊑conc-t₁
          where
            l1 : Σ (outcome⋆ (raw D) a₁ t₁) (λ i → a₁′ ⊑[ pos D ] (next⋆ (raw D) a₁ t₁ i) holds)
               → U a₁′ holds
            l1 (o , a₁′⊑next-o) = conc-D↓⊆U a₁′ ∣ ({!a₀◀U!} , {!o!}) , {!!} ∣
              where
                IH′ : Σ (Experiment⋆ (raw D) a₁) (λ t → down (pos D) (conclusions⋆ D t) ⊆ U) → A
                IH′ (Leaf a , snd) = {!!}
                IH′ (Branch b x , snd) = {!!}

                IH : {!!}
                IH = ∥∥-rec {!∥∥-prop _!} IH′ (lemma₁ 𝒯 U a₀ a₁ a₀⊒a₁ a₀◀U)

```

```
-- --}
-- --}
-- --}
```
