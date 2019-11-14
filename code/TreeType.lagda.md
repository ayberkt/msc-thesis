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
production  : (D : PostSystem ℓ) → nonterminal D → Set ℓ
location    : (D : PostSystem ℓ) → {x : nonterminal D} → production D x → Set ℓ
choose      : (D : PostSystem ℓ) {x : nonterminal D} {y : production D x}
            → location D y → nonterminal D

nonterminal (A , _ , _ , _) = A
production  (_ , B , _ , _) = B
location    (_ , _ , C , _) = C
choose      (_ , _ , _ , d) = d
```

Given a Post system `D`, which describes the structure of a tree, the type of inhabitants
of a specific tree satisfying `D` and starting with nonterminal `s` is given by the type
`Tree D s`.

```
record Tree (D : PostSystem ℓ) (s : nonterminal D) : Set (suc ℓ) where
  constructor tree
  inductive

  field
    a : nonterminal D
    b : production D a
    c : (z : location D b) → Tree D (choose D z)
```

# Stump

```
data Production⋆ (D : PostSystem ℓ) : nonterminal D → Set ℓ where
  Leaf   : (a : nonterminal D) → Production⋆ D a
  Branch : {a : nonterminal D} (b : production D a)
         → ((c : location D b) → Production⋆ D (choose D c))
         → Production⋆ D a
```

Given a `Production⋆`, say `t`, we denote by `location⋆ t` the type of _sequences of
locations_ in `t`. In other words, an inhabitant of `location⋆ t` is a _specific_ sequence
of choices in the tree `t`.

```
location⋆ : {D : PostSystem ℓ} {s : nonterminal D} → Production⋆ D s → Set ℓ
location⋆ {ℓ} (Leaf   a)   = ⊤ {ℓ}
location⋆ {_} {D = D} (Branch b f) = Σ[ o ∈ (location D b) ] location⋆ (f o)
```

Finally, we can take a sequence of choices in `t : Production⋆` and then follow all the
choices all the way to the end. This procedure is implemented in the function `choose⋆`.

```
choose⋆ : {D : PostSystem ℓ} {s : nonterminal D}
        → (t : Production⋆ D s) → location⋆ t → nonterminal D
choose⋆ (Leaf   s)   _       = s
choose⋆ (Branch b f) (c , y) = choose⋆ (f c) y
```

**TODO**: explain.

```
append : (D : PostSystem ℓ) → (a : nonterminal D)
       → (t : Production⋆ D a)
       → (g : (e : location⋆ t) → Production⋆ D (choose⋆ t e))
       → Production⋆ D a
append D a (Leaf   a)   g = g tt
append D a (Branch b f) g = Branch b λ c → append D (choose D c) (f c) (λ - → g (c , -))
```

# Perpetuation

Given a Post system, we will now order on the nonterminals representing whether one
contains more information than another. The idea is that if nonterminal `a₁` contains more
information than `a₀` then the knowledge state there is **more refined** than the one at
`a₁`; we thus write `a₁ ⊑ a₀`.

As we have already hinted, the point of this order is to view each nonterminal as a stage
of information. In light of this view, `choose` will be analogous to learning something
from an experiment which takes one from one stage to another (we will shortly introduce
new terminology).

In order for this to make sense, though, we must require that choosing nonterminals always
takes us to stages that are at least as refined than the current one. The intuitive
reading of this is: _experimentation never takes away existing knowledge_. Accordingly,
this property will be called **perpetuation**; we express it in the type family
`HasPerpetuation`.

```
HasPerpetuation : (P : Poset ℓ₀ ℓ₁) → IsAPostSystem ∣ P ∣ₚ → Set (ℓ₀ ⊔ ℓ₁)
HasPerpetuation {ℓ₀} P P-disc =
  (x : nonterminal D) (y : production D x) (z : location D y) →
    (choose D z) ⊑[ P ] x holds
  where
    D : PostSystem ℓ₀
    D = (∣ P ∣ₚ , P-disc)
```

We can define the analogous property for `choose⋆`:

```
HasPerpetuation⋆ : (P : Poset ℓ₀ ℓ₁) → IsAPostSystem ∣ P ∣ₚ → Set (ℓ₀ ⊔ ℓ₁)
HasPerpetuation⋆ {ℓ₀} P P-disc =
  (a : nonterminal D) (t : Production⋆ D a) (o : location⋆ t) → choose⋆ t o ⊑[ P ] a holds
  where
    D : PostSystem ℓ₀
    D = (∣ P ∣ₚ , P-disc)
```

We will refer to a Post system that has the perpetutation property as a
`Discipline`, it the sense that the stages of knowledge (i.e., the nonterminals)
resemble a _discipline of knowledge_. Accordingly, we introduce new terminology
for the projections.

```
Discipline : (ℓ₀ ℓ₁ : Level) → Set (suc ℓ₀ ⊔ suc ℓ₁)
Discipline ℓ₀ ℓ₁ =
  Σ[ P ∈ (Poset ℓ₀ ℓ₁) ] Σ[ P-disc ∈ (IsAPostSystem ∣ P ∣ₚ) ] HasPerpetuation P P-disc
```

It will be convenient to be easily refer to the poset and the post system
contained inside a discipline.

```
pos : Discipline ℓ₀ ℓ₁ → Poset ℓ₀ ℓ₁
pos (P , _) = P

post : (D : Discipline ℓ₀ ℓ₁) → PostSystem ℓ₀
post (P , P-disc , _) = ∣ P ∣ₚ , P-disc
```

Non-terminals are now called **stages**.

```
stage : Discipline ℓ₀ ℓ₁ → Set ℓ₀
stage D = nonterminal (post D)
```

Productions are now called **experiments**; `exp` for short.

```
exp : (D : Discipline ℓ₀ ℓ₁) → stage D → Set ℓ₀
exp D = production (post D)

experiment⋆ : (D : Discipline ℓ₀ ℓ₁) → stage D → Set ℓ₀
experiment⋆ D = Production⋆ (post D) 
```

Locations are now called **outcomes** in the sense that a location for a
reference to another non-terminal is like a possible outcome of the production.

```
outcome : (D : Discipline ℓ₀ ℓ₁) → {x : stage D} → exp D x → Set ℓ₀
outcome (P , D , _) = location (∣ P ∣ₚ , D)

outcome⋆ : {D : Discipline ℓ₀ ℓ₁} → {a : stage D} → Production⋆ (post D) a → Set ℓ₀
outcome⋆ = location⋆
```

The `choose` operation is now called `revise` in the sense that it is an
operation of _revising one's knowledge state_.

```
revise : (D : Discipline ℓ₀ ℓ₁)
      → {a : stage D} → {b : exp D a} → outcome D b → stage D
revise D = choose (post D)
```

In other words, we revise our knowledge state in light of an experiments outcome
which yields a new knowledge state.

```
prog⇒prog⋆ : (D : Discipline ℓ₀ ℓ₁) → HasPerpetuation⋆ (pos D) (proj₁ (proj₂ D))
prog⇒prog⋆ D@(P , disc , IS) a (Leaf a)   o = ⊑-refl a
  where
    open PosetStr (proj₂ P) using (⊑-refl; _⊑⟨_⟩_; _■)
prog⇒prog⋆ D@(P , disc , IS) a (Branch b f) (o , os) = foo
  where
   open PosetStr (proj₂ P) using (⊑-refl; _⊑⟨_⟩_; _■)

   IH : choose⋆ (f o) os ⊑[ P ] revise D o holds
   IH = prog⇒prog⋆ D (choose (∣ P ∣ₚ , disc) o) (f o) os

   foo : choose⋆ (Branch b f) (o , os) ⊑[ P ] a holds
   foo = choose⋆ (Branch b f) (o , os) ⊑⟨ IH ⟩ choose (post D) o ⊑⟨ IS a b o ⟩ a ■

```

# Simulation

The other property we are interested in, which will define a formal topology
when coupled with perpetuation, is **simulation**. Let us first introduce some
notation to build up towards its definition.

`down P ℱ a` denotes a predicate expressing: stage `a` has a more refined state
of information than at least one stage in `ℱ`.

```
down : (P : Poset ℓ₀ ℓ₁) → Sub ℓ₂ ∣ P ∣ₚ → ∣ P ∣ₚ → Ω (ℓ₁ ⊔ ℓ₂)
down P ℱ@(I , F) a = ∥ (Σ[ i ∈ I ] a ⊑[ P ] F i holds) ∥ , ∥∥-prop _

syntax down P ℱ a = ℱ ↓[ P ] a
```

We will often be dealing with the predicate `ℱ ↓[ P ] -`.

Ad-hoc notion of subset since there are some universe problems with `𝒫`. _This should be
replaced with `𝒫` once it is properly generalised._

```
_⊆_ : {X : Set ℓ} → (X → Ω ℓ′) → (X → Ω ℓ′) → Set (ℓ ⊔ ℓ′)
_⊆_ {X = X} U V = (x : X) → U x holds → V x holds
```

Given a `Production⋆` `t`, we can define a family of nonterminals it _reaches_
i.e., the leaves of the tree.

```
leaves : {D : PostSystem ℓ} {s : nonterminal D} → Production⋆ D s → Sub ℓ (nonterminal D)
leaves e = location⋆ e , choose⋆ e
```

We may hence define a notion of refinement: `t₀` refines `t₁` iff _any stage that is more
informative than a leaf of `t₀` is more informative than a leaf of `t₁`.

```
refines : (D : Discipline ℓ₀ ℓ₁) {s s′ : stage D}
        → experiment⋆ D s′ → experiment⋆ D s → Set (ℓ₀ ⊔ ℓ₁)
refines D@(P , _) e f = (λ - → leaves e ↓[ P ] -) ⊆ (λ - → leaves f ↓[ P ] -)

syntax refines D e f = e ℛ[ D ] f
```

Using the notion of refinement, we formulate the simulation property (given in
`IsSimulation⋆`) which says: given stages `a₁ ⊑ a₀`, for any `experiment⋆` on `a₀`, there
exists some `experiment⋆` `t₁` that is a refinement of `t₀`. In other words: as we move
towards more refined states of information, we maintain access to as refined sequences of
experiments.

```
IsSimulation⋆ : (D : Discipline ℓ₀ ℓ₁) → Set (ℓ₀ ⊔ ℓ₁)
IsSimulation⋆ D@(P , _) =
  (a₀ a₁ : stage D) → a₁ ⊑[ P ] a₀ holds →
    (t₀ : experiment⋆ D a₀) → Σ[ t₁ ∈ (experiment⋆ D a₁) ] (t₁ ℛ[ D ] t₀)
```

The analogous property for single experiments is given in `IsSimulation` which in fact
implies `IsSimulation⋆`.

```
IsSimulation : (D : Discipline ℓ₀ ℓ₁) → Set (ℓ₀ ⊔ ℓ₁)
IsSimulation D@(P , _) =
  (a₀ a₁ : stage D) → a₁ ⊑[ P ] a₀ holds → (b₀ : exp D a₀) →
    Σ[ b₁ ∈ (exp D a₁) ]   (λ - → (outcome D b₁ , revise D) ↓[ P ] -)
                         ⊆ (λ - → (outcome D b₀ , revise D) ↓[ P ] -)
```

**TODO**: simulation implies simulation⋆.

```
singleton : (D : Discipline ℓ₀ ℓ₁) {s : stage D} → exp D s → Production⋆ (post D) s
singleton D e = Branch e (Leaf ∘ revise D)

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

    𝒮 : Σ[ b₁ ∈ (exp D a₁) ]  (λ - → (outcome D b₁ , next⁺ D) ↓[ P ] -)
                             ⊆ (λ - → (outcome D b₀ , next⁺ D) ↓[ P ] -)
    𝒮 = D-sim a₀ a₁ a₀⊒a₁ b₀
    b₁ = proj₁ 𝒮
--}
```

# Formal Topology

A _formal topology_ is a **(1) progressive discipline** whose relation **(2) is a
simulation**, that is equipped with a **(3) cover relation**.

```
record IsFormalTopology (D : Discipline ℓ₀ ℓ₁) (ℓ₂ : Level) : Set (ℓ₀ ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    D-sim : IsSimulation⋆ D

  _◀_ : stage D → ((stage D) → Ω (ℓ₀ ⊔ ℓ₁)) → Set (ℓ₀ ⊔ ℓ₁)
  a ◀ U =
    ∥ Σ[ t ∈ (Production⋆ (post D) a) ] (λ - → (leaves t ) ↓[ pos D ] -) ⊆ U ∥

FormalTopology : (ℓ₀ ℓ₁ ℓ₂ : Level) → Set (suc ℓ₀ ⊔ suc ℓ₁ ⊔ ℓ₂)
FormalTopology ℓ₀ ℓ₁ ℓ₂ = Σ[ D ∈ (Discipline ℓ₀ ℓ₁) ] IsFormalTopology D ℓ₂

cover-of : (𝒯 : FormalTopology ℓ₀ ℓ₁ ℓ₂)
         → stage (proj₁ 𝒯) → (stage (proj₁ 𝒯) → Ω (ℓ₀ ⊔ ℓ₁)) → Set (ℓ₀ ⊔ ℓ₁)
cover-of 𝒯@(_ , topo) = _◀_
  where
    open IsFormalTopology topo using (_◀_)

syntax cover-of 𝒯 a U = a ◀[ 𝒯 ] U
```

```
lemma₁ : (𝒯 : FormalTopology ℓ₀ ℓ₁ ℓ₂) (U : stage (proj₁ 𝒯) → Ω (ℓ₀ ⊔ ℓ₁))
       → (a₀ a₁ : stage (proj₁ 𝒯)) → a₁ ⊑[ pos (proj₁ 𝒯) ] a₀ holds → a₀ ◀[ 𝒯 ] U
       → a₁ ◀[ 𝒯 ] U
lemma₁ 𝒯@(D , topo) U a₀ a₁ a₀⊒a₁ = ∥∥-rec (∥∥-prop _) (∣_∣ ∘ ψ)
  where
    open IsFormalTopology topo using (D-sim)

    ψ : Σ[ t₀ ∈ (Production⋆ (post D) a₀) ]((λ - →  (leaves t₀) ↓[ pos D ] -) ⊆ U)
      → Σ[ t₁ ∈ (Production⋆ (post D) a₁) ] (λ - → (leaves t₁) ↓[ pos D ] -) ⊆ U
    ψ (t , φ) = t₁ , conc-t₁↓⊆U
      where
        t₁ : Production⋆ (post D) a₁
        t₁ = proj₁ (D-sim a₀ a₁ a₀⊒a₁ t)

        t₁-sim : refines D t₁ t
        t₁-sim = proj₂ (D-sim a₀ a₁ a₀⊒a₁ t)

        conc-t₁↓⊆U : (λ - → leaves t₁ ↓[ pos D ] -) ⊆ U
        conc-t₁↓⊆U a = φ a ∘ t₁-sim a
```

```
-- --}
-- --}
-- --}
```
