<!--
```
{-# OPTIONS --without-K #-}

open import Truncation

module TreeType (pt : TruncationExists) where

open import Variables
open import Data.Empty  using (⊥; ⊥-elim)
open import Unit
open import Data.Bool   using (Bool; true; false; _∨_)
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

Given a Post system `D` and a start stage `s`, we denote by `Production⋆ D s` the type
of experimentation sequences that start from `s`.

```
data Production⋆ (D : PostSystem ℓ) : nonterminal D → Set ℓ where
  Leaf   : (a : nonterminal D) → Production⋆ D a
  Branch : {a : nonterminal D} (b : production D a)
         → ((c : location D b) → Production⋆ D (choose D c))
         → Production⋆ D a
```

Given a `Production⋆`, say `t`, we denote by `location⋆ t` the type of _sequences of
locations_ in `t`. In other words, an inhabitant of `location⋆ t` is a _specific_ sequence
of choices of experiments in the tree `t`.

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

Given a Post system, we will now require an order on the nonterminals representing whether
one contains more information than another. The idea is that if nonterminal `a₁` contains
more information than `a₀` then the knowledge state there is **more refined** than the one
at `a₁`; we thus write `a₁ ⊑ a₀`.

As we have already hinted, the point of this order is to view each nonterminal as a stage
of information. In light of this view, `choose` will be analogous to learning something
from an experiment which takes one from one stage to another (we will shortly introduce
new terminology).

In order for this to make sense, though, we must require that choosing nonterminals always
takes us to stages that are at least as refined as the current one. The intuitive reading
of this is: _experimentation never takes away existing knowledge_. Accordingly, this
property will be called **perpetuation**; we express it in the type family
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

outcome⋆ : {D : Discipline ℓ₀ ℓ₁} → {a : stage D} → experiment⋆ D a → Set ℓ₀
outcome⋆ = location⋆
```

The `choose` operation is now called `revise` in the sense that it is an
operation of _revising one's knowledge state_.

```
revise : (D : Discipline ℓ₀ ℓ₁)
      → {a : stage D} → {b : exp D a} → outcome D b → stage D
revise D = choose (post D)
```

In other words, we revise our knowledge state in light of an experiment's outcome
which yields a new knowledge state.

```
prog⇒prog⋆ : (D : Discipline ℓ₀ ℓ₁) → HasPerpetuation⋆ (pos D) (proj₂ (post D))
prog⇒prog⋆ D@(P , disc , IS) a (Leaf a)   o = ⊑-refl a
  where
    open PosetStr (proj₂ P) using (⊑-refl; _⊑⟨_⟩_; _■)
prog⇒prog⋆ D@(P , disc , IS) a (Branch b f) (o , os) = φ
  where
   open PosetStr (proj₂ P) using (⊑-refl; _⊑⟨_⟩_; _■)

   IH : choose⋆ (f o) os ⊑[ P ] revise D o holds
   IH = prog⇒prog⋆ D (choose (∣ P ∣ₚ , disc) o) (f o) os

   φ : choose⋆ (Branch b f) (o , os) ⊑[ P ] a holds
   φ = choose⋆ (Branch b f) (o , os) ⊑⟨ IH ⟩ choose (post D) o ⊑⟨ IS a b o ⟩ a ■

```

# Simulation

The other property we are interested in, which will define a formal topology
when coupled with perpetuation, is **simulation**. Let us first introduce some
notation to build up towards its definition.

`down P ℱ a` denotes a predicate expressing: stage `a` has a more refined state
of information than at least one stage in `ℱ`.

```
down : (P : Poset ℓ₀ ℓ₁) → Sub ℓ₂ ∣ P ∣ₚ → ∣ P ∣ₚ → Set (ℓ₁ ⊔ ℓ₂)
down P ℱ@(I , F) a = Σ[ i ∈ I ] a ⊑[ P ] F i holds

syntax down P ℱ a = a ≤[ P ] ℱ
```

We will often be dealing with the predicate `ℱ ↓[ P ] -`.

Ad-hoc notion of subset since there are some universe problems with `𝒫`. _This should be
replaced with `𝒫` once it is properly generalised._

```
_⊆_ : {X : Set ℓ} → (X → Set ℓ′) → (X → Set ℓ′) → Set (ℓ ⊔ ℓ′)
_⊆_ {X = X} U V = (x : X) → U x → V x
```

Given a `Production⋆` `t`, we can define a family of nonterminals it _reaches_ i.e., the
leaves of the tree.

```
leaves : {D : PostSystem ℓ} {s : nonterminal D} → Production⋆ D s → Sub ℓ (nonterminal D)
leaves e = location⋆ e , choose⋆ e
```

We may hence define a notion of refinement: `t₀` refines `t₁` iff _any stage that is more
informative than a leaf of `t₀` is more informative than a leaf of `t₁`.

```
refines : (D : Discipline ℓ₀ ℓ₁) {s s′ : stage D}
        → experiment⋆ D s′ → experiment⋆ D s → Set (ℓ₀ ⊔ ℓ₁)
refines D@(P , _) e f = (λ - → - ≤[ P ] leaves e) ⊆ (λ - → - ≤[ P ] leaves f)

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
    Σ[ b₁ ∈ (exp D a₁) ]   (λ - →  - ≤[ P ] (outcome D b₁ , revise D))
                         ⊆ (λ - →  - ≤[ P ] (outcome D b₀ , revise D))
```

```
singleton : (D : Discipline ℓ₀ ℓ₁) {s : stage D} → exp D s → experiment⋆ D s
singleton D e = Branch e (Leaf ∘ revise D)

sim⇒sim⋆ : (D : Discipline ℓ₀ ℓ₁) → IsSimulation D → IsSimulation⋆ D
sim⇒sim⋆ D@(PS , prog) _ a₀ a₁ a₁⊑a₀ (Leaf a₀) = (Leaf a₁) , ψ
  where
    open PosetStr (proj₂ PS) using (_⊑_; ⊑-refl; _⊑⟨_⟩_; _■)

    ψ : (x : stage D)
      → down (pos D) (leaves {D = post D} (Leaf a₁)) x
      → down (pos D) (leaves {D = post D} (Leaf a₀)) x
    ψ a (tt , a⊑a₁) = tt , (a ⊑⟨ a⊑a₁ ⟩ a₁ ⊑⟨ a₁⊑a₀ ⟩ a₀ ■)

sim⇒sim⋆ D@(P , _ , prog) D-sim a₀ a₁ a₀⊒a₁ t₀@(Branch b₀ f) =
  t₁ , t₁-refines-t₀
  where
    open PosetStr (proj₂ P) using (_⊑_; ⊑-refl)

    b₁ : exp D a₁
    b₁ = proj₁ (D-sim a₀ a₁ a₀⊒a₁ b₀)

    φ : (a : stage D)
      → a ≤[ P ] (outcome D b₁ , revise D) → a ≤[ P ] (outcome D b₀ , revise D)
    φ = proj₂ (D-sim a₀ a₁ a₀⊒a₁ b₀)

    g : (o₁ : outcome D b₁) → experiment⋆ D (revise D o₁)
    g o₁ = proj₁ IH
      where
        rev-o₀≤sat-b₀ : revise D o₁ ≤[ P ] (outcome D b₀ , revise D)
        rev-o₀≤sat-b₀ = φ (revise D o₁) (o₁ , (⊑-refl _))

        o₀ : outcome D b₀
        o₀ = proj₁ rev-o₀≤sat-b₀

        foo : revise D o₁ ⊑ revise D o₀ holds
        foo = proj₂ rev-o₀≤sat-b₀

        IH : Σ[ t′ ∈ experiment⋆ D (revise D o₁) ] refines D t′ (f o₀)
        IH = sim⇒sim⋆ D D-sim (revise D o₀) (revise D o₁) foo (f o₀)

    t₁ = Branch b₁ g

    t₁-refines-t₀ : (a : stage D) → a ≤[ P ] leaves t₁ → down P (leaves t₀) a
    t₁-refines-t₀ a ((o , os′) , a≤leaves-t₁-os) = (o₀ , os₀) , a⊑leaf-t₀-at-o₀-os₀
      where
        rev-o₀≤sat-b₀ : revise D o ≤[ P ] (outcome D b₀ , revise D)
        rev-o₀≤sat-b₀ = φ (revise D o) (o , ⊑-refl _)

        o₀ : outcome D b₀
        o₀ = proj₁ rev-o₀≤sat-b₀

        IH : Σ[ t′ ∈ experiment⋆ D (revise D o) ] refines D t′ (f o₀)
        IH = sim⇒sim⋆ D D-sim (revise D o₀) _ (proj₂ (φ _ (o , ⊑-refl _))) (f o₀)

        os₀ : location⋆ (f o₀)
        os₀ = proj₁ (proj₂ IH a (os′ , a≤leaves-t₁-os))

        a⊑leaf-t₀-at-o₀-os₀ : a ⊑ (leaves t₀ € (o₀ , os₀)) holds
        a⊑leaf-t₀-at-o₀-os₀ = proj₂ ((proj₂ IH) a (os′ , a≤leaves-t₁-os))
```

# Formal Topology

A _formal topology_ is a discipline with the simulation property.

```
FormalTopology : (ℓ₀ ℓ₁ : Level) → Set (suc ℓ₀ ⊔ suc ℓ₁)
FormalTopology ℓ₀ ℓ₁ = Σ[ D ∈ (Discipline ℓ₀ ℓ₁) ] (IsSimulation⋆ D)

cover-of : (𝒯 : FormalTopology ℓ₀ ℓ₁)
         → stage (proj₁ 𝒯) → (stage (proj₁ 𝒯) → Ω (ℓ₀ ⊔ ℓ₁)) → Set (ℓ₀ ⊔ ℓ₁)
cover-of 𝒯@(D , topo) a U =
  ∥ Σ[ t ∈ (experiment⋆ D a) ] (λ - → - ≤[ pos D ] leaves t) ⊆ (_holds ∘ U) ∥

syntax cover-of 𝒯 a U = a ◀[ 𝒯 ] U
```

```
lemma₁ : (𝒯 : FormalTopology ℓ₀ ℓ₁) (U : stage (proj₁ 𝒯) → Ω (ℓ₀ ⊔ ℓ₁))
       → (a₀ a₁ : stage (proj₁ 𝒯)) → a₁ ⊑[ pos (proj₁ 𝒯) ] a₀ holds → a₀ ◀[ 𝒯 ] U
       → a₁ ◀[ 𝒯 ] U
lemma₁ 𝒯@(D , D-sim) U a₀ a₁ a₀⊒a₁ a₀◀U = ∥∥-rec (∥∥-prop _) (∣_∣ ∘ ψ) a₀◀U
  where
    ψ : Σ[ t₀ ∈ experiment⋆ D a₀ ] (λ - → - ≤[ pos D ] leaves t₀) ⊆ (_holds ∘ U)
      → Σ[ t₁ ∈ experiment⋆ D a₁ ] (λ - → - ≤[ pos D ] leaves t₁) ⊆ (_holds ∘ U)
    ψ (t , φ) = t₁ , conc-t₁↓⊆U
      where
        t₁ : experiment⋆ D a₁
        t₁ = proj₁ (D-sim a₀ a₁ a₀⊒a₁ t)

        t₁-sim : refines D t₁ t
        t₁-sim = proj₂ (D-sim a₀ a₁ a₀⊒a₁ t)

        conc-t₁↓⊆U : (λ - → - ≤[ pos D ] leaves t₁) ⊆ (_holds ∘ U)
        conc-t₁↓⊆U a = φ a ∘ t₁-sim a
```

# Stone space

```
-- Do this for any distributive lattice.
{--
ss : FormalTopology zero zero
ss = (P , PS , perp) , sim
  where
    _⊑_ : Bool → Bool → Ω zero
    _     ⊑ true  = ⊤ , ⊤-prop
    false ⊑ _     = ⊤ , ⊤-prop
    true  ⊑ false = ⊥ , ⊥-prop

    ⊑-refl : (x : bool) → (x ⊑ x) holds
    ⊑-refl false = tt
    ⊑-refl true  = tt

    ⊑-trans : (x y z : bool) → (x ⊑ y) holds → (y ⊑ z) holds → (x ⊑ z) holds
    ⊑-trans false false false _ _ = tt
    ⊑-trans false false true  _ _ = tt
    ⊑-trans false true  true  _ _ = tt
    ⊑-trans true  true  true  _ _ = tt

    ⊑-antisym : (x y : bool) → (x ⊑ y) holds → (y ⊑ x) holds → x ≡ y
    ⊑-antisym false false _ _ = refl
    ⊑-antisym true true   _ _ = refl

    p : poset zero zero
    p = bool , posetstr _⊑_ bool-set ⊑-refl ⊑-trans ⊑-antisym

    ps : isapostsystem bool
    ps = expb , outb , revb
     where
        expb : bool → set
        expb a = σ[ b₁ ∈ bool ] σ[ b₂ ∈ bool ] ((b₁ ∨ b₂) ≡ a) ⊎ a ≡ false

        outb : {x : bool} → expb x → set
        outb (inj₁ (b₀ , b₁ , p)) = bool
        outb (inj₂ refl)          = ⊥

        revb : {x : bool} {y : expb x} → outb y → bool
        revb {y = inj₁ (b₀ , b₁ , p)} false = b₀
        revb {y = inj₁ (b₀ , b₁ , p)} true  = b₁
        revb {y = inj₂ refl} ()

    perp : hasperpetuation p ps
    perp false (inj₁ (false , false , _)) false = tt
    perp false (inj₁ (false , false , _)) true  = tt
    perp false (inj₂ refl) ()
    perp true  b c = tt

    sim : issimulation⋆ (p , ps , perp)
    sim false false tt t₀ = t₀ , λ _ → id
    sim true  true  tt t₀ = t₀ , (λ _ → id)
    sim true  false tt (leaf true) = leaf false , λ _ _ → ∣ tt , tt ∣
    sim true  false tt (branch (inj₁ (b₀ , b₁ , p)) f) = {!branch!} , {!!}
--}
```

Another example: trying to define Baire space.

```
-- --}
-- --}
-- --}
```
