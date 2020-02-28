<!--
```
{-# OPTIONS --cubical --safe #-}

module TreeType where

open import Basis
open import Powerset
open import Truncation
open import Data.Empty  using (⊥; ⊥-elim)
open import Unit
open import Data.Bool   using (Bool; true; false; _∨_)
open import Data.List   using (List; _∷_; [])
open import Data.Nat    using (ℕ) renaming (zero to nzero; suc to nsuc)
open import Poset
open import Family
```
-->

# Introduction

The idea of this development is to define a [formal
topology](https://ncatlab.org/nlab/show/formal+topology) using the tree type
(sometimes called indexed containers or [interaction
systems](http://www.dcs.ed.ac.uk/home/pgh/interactive_systems.html)).

A _grammar_ on a type `A` consists of

1. A family of types `B : A → Type`
2. A family of types `C : (x : A) → B(x) → Type`
3. A function: `d : (x : A) → (y : B(x)) → (z : C(x, y)) → A`

```
GrammarStr : (A : Set ℓ) → Set (suc ℓ)
GrammarStr {ℓ = ℓ} A =
  Σ[ B ∈ (A → Set ℓ) ] Σ[ C ∈ ({x : A} → B x → Set ℓ) ]({x : A} → {y : B x} → C y → A)
```

The idea is that we view

1. `A` as a set of non-terminals; accordingly, we will call it `nonterminal`.
2. `B` as the type of productions for a given non-terminal; accordingly, we will call it
   `production`.
3. `C` as the type of locations/selectors of other non-terminals in a given production;
   accordingly, we will call it `location`.
4. `d` as a function that choose a given location in a production, therefore yielding
   a new non-terminal; accordingly, we will call it `choose`.

```
Grammar : (ℓ : Level) → Set (suc ℓ)
Grammar ℓ = Σ (Set ℓ) GrammarStr

nonterminal : Grammar ℓ → Set ℓ
production  : (D : Grammar ℓ) → nonterminal D → Set ℓ
location    : (D : Grammar ℓ) → {x : nonterminal D} → production D x → Set ℓ
choose      : (D : Grammar ℓ) {x : nonterminal D} {y : production D x}
            → location D y → nonterminal D

nonterminal (A , _ , _ , _) = A
production  (_ , B , _ , _) = B
location    (_ , _ , C , _) = C
choose      (_ , _ , _ , d) = d
```

Given a grammar `G`, which describes the structure of a tree, the type of inhabitants of a
specific tree satisfying `G` that starts with nonterminal `s` is given by the type `Tree D
s`.

```
record Tree (G : Grammar ℓ) (s : nonterminal G) : Set (suc ℓ) where
  constructor tree
  inductive

  field
    a : nonterminal G
    b : production G a
    c : (z : location G b) → Tree G (choose G z)
```

# Production⋆

Given a grammar `G` and a start nonterminal `s`, we denote by `Production⋆ D s` the type
of inhabited by repeated choices of productions, starting at `s`. One can think of this
as the reflexive-transitive closure of the choosing relation.

```
data Production⋆ (G : Grammar ℓ) : nonterminal G → Set ℓ where
  Leaf   : (a : nonterminal G) → Production⋆ G a
  Branch : {a : nonterminal G} (b : production G a)
         → ((c : location G b) → Production⋆ G (choose G c))
         → Production⋆ G a
```

Given a `Production⋆`, say `t`, we denote by `location⋆ t` the type of _sequences of
locations_ in `t`. In other words, an inhabitant of `location⋆ t` is a _specific_ sequence
of choices of experiments in the tree `t`.

```
module _ {G : Grammar ℓ} where

  location⋆ : {s : nonterminal G} → Production⋆ G s → Set ℓ
  location⋆ (Leaf   a)   = N₁ {ℓ}
  location⋆ (Branch b f) = Σ[ o ∈ (location G b) ] location⋆ (f o)
```

Finally, we can take a sequence of choices in `t : Production⋆` and then follow all the
choices all the way to the end. This procedure is implemented in the function `choose⋆`.

```
  choose⋆ : {s : nonterminal G}
          → (t : Production⋆ G s) → location⋆ t → nonterminal G
  choose⋆ (Leaf   s)   _       = s
  choose⋆ (Branch b f) (c , y) = choose⋆ (f c) y
```

**TODO**: explain.

```
  append : (a : nonterminal G)
         → (t : Production⋆ G a)
         → (g : (e : location⋆ t) → Production⋆ G (choose⋆ t e))
         → Production⋆ G a
  append a (Leaf   a)   g = g tt
  append a (Branch b f) g = Branch b λ c → append (choose G c) (f c) (λ - → g (c , -))
```

If we have a `Production⋆` constructed using `append`, we can take a sequence of outcomes
on it and then **bisect** these outcomes to obtain two different sequences of outcomes:
(1) one for the `Production⋆` we are appending onto, and (2) one for every `Production⋆`
appended under the one in (1). We give these in `bisect₀` and `bisect₁` respectively.

```
  bisect₀ : (a : nonterminal G)
          → (t : Production⋆ G a)
          → (f : (os : location⋆ t) → Production⋆ G (choose⋆ t os))
          → location⋆ (append a t f)
          → location⋆ t
  bisect₀ a (Leaf   a)   g os       = tt
  bisect₀ a (Branch b f) g (o , os) = o , bisect₀ (choose G o) (f o) (λ - → g (o , -)) os
```

```
  bisect₁ : (a : nonterminal G)
          → (t : Production⋆ G a)
          → (g : (os : location⋆ t) → Production⋆ G (choose⋆ t os))
          → (os : location⋆ (append a t g))
          → location⋆ (g (bisect₀ a t g os))
  bisect₁ a (Leaf a)     g os       = os
  bisect₁ a (Branch b f) g (o , os) = bisect₁ (choose G o) (f o) (λ os′ → g (o , os′)) os
```


# Perpetuation ("Progressiveness", "Monotonicity")

Given a Post system, we will now require an order on the nonterminals representing whether
one contains more information than another. The idea is that if nonterminal `a₁` contains
more information than `a₀` then the knowledge state there is **more refined** than the one
at `a₁`; we thus write `a₁ ⊑ a₀`.

As we have already hinted, the point of this order is to view each nonterminal as a stage
of information. In light of this view, `choose` will be analogous to learning something
from an experiment which takes one from one stage to another (we will shortly introduce
more suggestive terminology).

In order for this to make sense, though, we must require that choosing nonterminals always
takes us to stages that are at least as refined as the current one. The intuitive reading
of this is: _experimentation never takes away existing knowledge_. Accordingly, this
property will be called **perpetuation**; we express it in the type family
`HasPerpetuation`.

```
HasPerpetuation : (P : Poset ℓ₀ ℓ₁) → GrammarStr ∣ P ∣ₚ → Set (ℓ₀ ⊔ ℓ₁)
HasPerpetuation {ℓ₀} P P-disc =
  (x : nonterminal D) (y : production D x) (z : location D y) →
    (choose D z) ⊑[ P ] x is-true
  where
    D : Grammar ℓ₀
    D = (∣ P ∣ₚ , P-disc)
```

We can define the analogous property for `choose⋆`:

```
HasPerpetuation⋆ : (P : Poset ℓ₀ ℓ₁) → GrammarStr ∣ P ∣ₚ → Set (ℓ₀ ⊔ ℓ₁)
HasPerpetuation⋆ {ℓ₀} P P-disc =
  (a : nonterminal D) (t : Production⋆ D a) (o : location⋆ t) →
    choose⋆ t o ⊑[ P ] a is-true
  where
    D : Grammar ℓ₀
    D = (∣ P ∣ₚ , P-disc)
```

We will refer to a Post system that has the perpetutation property as a
`Discipline`, it the sense that the stages of knowledge (i.e., the nonterminals)
resemble a _discipline of knowledge_. Accordingly, we introduce new terminology
for the projections.

```
Discipline : (ℓ₀ ℓ₁ : Level) → Set (suc ℓ₀ ⊔ suc ℓ₁)
Discipline ℓ₀ ℓ₁ =
  Σ[ P ∈ (Poset ℓ₀ ℓ₁) ] Σ[ P-disc ∈ (GrammarStr ∣ P ∣ₚ) ] HasPerpetuation P P-disc
```

It will be convenient to be easily refer to the poset and the post system
contained inside a discipline.

```
pos : Discipline ℓ₀ ℓ₁ → Poset ℓ₀ ℓ₁
pos (P , _) = P

post : (D : Discipline ℓ₀ ℓ₁) → Grammar ℓ₀
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

outcome⋆ : (D : Discipline ℓ₀ ℓ₁) → {a : stage D} → experiment⋆ D a → Set ℓ₀
outcome⋆ D = location⋆ {G = post D}
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
prog⇒prog⋆ : (D : Discipline ℓ₀ ℓ₁) → HasPerpetuation⋆ (pos D) (π₁ (post D))
prog⇒prog⋆ D@(P , disc , IS) a (Leaf a)   o = ⊑[ P ]-refl a
prog⇒prog⋆ D@(P , disc , IS) a (Branch b f) (o , os) = φ
  where
   open PosetReasoning P

   IH : choose⋆ (f o) os ⊑[ P ] revise D o is-true
   IH = prog⇒prog⋆ D (choose (∣ P ∣ₚ , disc) o) (f o) os

   φ : choose⋆ (Branch b f) (o , os) ⊑[ P ] a is-true
   φ = choose⋆ (Branch b f) (o , os) ⊑⟨ IH ⟩ choose (post D) o ⊑⟨ IS a b o ⟩ a ■

```

# Simulation

The other property we are interested in, which will define a formal topology
when coupled with perpetuation, is **simulation**. Let us first introduce some
notation to build up towards its definition.

TODO: explain the fact that we tried to truncate this and could not.
TODO: do not call this a predicate.

`down P ℱ a` denotes a predicate expressing: stage `a` has a more refined state
of information than at least one stage in `ℱ`.

```
downs : (P : Poset ℓ₀ ℓ₁) → Sub ℓ₂ ∣ P ∣ₚ → ∣ P ∣ₚ → Set (ℓ₁ ⊔ ℓ₂)
downs P ℱ@(I , F) a = Σ[ i ∈ I ] a ⊑[ P ] F i is-true

syntax downs P ℱ a = a ↓[ P ] ℱ
```

We will often be dealing with the predicate `ℱ ↓[ P ] -`.

Ad-hoc notion of subset (TODO: call this something else) since there are some
universe problems with `𝒫`. _This should be replaced with `𝒫` once it is
properly generalised._

Given a `Production⋆` `t`, we can define a family of nonterminals it _reaches_ i.e., the
leaves of the tree.

```
leaves : {D : Grammar ℓ} {s : nonterminal D} → Production⋆ D s → Sub ℓ (nonterminal D)
leaves e = location⋆ e , choose⋆ e
```

We may hence define a notion of refinement: `t₀` refines `t₁` iff _any stage that is more
informative than a leaf of `t₀` is more informative than a leaf of `t₁`.

```
refines : (D : Discipline ℓ₀ ℓ₁) {s s′ : stage D}
        → experiment⋆ D s′ → experiment⋆ D s → Set (ℓ₀ ⊔ ℓ₁)
refines D@(P , _) e f = (λ - → - ↓[ P ] leaves e) ⊆⊆ (λ - → - ↓[ P ] leaves f)

syntax refines D e f = e ℛ[ D ] f
```

Using the notion of refinement, we formulate the simulation property (given in
`IsSimulation⋆`) which says: given stages `a₁ ⊑ a₀`, for any `experiment⋆` on `a₀`, there
exists some `experiment⋆` `t₁` that is a refinement of `t₀`. In other words: as we move
towards more refined states of information, we maintain access to as refined sequences of
experiments.

```
module _ (D : Discipline ℓ₀ ℓ₁) where

  private
    P    = pos   D
    G    = post  D
    prog = π₁    D

  open PosetReasoning P

  IsSimulation⋆ : Set (ℓ₀ ⊔ ℓ₁)
  IsSimulation⋆ =
    (a₀ a₁ : stage D) → a₁ ⊑[ P ] a₀ is-true →
      (t₀ : experiment⋆ D a₀) → Σ[ t₁ ∈ (experiment⋆ D a₁) ] (t₁ ℛ[ D ] t₀)
```

The analogous property for single experiments is given in `IsSimulation` which in fact
implies `IsSimulation⋆`.

```
  IsSimulation : Set (ℓ₀ ⊔ ℓ₁)
  IsSimulation =
    (a₀ a₁ : stage D) → a₁ ⊑[ P ] a₀ is-true → (b₀ : exp D a₀) →
      Σ[ b₁ ∈ (exp D a₁) ]  (λ - →  - ↓[ P ] (outcome D b₁ , revise D))
                         ⊆⊆ (λ - →  - ↓[ P ] (outcome D b₀ , revise D))
```

```
  sim⇒sim⋆ : IsSimulation → IsSimulation⋆

  sim⇒sim⋆ _ a₀ a₁ a₁⊑a₀ (Leaf a₀) = (Leaf a₁) , ψ
    where
      ψ : (x : stage D)
        → downs (pos D) (leaves {D = post D} (Leaf a₁)) x
        → downs (pos D) (leaves {D = post D} (Leaf a₀)) x
      ψ a (tt , a⊑a₁) = tt , (a ⊑⟨ a⊑a₁ ⟩ a₁ ⊑⟨ a₁⊑a₀ ⟩ a₀ ■)

  sim⇒sim⋆ D-sim a₀ a₁ a₀⊒a₁ t₀@(Branch b₀ f) =
    t₁ , t₁-refines-t₀
    where
      b₁ : exp D a₁
      b₁ = π₀ (D-sim a₀ a₁ a₀⊒a₁ b₀)

      φ : (a : stage D)
        → a ↓[ P ] (outcome D b₁ , revise D) → a ↓[ P ] (outcome D b₀ , revise D)
      φ = π₁ (D-sim a₀ a₁ a₀⊒a₁ b₀)

      g : (o₁ : outcome D b₁) → experiment⋆ D (revise D o₁)
      g o₁ = π₀ IH
        where
          rev-o₀≤sat-b₀ : revise D o₁ ↓[ P ] (outcome D b₀ , revise D)
          rev-o₀≤sat-b₀ = φ (revise D o₁) (o₁ , (⊑[ P ]-refl _))

          o₀ : outcome D b₀
          o₀ = π₀ rev-o₀≤sat-b₀

          rev-o₁⊑rev-o₀ : revise D o₁ ⊑[ P ] revise D o₀ is-true
          rev-o₁⊑rev-o₀ = π₁ rev-o₀≤sat-b₀

          IH : Σ[ t′ ∈ experiment⋆ D (revise D o₁) ] refines D t′ (f o₀)
          IH = sim⇒sim⋆ D-sim (revise D o₀) (revise D o₁) rev-o₁⊑rev-o₀ (f o₀)

      t₁ = Branch b₁ g

      t₁-refines-t₀ : (a : stage D) → a ↓[ P ] leaves t₁ → a ↓[ P ] leaves t₀
      t₁-refines-t₀ a ((o₁ , os₁) , a≤leaves-t₁-os) = (o₀ , os₀) , a⊑leaf-t₀-at-o₀-os₀
        where
          rev-o₀≤sat-b₀ : revise D o₁ ↓[ P ] (outcome D b₀ , revise D)
          rev-o₀≤sat-b₀ = φ (revise D o₁) (o₁ , ⊑[ P ]-refl _)

          o₀ : outcome D b₀
          o₀ = π₀ rev-o₀≤sat-b₀

          IH : Σ[ t′ ∈ experiment⋆ D (revise D o₁) ] refines D t′ (f o₀)
          IH = sim⇒sim⋆ D-sim (revise D o₀) _ (π₁ (φ _ (o₁ , ⊑[ P ]-refl _))) (f o₀)

          os₀ : location⋆ (f o₀)
          os₀ = π₀ (π₁ IH a (os₁ , a≤leaves-t₁-os))

          a⊑leaf-t₀-at-o₀-os₀ : a ⊑[ P ] (leaves t₀ € (o₀ , os₀)) is-true
          a⊑leaf-t₀-at-o₀-os₀ = π₁ ((π₁ IH) a (os₁ , a≤leaves-t₁-os))
```

# Formal Topology

A _formal topology_ is a discipline with the simulation property.

```
FormalTopology : (ℓ₀ ℓ₁ : Level) → Set (suc ℓ₀ ⊔ suc ℓ₁)
FormalTopology ℓ₀ ℓ₁ = Σ[ D ∈ (Discipline ℓ₀ ℓ₁) ] (IsSimulation D)

cover-of : (𝒯 : FormalTopology ℓ₀ ℓ₁)
         → stage (π₀ 𝒯) → (stage (π₀ 𝒯) → Ω ℓ₂) → Set (ℓ₀ ⊔ ℓ₁ ⊔ ℓ₂)
cover-of 𝒯@(D , topo) a U =
  ∥ Σ[ t ∈ (experiment⋆ D a) ] (λ - → - ↓[ pos D ] leaves t) ⊆⊆ (_is-true ∘ U) ∥

syntax cover-of 𝒯 a U = a ◀[ 𝒯 ] U
```

```
private
  down-closure : (𝒯 : FormalTopology ℓ₀ ℓ₁) (U : stage (π₀ 𝒯) → Ω (ℓ₀ ⊔ ℓ₁))
              → (a₀ a₁ : stage (π₀ 𝒯))
              → a₁ ⊑[ pos (π₀ 𝒯) ] a₀ is-true
              → a₀ ◀[ 𝒯 ] U
              → a₁ ◀[ 𝒯 ] U
  down-closure 𝒯@(D , D-sim) U a₀ a₁ a₀⊒a₁ a₀◀U = ∥∥-rec (∥∥-prop _) (∣_∣ ∘ ψ) a₀◀U
    where
      ψ : Σ[ t₀ ∈ experiment⋆ D a₀ ] (λ - → - ↓[ pos D ] leaves t₀) ⊆⊆ (_is-true ∘ U)
        → Σ[ t₁ ∈ experiment⋆ D a₁ ] (λ - → - ↓[ pos D ] leaves t₁) ⊆⊆ (_is-true ∘ U)
      ψ (t , φ) = t₁ , conc-t₁↓⊆U
        where
          t₁ : experiment⋆ D a₁
          t₁ = π₀ (sim⇒sim⋆ D D-sim a₀ a₁ a₀⊒a₁ t)

          t₁-sim : refines D t₁ t
          t₁-sim = π₁ (sim⇒sim⋆ D D-sim a₀ a₁ a₀⊒a₁ t)

          conc-t₁↓⊆U : (λ - → - ↓[ pos D ] leaves t₁) ⊆⊆ (_is-true ∘ U)
          conc-t₁↓⊆U a = φ a ∘ t₁-sim a
```

```
module _ (𝒯 : FormalTopology ℓ₀ ℓ₁) where

  private
    D     = π₀ 𝒯
    D-sim = π₁ 𝒯

  _↓_ : ∣ pos D ∣ₚ → Sub ℓ₂ ∣ pos D ∣ₚ → Set (ℓ₁ ⊔ ℓ₂)
  _↓_ = λ a ℱ → a ↓[ pos D ] ℱ

  open PosetReasoning (π₀ D)

  _⊗_ : {a : stage D} → experiment⋆ D a → experiment⋆ D a → experiment⋆ D a
  _⊗_ {a = a} t@(Leaf a)     t′@(Leaf a)      = Leaf a
  _⊗_ {a = a} t@(Leaf a)     t′               = t′
  _⊗_ {a = a} t              t′@(Leaf a)      = t
  _⊗_ {a = a} t@(Branch b f) t′@(Branch b′ g) = append a t h
    where
      h : (os : location⋆ t) → experiment⋆ D (choose⋆ t os)
      h os = π₀ (sim⇒sim⋆ D D-sim a (choose⋆ t os) a⊑choose⋆-t-os t′)
        where
          a⊑choose⋆-t-os : choose⋆ t os ⊑[ pos D ] a is-true
          a⊑choose⋆-t-os = prog⇒prog⋆ D a t os

  bisect₀-lemma : (a a′ : stage D)
                → (t : experiment⋆ D a)
                → (f : (os : outcome⋆ D t) → experiment⋆ D (choose⋆ t os))
                → (os : outcome⋆ D (append a t f))
                → a′ ⊑[ pos D ] (leaves (append a t f) € os) is-true
                → a′ ⊑[ pos D ] (leaves t € bisect₀ a t f os) is-true
  bisect₀-lemma a a′ (Leaf a) g os a′⊑leaves-append-etc =
    a′                                  ⊑⟨ a′⊑leaves-append-etc     ⟩
    leaves (append a (Leaf a) g) € os   ⊑⟨ prog⇒prog⋆ D a (g tt) os ⟩
    a                                   ■
  bisect₀-lemma a a′ t@(Branch b f) g (o , os) a′⊑leaves-append-etc =
    a′                                  ⊑⟨ a′⊑leaves-append-etc     ⟩
    leaves (append a t g) € (o , os)    ⊑⟨ φ                        ⟩
    leaves t € (bisect₀ a t g (o , os)) ■
    where
      φ : (leaves (append a t g) € (o , os))
        ⊑[ pos D ] (leaves t € (bisect₀ a t g (o , os))) is-true
      φ = bisect₀-lemma (revise D o) _ (f o) (λ - → g (o , -)) os (≡⇒⊑ (pos D) refl)

  bisect₁-lemma : (a a′ : stage D)
                → (t : experiment⋆ D a)
                → (f : (os : outcome⋆ D t) → experiment⋆ D (choose⋆ t os))
                → (γ : a′ ↓ leaves (append a t f))
                → a′ ↓ leaves (f (bisect₀ a t f (π₀ γ)))
  bisect₁-lemma a a′ (Leaf   a)   g p              = p
  bisect₁-lemma a a′ (Branch b f) g ((o , os) , q) =
    bisect₁-lemma (revise D o) a′ (f o) (λ os′ → g (o , os′)) (os , q)

  ⊗-lemma₀ : (a a′ : stage D) (t t′ : experiment⋆ D a)
           → a′ ↓ leaves (t ⊗ t′) → a′ ↓ leaves t
  ⊗-lemma₀ a a′ t@(Leaf a) t′@(Leaf   a) a′≤leaves-t⊗t′ = a′≤leaves-t⊗t′
  ⊗-lemma₀ a a′ t@(Leaf a) t′@(Branch b′ g) (os , γ) = tt , a′⊑a
    where
      a′⊑a : a′ ⊑[ pos D ] a is-true
      a′⊑a = a′ ⊑⟨ γ ⟩ _ ⊑⟨ prog⇒prog⋆ D a t′ os ⟩ a ■
  ⊗-lemma₀ a a′ t@(Branch b x) t′@(Leaf   a)    (os , γ) = os , γ
  ⊗-lemma₀ a a′ t@(Branch b f) t′@(Branch b′ g) (os , γ) =
    bisect₀ a t h os , bisect₀-lemma a a′ t h os γ
    where
      h : (os : location⋆ t) → experiment⋆ D (choose⋆ t os)
      h os = π₀ (sim⇒sim⋆ D D-sim a (choose⋆ t os) a⊑choose⋆-t-os t′)
        where
          a⊑choose⋆-t-os : choose⋆ t os ⊑[ pos D ] a is-true
          a⊑choose⋆-t-os = prog⇒prog⋆ D a t os

  ⊗-lemma₁ : (a a′ : stage D) (t t′ : experiment⋆ D a)
           → a′ ↓ leaves (t ⊗ t′) → a′ ↓ leaves t′
  ⊗-lemma₁ a a′ t t′@(Leaf a) (os , γ) =
    tt , (a′ ⊑⟨ γ ⟩ leaves (t ⊗ t′) € os ⊑⟨ prog⇒prog⋆ D a (t ⊗ t′) os ⟩ a ■)
  ⊗-lemma₁ a a′ t@(Leaf   a)   t′@(Branch b′ g) (os       , γ) = os , γ
  ⊗-lemma₁ a a′ t@(Branch b f) t′@(Branch b′ g) ((o , os) , γ) = a′≤leaves-t
    where
      a′≤leaves-t : a′ ↓ leaves t′
      a′≤leaves-t = π₁ sim⋆ a′ (bisect₁-lemma a a′ t h ((o , os) , γ))
        where
          h : (os′ : outcome⋆ D t) → experiment⋆ D (choose⋆ t os′)
          h os′ = π₀ (sim⇒sim⋆ D D-sim a (choose⋆ t os′) choose⋆-t-os′⊑a t′)
            where
              choose⋆-t-os′⊑a : choose⋆ t os′ ⊑[ pos D ] a is-true
              choose⋆-t-os′⊑a = prog⇒prog⋆ D a t os′

          OS : outcome⋆ D t
          OS = (o , bisect₀ (revise D o) (f o) (λ os′ → h (o , os′)) os)

          choose⋆-t-OS⊑a : choose⋆ t OS ⊑[ pos D ] a is-true
          choose⋆-t-OS⊑a = prog⇒prog⋆ D a t OS

          sim⋆ = sim⇒sim⋆ D D-sim a (choose⋆ t OS) choose⋆-t-OS⊑a t′

  a◀U∧a◀V⇒a◀U∩V : (U V : 𝒫 (stage (π₀ 𝒯)))
                → (a : stage (π₀ 𝒯))
                → a ◀[ 𝒯 ] U → a ◀[ 𝒯 ] V → a ◀[ 𝒯 ] (U ∩ V)
  a◀U∧a◀V⇒a◀U∩V U V a a◀U a◀V =
    ∥∥-rec (∥∥-prop _) (λ p → ∥∥-rec (∥∥-prop _) (λ q → ∣ φ U V a p q ∣) a◀V) a◀U
    where
      φ : (U V : 𝒫 (stage D)) (a : stage D)
        → Σ[ t₀ ∈ (experiment⋆ D a) ] (λ - → - ↓ (leaves t₀)) ⊆⊆ (_is-true ∘ U)
        → Σ[ t₁ ∈ (experiment⋆ D a) ] (λ - → - ↓ (leaves t₁)) ⊆⊆ (_is-true ∘ V)
        → Σ[ t₂ ∈ (experiment⋆ D a) ] (λ - → - ↓ (leaves t₂)) ⊆⊆ (_is-true ∘ (U ∩ V))
      φ U V a (t , p) (t′ , q) = t ⊗ t′ , NTS
        where
          sim⋆ : (os : outcome⋆ D t)
               → Σ[ t⋆ ∈ experiment⋆ D (choose⋆ t os) ] t⋆ ℛ[ D ] t′
          sim⋆ os = sim⇒sim⋆ D D-sim a (choose⋆ t os) (prog⇒prog⋆ D a t os) t′

          NTS : (a′ : stage D) → a′ ↓ leaves (t ⊗ t′) → (U ∩ V) a′ is-true
          NTS a′ γ = p a′ (⊗-lemma₀ a a′ t t′ γ) , q a′ (⊗-lemma₁ a a′ t t′ γ)
```

# Baire space

```
-- TODO.
```

# Stone space from a Boolean algebra

```
-- TODO.
```

```
-- --}
-- --}
-- --}
```
