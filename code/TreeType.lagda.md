<!--
```
module TreeType where

open import Variables
open import Data.Empty  using (⊥; ⊥-elim)
open import Data.Unit   using (⊤; tt)
open import Data.Bool   using (Bool; true; false)
open import Data.List   using (List; _∷_; [])
open import Common
open import Poset
open import Homotopy
```
-->

# Introduction

We would like to start by defining a predicate on some type `A` expressing what it means
for `A` to behave like a type of _stages of knowledge_ which are connected via a notion of
_experimentation_. We call such a type a _discipline_ in the sense of a _discipline of
knowledge_.

```
record IsADiscipline (A : Set ℓ) : Set (suc ℓ) where
  constructor disc

  field
```

1. An `A`-indexed family of types `B` which can be interpreted as representing _the set of
   possible experiments one can conduct at stage `x`_.

```
    B : A → Set ℓ
```

2. Given a stage of knowledge `x : A` and experiment `y : B x`, `C x y` is the type of
   _possible outcomes of the experiment `x`_.

```
    C : (x : A) → B x → Set ℓ
```

3. After performing the experiment, the state of knowledge is _updated_ in light of the
   obtained data. `d` takes a state of knowledge `x`, an experiment `y`, and and outcome
   `z` of the experiment and yields a new knowledge state.

```
    d : {x : A} {y : B x} → (z : C x y) → A
```

4. Finally, we require an initial knowledge state to serve as a start node.

```
    a : A
```

We collect disciplines in the type `Discipline`.

```
Discipline : (ℓ : Level) → Set (suc ℓ)
Discipline ℓ = Σ[ A ∈ (Set ℓ) ] (IsADiscipline A)
```

We will be interested in those disciplines in which experiments are well-designed in the
sense that conducting an experiment lands us in a _superior_ state of knowledge. We call
this condition _progressiveness_ in the sense that the experiments help us advance the
discipline of knowledge. Therefore we require a partial ordering on the knowledge stages
expressing whether one contains more information than the other.

We define the predicate expressing that a discipline on a poset is progressive as follows:

```
IsProgressive : (P : Poset ℓ₀ ℓ₁) → IsADiscipline ∣ P ∣ₚ → Set (ℓ₀ ⊔ ℓ₁)
IsProgressive P (disc B C d _) = (x : ∣ P ∣ₚ) (y : B x) (z : C x y) → (d z) ⊑[ P ] x holds 
```

We collect progressive disciplines in the following type, that we call `Science`.

```
PreScience : (ℓ₀ ℓ₁ : Level) → Set (suc ℓ₀ ⊔ suc ℓ₁)
PreScience ℓ₀ ℓ₁ =
  Σ[ P ∈ (Poset ℓ₀ ℓ₁) ] Σ[ P-disc ∈ (IsADiscipline ∣ P ∣ₚ) ] IsProgressive P P-disc
```

# Elimination

# Examples

```
data EvenOddA : Set where
  Even Odd : EvenOddA

data OddB : Set where
  sO : OddB

data EvenB : Set where
  zeroE sE : EvenB

EvenOdd : Discipline zero
EvenOdd = EvenOddA , disc B C d Even
  where
    B : EvenOddA → Set zero
    B Even = EvenB
    B Odd  = OddB

    C : (x : EvenOddA) → B x → Set zero
    C Even zeroE = ⊥
    C Even sE    = ⊤
    C Odd  sO    = ⊤

    d : {x : EvenOddA} {y : B x} → C x y → EvenOddA
    d {Even} {sE} tt = Odd
    d {Odd}  {sO} tt = Even
```

```
-- --}
-- --}
-- --}
```
