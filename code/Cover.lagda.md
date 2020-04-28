```
{-# OPTIONS --cubical --safe #-}

module Cover where

open import Level
open import FormalTopology
open import Powerset
open import Poset
open import Basis
```

## The test

```
module Test (ℱ : FormalTopology ℓ ℓ′) where
  private
    P    = π₀ (π₀ ℱ)
    D    = π₀ ℱ
    out  = outcome
    sim  = π₁ ℱ
    mono = π₁ (π₁ (π₀ ℱ))

  data _<|_ (a : ∣ P ∣ₚ) (U : ∣ P ∣ₚ → hProp ℓ) : Type ℓ where
    dir    : U a is-true → a <| U
    branch : (b : exp D a) → (f : (c : out D b) → next D c <| U) → a <| U
    squash : (p₀ p₁ : a <| U) → p₀ ≡ p₁

  <|-prop : (a : ∣ P ∣ₚ) (U : 𝒫 ∣ P ∣ₚ) → isProp (a <| U)
  <|-prop a U = squash
```

```
  ∩-comm : (U : 𝒫 ∣ P ∣ₚ) (V : 𝒫 ∣ P ∣ₚ) (a : ∣ P ∣ₚ)
         → (((V ∩ U) a ⇒ (U ∩ V) a) ∧ ((U ∩ V) a ⇒ (V ∩ U) a)) is-true
  ∩-comm U V a =  V∩U⇒U∩V , U∩V⇒V∩U
    where
      V∩U⇒U∩V : (V ∩ U) a is-true → (U ∩ V) a is-true
      V∩U⇒U∩V (aεV , aεU) = aεU , aεV

      U∩V⇒V∩U : (U ∩ V) a is-true → (V ∩ U) a is-true
      U∩V⇒V∩U (aεU , aεV) = aεV , aεU

  <|-∩-comm : {U : 𝒫 ∣ P ∣ₚ} {V : 𝒫 ∣ P ∣ₚ} (a : ∣ P ∣ₚ) → a <| (V ∩ U) → a <| (U ∩ V)
  <|-∩-comm {U = U} {V} a (dir p)          = dir (π₀ (∩-comm U V a) p)
  <|-∩-comm {U = U} {V} a (branch b f)     = branch b (λ c → <|-∩-comm (next D c) (f c))
  <|-∩-comm {U = U} {V} a (squash p₀ p₁ i) = squash (<|-∩-comm a p₀) (<|-∩-comm a p₁) i

  module _ {U : ∣ P ∣ₚ → hProp ℓ} (U-down : IsDownwardClosed P U is-true) where

    lem1 : {a a′ : ∣ P ∣ₚ} → a′ ⊑[ P ] a is-true →  a <| U → a′ <| U
    lem1 {_}     {_}  h (squash p₀ p₁ i) = squash (lem1 h p₀) (lem1 h p₁) i
    lem1 {_}     {_}  h (dir q)          = dir (U-down _ _ q h)
    lem1 {a = a} {a′} h (branch b f)     = branch b′ g
      where
        b′ : exp D a′
        b′ = π₀ (sim a′ a h b)

        g : (c′ : out D b′) → next D c′ <| U
        g c′ = lem1 (π₁ (π₁ (sim a′ a h b) c′)) (f c)
          where
            c : out D b
            c = π₀ (π₁ (sim a′ a h b) c′)

  lem4 : (U : 𝒫 ∣ P ∣ₚ) (V : 𝒫 ∣ P ∣ₚ)
       → ((u : ∣ P ∣ₚ) → U u is-true → u <| V) → (a : ∣ P ∣ₚ) → a <| U → a <| V
  lem4 U V h a (squash p₀ p₁ i) = squash (lem4 U V h a p₀) (lem4 U V h a p₁) i
  lem4 U V h a (dir p)          = h a p
  lem4 U V h a (branch b f)     = branch b (λ c → lem4  U V h (next D c) (f c))

  module _ (U : 𝒫 ∣ P ∣ₚ) (V : 𝒫 ∣ P ∣ₚ) (V-dc : IsDownwardClosed P V is-true) where
```

```
    lem2 : {a : ∣ P ∣ₚ} → a <| U → V a is-true → a <| (U ∩ V)
    lem2 (squash p₀ p₁ i) h = squash (lem2 p₀ h) (lem2 p₁ h) i
    lem2 (dir q)          h = dir (q , h)
    lem2 (branch b f)     h = branch b (λ c → lem2 (f c) (V-dc _ _ h (mono _ b c)))

  module _ (U : 𝒫 ∣ P ∣ₚ) (V : 𝒫 ∣ P ∣ₚ)
           (U-dc : IsDownwardClosed P U is-true)
           (V-dc : IsDownwardClosed P V is-true) where

    lem3 : (a a′ : ∣ P ∣ₚ) → a′ ⊑[ P ] a is-true → a′ <| U → a <| V → a′ <| (U ∩ V)
    lem3 a a′ h (squash p₀ p₁ i) q = squash (lem3 a a′ h p₀ q) (lem3 a a′ h p₁ q) i
    lem3 a a′ h (dir p)          q = <|-∩-comm a′ (lem2 V U U-dc (lem1 V-dc h q) p)
    lem3 a a′ h (branch b f)     q = branch b g
      where
        g : (c : out D b) → next D c <| (U ∩ V)
        g c = lem3 a′ (next D c) (mono a′ b c) (f c) (lem1 V-dc h q)
```
