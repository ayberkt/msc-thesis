```
{-# OPTIONS --cubical --safe #-}

module Cover where

open import Level
open import FormalTopology
open import Poset
open import Basis
```

## The test

```
module Test (ℱ : FormalTopology ℓ ℓ′) where
  private
    P    = pos ℱ
    D    = π₀ ℱ
    out  = outcome

  data _<|_ (a : ∣ P ∣ₚ) (U : ∣ P ∣ₚ → hProp ℓ) : Type ℓ where
    dir    : [ U a ] → a <| U
    branch : (b : exp ℱ a) → (f : (c : out ℱ b) → next ℱ c <| U) → a <| U
    squash : (p₀ p₁ : a <| U) → p₀ ≡ p₁

  <|-prop : (a : ∣ P ∣ₚ) (U : 𝒫 ∣ P ∣ₚ) → isProp (a <| U)
  <|-prop a U = squash
```

```
  ∩-comm : (U : 𝒫 ∣ P ∣ₚ) (V : 𝒫 ∣ P ∣ₚ) (a : ∣ P ∣ₚ)
         → [ ((V ∩ U) a ⇒ (U ∩ V) a) ⊓ ((U ∩ V) a ⇒ (V ∩ U) a) ]
  ∩-comm U V a =  V∩U⇒U∩V , U∩V⇒V∩U
    where
      V∩U⇒U∩V : [ (V ∩ U) a ] → [ (U ∩ V) a ]
      V∩U⇒U∩V (aεV , aεU) = aεU , aεV

      U∩V⇒V∩U : [ (U ∩ V) a ] → [ (V ∩ U) a ]
      U∩V⇒V∩U (aεU , aεV) = aεV , aεU

  <|-∩-comm : {U : 𝒫 ∣ P ∣ₚ} {V : 𝒫 ∣ P ∣ₚ} (a : ∣ P ∣ₚ) → a <| (V ∩ U) → a <| (U ∩ V)
  <|-∩-comm {U = U} {V} a (dir p)          = dir (π₀ (∩-comm U V a) p)
  <|-∩-comm {U = U} {V} a (branch b f)     = branch b (λ c → <|-∩-comm (next ℱ c) (f c))
  <|-∩-comm {U = U} {V} a (squash p₀ p₁ i) = squash (<|-∩-comm a p₀) (<|-∩-comm a p₁) i

  module _ {U : ∣ P ∣ₚ → hProp ℓ} (U-down : [ isDownwardsClosed P U ]) where

    ◀-lem₁ : {a a′ : ∣ P ∣ₚ} → [ a′ ⊑[ P ] a ] →  a <| U → a′ <| U
    ◀-lem₁ {_}     {_}  h (squash p₀ p₁ i) = squash (◀-lem₁ h p₀) (◀-lem₁ h p₁) i
    ◀-lem₁ {_}     {_}  h (dir q)          = dir (U-down _ _ q h)
    ◀-lem₁ {a = a} {a′} h (branch b f)     = branch b′ g
      where
        b′ : exp ℱ a′
        b′ = π₀ (sim ℱ a′ a h b)

        g : (c′ : out ℱ b′) → next ℱ c′ <| U
        g c′ = ◀-lem₁ (π₁ (π₁ (sim ℱ a′ a h b) c′)) (f c)
          where
            c : out ℱ b
            c = π₀ (π₁ (sim ℱ a′ a h b) c′)

  lem4 : (U : 𝒫 ∣ P ∣ₚ) (V : 𝒫 ∣ P ∣ₚ)
       → ((u : ∣ P ∣ₚ) → [ U u ] → u <| V) → (a : ∣ P ∣ₚ) → a <| U → a <| V
  lem4 U V h a (squash p₀ p₁ i) = squash (lem4 U V h a p₀) (lem4 U V h a p₁) i
  lem4 U V h a (dir p)          = h a p
  lem4 U V h a (branch b f)     = branch b (λ c → lem4  U V h (next ℱ c) (f c))

  module _ (U : 𝒫 ∣ P ∣ₚ) (V : 𝒫 ∣ P ∣ₚ) (V-dc : [ isDownwardsClosed P V ]) where
```

```
    lem2 : {a : ∣ P ∣ₚ} → a <| U → [ V a ] → a <| (U ∩ V)
    lem2 (squash p₀ p₁ i) h = squash (lem2 p₀ h) (lem2 p₁ h) i
    lem2 (dir q)          h = dir (q , h)
    lem2 (branch b f)     h = branch b (λ c → lem2 (f c) (V-dc _ _ h (mono ℱ _ b c)))

  module _ (U : 𝒫 ∣ P ∣ₚ) (V : 𝒫 ∣ P ∣ₚ)
           (U-dc : [ isDownwardsClosed P U ])
           (V-dc : [ isDownwardsClosed P V ]) where

    lem3 : (a a′ : ∣ P ∣ₚ) → [ a′ ⊑[ P ] a ] → a′ <| U → a <| V → a′ <| (U ∩ V)
    lem3 a a′ h (squash p₀ p₁ i) q = squash (lem3 a a′ h p₀ q) (lem3 a a′ h p₁ q) i
    lem3 a a′ h (dir p)          q = <|-∩-comm a′ (lem2 V U U-dc (◀-lem₁ V-dc h q) p)
    lem3 a a′ h (branch b f)     q = branch b g
      where
        g : (c : out ℱ b) → next ℱ c <| (U ∩ V)
        g c = lem3 a′ (next ℱ c) (mono ℱ a′ b c) (f c) (◀-lem₁ V-dc h q)
```
