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
  module _ {U : ∣ P ∣ₚ → hProp ℓ} (U-down : [ isDownwardsClosed P U ]) where

    ◀-lem₁ : {a a′ : ∣ P ∣ₚ} → [ a′ ⊑[ P ] a ] →  a <| U → a′ <| U
    ◀-lem₁ {_}     {_}  h (squash p₀ p₁ i) = squash (◀-lem₁ h p₀) (◀-lem₁ h p₁) i
    ◀-lem₁ {_}     {_}  h (dir q)          = dir (U-down _ _ q h)
    ◀-lem₁ {a = a} {a′} h (branch b f)     = branch b′ g
      where
        b′ : exp ℱ a′
        b′ = π₀ (sim ℱ a′ a h b)

        g : (c′ : out ℱ b′) → next ℱ c′ <| U
        g c′ = ◀-lem₁ δc′⊑δc (f c)
          where
            c : out ℱ b
            c = π₀ (π₁ (sim ℱ a′ a h b) c′)

            δc′⊑δc : [ next ℱ c′ ⊑[ P ] next ℱ c ]
            δc′⊑δc = π₁ (π₁ (sim ℱ a′ a h b) c′)

  lem₄ : (U : 𝒫 ∣ P ∣ₚ) (V : 𝒫 ∣ P ∣ₚ)
       → ((u : ∣ P ∣ₚ) → [ U u ] → u <| V) → (a : ∣ P ∣ₚ) → a <| U → a <| V
  lem₄ U V h a (squash p₀ p₁ i) = squash (lem₄ U V h a p₀) (lem₄ U V h a p₁) i
  lem₄ U V h a (dir p)          = h a p
  lem₄ U V h a (branch b f)     = branch b (λ c → lem₄  U V h (next ℱ c) (f c))

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

    lem3 : {a a′ : ∣ P ∣ₚ} → [ a′ ⊑[ P ] a ] → a <| U → a′ <| V → a′ <| (V ∩ U)
    lem3 {a} {a′} a′⊑a (squash p₀ p₁ i) q = squash (lem3 a′⊑a p₀ q) (lem3 a′⊑a p₁ q) i
    lem3 {a} {a′} a′⊑a (dir a∈U)        q = lem2 V U U-dc q (U-dc a a′ a∈U a′⊑a)
    lem3 {a} {a′} a′⊑a (branch b f)     q = branch b′ g
      where
        b′ : exp ℱ a′
        b′ = π₀ (sim ℱ a′ a a′⊑a b)

        g : (c′ : out ℱ b′) → next ℱ c′ <| (V ∩ U)
        g c′ = lem3 NTS (f c) (◀-lem₁ V-dc (mono ℱ a′ b′ c′) q)
          where
            c : out ℱ b
            c = π₀ (π₁ (sim ℱ a′ a a′⊑a b) c′)

            NTS : [ next ℱ c′ ⊑[ P ] next ℱ c ]
            NTS = π₁ (π₁ (sim ℱ a′ a a′⊑a b) c′)
```
