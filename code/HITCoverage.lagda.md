```
{-# OPTIONS --cubical --safe #-}

module HITCoverage where

open import Level
open import Basis
```

## The test

```
module Test (P     : Type ℓ)
            (_⊑_   : P → P → Type ℓ′)
            -- (refl  : (a        : P) → a ⊑ a)
            -- (trans : (a₀ a₁ a₂ : P) → a₀ ⊑ a₁ → a₁ ⊑ a₂ → a₀ ⊑ a₂)
            (exp   : P → Type ℓ)
            (out   : {a : P} → exp a → Type ℓ)
            (rev   : {a : P} → {b : exp a} → out b → P)
            (mono  : (a : P) → (b : exp a) → (c : out b) → rev c ⊑ a)
            (sim   : (a₀ a : P)
                   → a₀ ⊑ a
                   → (b : exp a)
                   → Σ (exp a₀)
                       (λ b₀ → (c₀ : out b₀) →
                         Σ (out b) (λ c → (rev c₀) ⊑ (rev c))))
            where

  IsDownwardClosed : (P → Type ℓ₀) → Type (ℓ ⊔ ℓ′ ⊔ ℓ₀)
  IsDownwardClosed U = {a₀ a : P} → U a → a₀ ⊑ a → U a₀

  data _<|_ (a : P) (U : P → Type ℓ) : Type ℓ where
    dir    : U a → a <| U
    branch : (b : exp a) → (f : (c : out b) → rev c <| U) → a <| U
    squash : (p₀ p₁ : a <| U) → p₀ ≡ p₁

  <|-prop : (a : P) (U : P → Type ℓ) → IsProp (a <| U)
  <|-prop a U = squash
```

```
  private
    _∩_ : (P → Type ℓ₀) → (P → Type ℓ₁) → P → Type (ℓ₀ ⊔ ℓ₁)
    U ∩ V = λ x → U x × V x

  ∩-comm : (U : P → Type ℓ₀) → (V : P → Type ℓ₁)
         → (a : P) → ((V ∩ U) a → (U ∩ V) a) × ((U ∩ V) a → (V ∩ U) a)
  ∩-comm U V a =  V∩U⇒U∩V , U∩V⇒V∩U
    where
      V∩U⇒U∩V : (V ∩ U) a → (U ∩ V) a
      V∩U⇒U∩V (aεV , aεU) = aεU , aεV

      U∩V⇒V∩U : (U ∩ V) a → (V ∩ U) a
      U∩V⇒V∩U (aεU , aεV) = aεV , aεU

  <|-∩-comm : {U : P → Type ℓ} {V : P → Type ℓ}
            → (a : P) → a <| (V ∩ U) → a <| (U ∩ V)
  <|-∩-comm {U = U} {V} a (dir p)          = dir (π₀ (∩-comm U V a) p)
  <|-∩-comm {U = U} {V} a (branch b f)     = branch b (λ c → <|-∩-comm (rev c) (f c))
  <|-∩-comm {U = U} {V} a (squash p₀ p₁ i) = squash (<|-∩-comm a p₀) (<|-∩-comm a p₁) i

  module _ {U : P → Type ℓ} (U-down : IsDownwardClosed U) where

    lem1 : {a a′ : P} → a′ ⊑ a →  a <| U → a′ <| U
    lem1 {_}     {_}  h (squash p₀ p₁ i) = squash (lem1 h p₀) (lem1 h p₁) i
    lem1 {_}     {_}  h (dir q)          = dir (U-down q h)
    lem1 {a = a} {a′} h (branch b f)     = branch b′ g
      where
        b′ : exp a′
        b′ = π₀ (sim a′ a h b)

        g : (c′ : out b′) → rev c′ <| U
        g c′ = lem1 (π₁ (π₁ (sim a′ a h b) c′)) (f c)
          where
            c : out b
            c = π₀ (π₁ (sim a′ a h b) c′)

  lem4 : (U : P → Type ℓ) (V : P → Type ℓ)
       → ((u : P) → U u → u <| V) → (a : P) → a <| U → a <| V
  lem4 U V h a (squash p₀ p₁ i) = squash (lem4 U V h a p₀) (lem4 U V h a p₁) i
  lem4 U V h a (dir p)          = h a p
  lem4 U V h a (branch b f)     = branch b (λ c → lem4  U V h (rev c) (f c))

  module _ {U : P → Type ℓ} {V : P → Type ℓ}
           (U-down : IsDownwardClosed U) (V-down : IsDownwardClosed V) where
```

```
    lem2 : {a : P} → a <| U → V a → a <| (U ∩ V)
    lem2 {a = a} (squash p₀ p₁ i) h = squash (lem2 p₀ h) (lem2 p₁ h) i
    lem2 {a = a} (dir q)          h = dir (q , h)
    lem2 {a = a} (branch b f)     h = branch b (λ c → lem2 (f c) (V-down h (mono a b c)))

  module _ (U : P → Type ℓ) (V : P → Type ℓ)
           (U-down : IsDownwardClosed U) (V-down : IsDownwardClosed V) where

    lem3 : (a a′ : P) → a′ ⊑ a → a′ <| U → a <| V → a′ <| (U ∩ V)
    lem3 a a′ h (squash p₀ p₁ i) q = squash (lem3 a a′ h p₀ q) (lem3 a a′ h p₁ q) i
    lem3 a a′ h (dir p)          q = <|-∩-comm a′ (lem2 V-down U-down (lem1 V-down h q) p)
    lem3 a a′ h (branch b f)     q = branch b g
      where
        g : (c : out b) → rev c <| (U ∩ V)
        g c = lem3 a′ (rev c) (mono a′ b c) (f c) (lem1 V-down h q)
```
