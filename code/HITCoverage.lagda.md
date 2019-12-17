```
{-# OPTIONS --cubical #-}

module HITCoverage where

open import Level
open import Agda.Primitive.Cubical
open import Agda.Builtin.Cubical.Path
open import Data.Empty   using (⊥) renaming (⊥-elim to explode)
open import Data.Product using (Σ; _,_; _×_) renaming (proj₁ to π₀; proj₂ to π₁)

Type₀  = Set zero

Type : (ℓ : Level) → Set (suc ℓ)
Type ℓ = Set ℓ
```

```
variable
  ℓ ℓ′ ℓ₀ ℓ₁ ℓ₂ : Level
  A B P         : Type ℓ

IsProposition : Type ℓ → Type ℓ
IsProposition A = (a b : A) → a ≡ b
```

Here goes the test:

```
module Test (P     : Type ℓ)
            (_⊑_   : P → P → Type ℓ′)
            (refl  : (a        : P) → a ⊑ a)
            (trans : (a₀ a₁ a₂ : P) → a₀ ⊑ a₁ → a₁ ⊑ a₂ → a₀ ⊑ a₂)
            (exp   : P → Type ℓ)
            (out   : (a : P) → exp a → Type ℓ)
            (rev   : (a : P) → (b : exp a) → out a b → P)
            (mono  : (a : P) → (b : exp a) → (c : out a b) → rev a b c ⊑ a)
            (sim   : (a₀ a : P)
                   → a₀ ⊑ a
                   → (b : exp a)
                   → Σ (exp a₀) (λ b₀ → (c₀ : out a₀ b₀) → Σ (out a b) (λ c → (rev a₀ b₀ c₀) ⊑ (rev a b c))))
            where

  IsDownwardClosed : (P → Type ℓ₀) → Type (ℓ ⊔ ℓ′ ⊔ ℓ₀)
  IsDownwardClosed U = (a₀ a : P) → U a → a₀ ⊑ a → U a₀

  data _<|_ (a : P) (U : P → Type ℓ₀) : Type (ℓ ⊔ suc ℓ₀) where
    dir    : U a → a <| U
    branch : (b : exp a) → (f : (c : out a b) → rev a b c <| U) → a <| U
    squash : (p₀ p₁ : a <| U) → p₀ ≡ p₁

  <|-prop : (a : P) (U : P → Type ℓ′) → IsProposition (a <| U)
  <|-prop a U = squash
```

```
  _∩_ : (P → Type ℓ₀) → (P → Type ℓ₁) → P → Type (ℓ₀ ⊔ ℓ₁)
  U ∩ V = λ x → U x × V x

  lem1 : (a a′ : P)
       → (U : P → Type ℓ₀) → (V : P → Type ℓ₁)
       → (U-down : IsDownwardClosed U) → (V-down : IsDownwardClosed V)
       → a′ ⊑ a →  a <| U → a′ <| U
  lem1 a a′ U V U-down V-down h (dir q)      = dir (U-down a′ a q h)
  lem1 a a′ U V U-down V-down h (branch b f) = branch b′ g
    where
      b′ : exp a′
      b′ = π₀ (sim a′ a h b)

      g : (c′ : out a′ b′) → rev a′ b′ c′ <| U
      g c′ = lem1 (rev a b c) (rev a′ b′ c′) U V U-down V-down (π₁ (π₁ (sim a′ a h b) c′)) (f c)
        where
          c : out a b
          c = π₀ (π₁ (sim a′ a h b) c′)
  lem1 a a′ U V U-down V-down h (squash p₀ p₁ i) = squash (lem1 a a′ U V U-down V-down h p₀) (lem1 a a′ U V U-down V-down h p₁) i
```

```
  lem2 : (a : P) → (U : P → Type ℓ₀) → (V : P → Type ℓ₁)
       → IsDownwardClosed U → IsDownwardClosed V → a <| U → V a → a <| (U ∩ V)
  lem2 a U V U-down V-down (dir q) h       = dir (q , h)
  lem2 a U V U-down V-down (branch b f) h  = branch b g
    where
      g : (c : out a b) → rev a b c <| (U ∩ V)
      g c = lem2 (rev a b c) U V U-down V-down (f c) (V-down (rev a b c) a h (mono a b c))
  lem2 a U V U-down V-down (squash p₀ p₁ i) h = squash (lem2 a U V U-down V-down p₀ h) (lem2 a U V U-down V-down p₁ h) i
```

```
  lem3 : (a a′ : P) (U V : P → Type ℓ₀)
       → IsDownwardClosed U
       → IsDownwardClosed V
       → a′ ⊑ a → a′ <| U → a <| V → a′ <| (V ∩ U)
  lem3 a a′ U V U-down V-down h (dir p) q          = lem2 a′ V U V-down U-down (lem1 a a′ V U V-down U-down h q) p
  lem3 a a′ U V U-down V-down h (branch b f) q     = branch b g
    where
      g : (c : out a′ b) → rev a′ b c <| (V ∩ U)
      g c = lem3 a′ (rev a′ b c) U V U-down V-down (mono a′ b c) (f c) (lem1 a a′ V U V-down U-down h q)
  lem3 a a′ U V U-down V-down h (squash p₀ p₁ i) q =
    squash (lem3 a a′ U V U-down V-down h p₀ q) (lem3 a a′ U V U-down V-down h p₁ q) i
```

```
  lem4 : (a : P) (U : P → Type ℓ₀) (V : P → Type ℓ₁)
       → a <| U → ((u : P) → U u → u <| V) → a <| V
  lem4 a U V (dir p)          h = h a p
  lem4 a U V (branch b f)     h = branch b (λ c → lem4 (rev a b c) U V (f c) h)
  lem4 a U V (squash p₀ p₁ i) h = squash (lem4 a U V p₀ h) (lem4 a U V p₁ h) i
```
