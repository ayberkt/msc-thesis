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
            -- (refl  : (a        : P) → a ⊑ a)
            -- (trans : (a₀ a₁ a₂ : P) → a₀ ⊑ a₁ → a₁ ⊑ a₂ → a₀ ⊑ a₂)
            (exp   : P → Type ℓ)
            (out   : (a : P) → exp a → Type ℓ)
            (rev   : (a : P) → (b : exp a) → out a b → P)
            (mono  : {a : P} → (b : exp a) → (c : out a b) → rev a b c ⊑ a)
            (sim   : (a₀ a : P)
                   → a₀ ⊑ a
                   → (b : exp a)
                   → Σ (exp a₀) (λ b₀ → (c₀ : out a₀ b₀) → Σ (out a b) (λ c → (rev a₀ b₀ c₀) ⊑ (rev a b c))))
            where

  IsDownwardClosed : (P → Type ℓ₀) → Type (ℓ ⊔ ℓ′ ⊔ ℓ₀)
  IsDownwardClosed U = {a₀ a : P} → U a → a₀ ⊑ a → U a₀

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

  ∩-comm : (U : P → Type ℓ₀) → (V : P → Type ℓ₁)
         → (a : P) → ((V ∩ U) a → (U ∩ V) a) × ((U ∩ V) a → (V ∩ U) a)
  ∩-comm U V a =  V∩U⇒U∩V , U∩V⇒V∩U
    where
      V∩U⇒U∩V : (V ∩ U) a → (U ∩ V) a
      V∩U⇒U∩V (aεV , aεU) = aεU , aεV

      U∩V⇒V∩U : (U ∩ V) a → (V ∩ U) a
      U∩V⇒V∩U (aεU , aεV) = aεV , aεU

  <|-∩-comm : {U : P → Type ℓ₀} {V : P → Type ℓ₁}
            → (a : P) → a <| (V ∩ U) → a <| (U ∩ V)
  <|-∩-comm {U = U} {V} a (dir p)          = dir (π₀ (∩-comm U V a) p)
  <|-∩-comm {U = U} {V} a (branch b f)     = branch b (λ c → <|-∩-comm (rev a b c) (f c))
  <|-∩-comm {U = U} {V} a (squash p₀ p₁ i) = squash (<|-∩-comm a p₀) (<|-∩-comm a p₁) i

  module _ {U : P → Type ℓ₀} (U-down : IsDownwardClosed U) where

    lem1 : {a a′ : P} → a′ ⊑ a →  a <| U → a′ <| U
    lem1 {_}     {_}  h (squash p₀ p₁ i) = squash (lem1 h p₀) (lem1 h p₁) i
    lem1 {_}     {_}  h (dir q)          = dir (U-down q h)
    lem1 {a = a} {a′} h (branch b f)     = branch b′ g
      where
        b′ : exp a′
        b′ = π₀ (sim a′ a h b)

        g : (c′ : out a′ b′) → rev a′ b′ c′ <| U
        g c′ = lem1 (π₁ (π₁ (sim a′ a h b) c′)) (f c)
          where
            c : out a b
            c = π₀ (π₁ (sim a′ a h b) c′)

  lem4 : (a : P) (U : P → Type ℓ₀) (V : P → Type ℓ₁)
       → a <| U → ((u : P) → U u → u <| V) → a <| V
  lem4 a U V (squash p₀ p₁ i) h = squash (lem4 a U V p₀ h) (lem4 a U V p₁ h) i
  lem4 a U V (dir p)          h = h a p
  lem4 a U V (branch b f)     h = branch b (λ c → lem4 (rev a b c) U V (f c) h)

  module _ {U : P → Type ℓ₀} {V : P → Type ℓ₁}
           (U-down : IsDownwardClosed U) (V-down : IsDownwardClosed V) where
```

```
    lem2 : {a : P} → a <| U → V a → a <| (U ∩ V)
    lem2 (squash p₀ p₁ i) h = squash (lem2 p₀ h) (lem2 p₁ h) i
    lem2 (dir q)          h = dir (q , h)
    lem2 (branch b f)     h = branch b (λ c → lem2 (f c) (V-down h (mono b c)))

  module _ (U : P → Type ℓ₀) (V : P → Type ℓ₁)
           (U-down : IsDownwardClosed U) (V-down : IsDownwardClosed V) where

    lem3 : (a a′ : P) → a′ ⊑ a → a′ <| U → a <| V → a′ <| (U ∩ V)
    lem3 a a′ h (squash p₀ p₁ i) q = squash (lem3 a a′ h p₀ q) (lem3 a a′ h p₁ q) i
    lem3 a a′ h (dir p)          q = <|-∩-comm a′ (lem2 V-down U-down (lem1 V-down h q) p)
    lem3 a a′ h (branch b f)     q = branch b g
      where
        g : (c : out a′ b) → rev a′ b c <| (U ∩ V)
        g c = lem3 a′ (rev a′ b c) (mono b c) (f c) (lem1 V-down h q)
```

```
```
