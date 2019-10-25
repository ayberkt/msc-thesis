```
{-# OPTIONS --without-K #-}

module Coverage where

open import Variables
open import Common
open import Family
open import Homotopy
open import Poset
```

```
Covering : (ℓ : Level) → (P : Poset ℓ₀ ℓ₁) → ∣ P ∣ₚ → Set (ℓ₀ ⊔ ℓ₁ ⊔ suc ℓ)
Covering ℓ P a = Sub ℓ (↓[ P ] a)
```

Note that the level for the index set of the family is required to be explicitly provided.

```
Coverage : (ℓ : Level) → Poset ℓ₀ ℓ₁ → Set (ℓ₀ ⊔ ℓ₁ ⊔ suc ℓ)
Coverage ℓ P = (a : ∣ P ∣ₚ) → Sub ℓ (Covering ℓ P a)
```

A site is simply a poset equipped with a coverage.

```
Site : (ℓ₀ ℓ₁ ℓ₂ : Level) → Set (suc ℓ₀ ⊔ suc ℓ₁ ⊔ suc ℓ₂)
Site ℓ₀ ℓ₁ ℓ₂ = Σ[ P ∈ (Poset ℓ₀ ℓ₁) ] Coverage ℓ₂ P
```

The locality condition (à la Dragalin).

```
IsLocal : (S : Site ℓ₀ ℓ₁ ℓ₂) → Set (ℓ₀ ⊔ ℓ₁ ⊔ suc ℓ₂)
IsLocal {ℓ₂ = ℓ₂} (P , Cov) =
  (a b : ∣ P ∣ₚ) → b ⊑[ P ] a holds →
    (S : Covering ℓ₂ P a) → S ε Cov a →
      Σ[ T ∈ Covering ℓ₂ P b ] (T ε Cov b →
        (t : ↓[ P ] b) → t ε T →
          Σ[ s ∈ ↓[ P ] a ] (s ε S → (proj₁ t) ⊑[ P ] (proj₁ s) holds))
```
