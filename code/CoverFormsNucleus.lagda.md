```
{-# OPTIONS --cubical --safe #-}

open import Basis
open import Poset        hiding (IsDownwardClosed)
open import Frame        hiding (pos)
open import HITCoverage  hiding (Type)
open import Nucleus      using  (IsNuclear)
open import Powerset
open import TreeType

module CoverFormsNucleus (D : Discipline ℓ₀ ℓ₁) (D-sim : IsSimulation D) where

  pos-D  = strₚ (pos D)
  ⊑-refl = PosetStr.⊑-refl pos-D

```

Let us start by defining the frame formed by the downward-closed subsets of `P`.

```
  F↓      = downward-subset-frame (TreeType.pos D)
  stage-D = TreeType.stage   D
  exp-D   = TreeType.exp     D
  out-D   = TreeType.outcome D
  rev-D   = TreeType.revise  D
  mono-D  = π₁ D
  _⊑_     = λ (x y : stage-D) → x ⊑[ pos D ] y is-true

  open Frame.Frame F↓ using (_⊓_) renaming (_⊑_ to _◀_)
  open PosetStr (strₚ (Frame.P F↓)) using () renaming (⊑-antisym to ◀-antisym)

  sim : (a₀ a : stage-D)
      → a₀ ⊑ a → (b : exp-D a)
      → Σ (exp-D a₀) (λ b₀ → (c₀ : out-D b₀) → Σ (out-D b) (λ c → rev-D c₀ ⊑ rev-D c))
  sim a₀ a a₀⊑a b = b₀ , NTS
    where
      b₀ : exp-D a₀
      b₀ = π₀ (D-sim a a₀ a₀⊑a b)

      NTS : (c₀ : out-D (π₀ (D-sim a a₀ a₀⊑a b))) → Σ (out-D b) (λ c → rev-D c₀ ⊑ rev-D c)
      NTS c₀ = π₁ (D-sim a a₀ a₀⊑a b) (rev-D c₀) (c₀ , ⊑-refl (rev-D c₀))
```

```
  open Test stage-D _⊑_ exp-D out-D rev-D (π₁ mono-D) sim

  cover : ∣ F↓ ∣F → ∣ F↓ ∣F
  cover (U′ , U′-down) = U₀ , downward-closed
    where
      U₀ : stage-D → Ω ℓ₀
      U₀ = λ a → (a <| (_is-true ∘ U′)) , <|-prop a (_is-true ∘ U′)

      U₁ : stage-D → Type ℓ₀
      U₁ a = a <| (_is-true ∘ U′)

      U₁-down : IsDownwardClosed U₁
      U₁-down {a₀ = a₀} {a} aεU₁ a₀⊑a = lem1 (λ {a₀} {a} → U′-down a a₀) a₀⊑a aεU₁

      downward-closed : (a₀ a₁ : stage-D)
                      → U₀ a₀ is-true → a₁ ⊑[ pos D ] a₀ is-true → U₀ a₁ is-true
      downward-closed a₀ a₁ a₀εU₀ a₁⊑a₀ = U₁-down a₀εU₀ a₁⊑a₀

  cover-nuclear : IsNuclear F↓ cover
  cover-nuclear = N₀ , N₁ , N₂
    where
      N₀ : (a₀ a₁ : ∣ F↓ ∣F) → cover (a₀ ⊓ a₁) ≡ (cover a₀) ⊓ (cover a₁)
      N₀ 𝕌@(U , U-down) 𝕍@(V , V-down) = ◀-antisym (cover (𝕌 ⊓ 𝕍)) (cover 𝕌 ⊓ cover 𝕍) d u
        where
          U-down′ : IsDownwardClosed (_is-true ∘ U)
          U-down′ = U-down _ _

          V-down′ : IsDownwardClosed (_is-true ∘ V)
          V-down′ = V-down _ _

          d : (a : stage-D) → π₀ (cover (𝕌 ⊓ 𝕍)) a is-true → π₀ (cover 𝕌 ⊓ cover 𝕍) a is-true
          d a (dir p)        = dir (π₀ p) , dir (π₁ p)
          d a (branch b f)   =
            branch b (λ c → π₀ (d (rev-D c) (f c))) , branch b λ c → π₁ (d (rev-D c) (f c))
          d a (squash p q i) =
            squash (π₀ (d a p)) (π₀ (d a q)) i , squash (π₁ (d a p)) (π₁ (d a q)) i

          u : (a : stage-D) → π₀ (cover 𝕌 ⊓ cover 𝕍) a is-true → π₀ (cover (𝕌 ⊓ 𝕍)) a is-true
          u a p = lem3 (_is-true ∘ U) (_is-true ∘ V) U-down′ V-down′ a a (⊑-refl a) (π₀ p) (π₁ p)

      N₁ : (𝕌 : ∣ F↓ ∣F) → 𝕌 ◀ (cover 𝕌) is-true
      N₁ 𝕌@(U , U-down) a₀ p = lem1 (U-down _ _) {a = a₀} (⊑-refl a₀) (dir p)

      N₂ : (a : ∣ F↓ ∣F) → cover (cover a) ◀ (cover a) is-true
      N₂ 𝕌@(U , U-down) a′ p =
        lem4 a′ (λ a → π₀ (cover 𝕌) a is-true) (_is-true ∘ U) p (λ _ q → q)
```
