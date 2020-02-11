```
{-# OPTIONS --cubical --safe #-}

open import Basis
open import Poset        hiding (IsDownwardClosed)
open import Frame
open import HITCoverage  hiding (Type)
open import Nucleus      using  (IsNuclear; Nucleus; nuclear-fixed-point-frame)
open import Powerset
open import TreeType     hiding (pos)

module CoverFormsNucleus (D : Discipline ℓ₀ ℓ₁) (D-sim : IsSimulation D) where

  pos-D  = π₀ D
  ⊑-refl = ⊑[ pos-D ]-refl

```

Let us start by defining the frame formed by the downward-closed subsets of `P`.

```
  F↓      = downward-subset-frame (TreeType.pos D)
  stage-D = TreeType.stage   D
  exp-D   = TreeType.exp     D
  out-D   = TreeType.outcome D
  rev-D   = TreeType.revise  D
  mono-D  = π₁ D
  _⊑_     = λ (x y : stage-D) → x ⊑[ pos-D ] y is-true

  -- open Frame.Frame F↓ using (_⊓_) renaming (_⊑_ to _<<_)

  _⊓_ : ∣ F↓ ∣F → ∣ F↓ ∣F → ∣ F↓ ∣F
  x ⊓ y = x ⊓[ F↓ ] y

  _<<_ : ∣ F↓ ∣F → ∣ F↓ ∣F → hProp ℓ₀
  x << y = x ⊑[ pos F↓ ] y

  ◀-antisym = ⊑[ pos F↓ ]-antisym

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

## The nucleus

```
  open Test stage-D _⊑_ exp-D out-D rev-D (π₁ mono-D) sim

  𝕛 : ∣ F↓ ∣F → ∣ F↓ ∣F
  𝕛 (U , U-down) = U₀ , λ _ _ → down-closed
    where
      U′ = _is-true ∘ U

      -- This is not  h-propositional unless we force it to be using the HIT definition.
      U₀ : stage-D → Ω ℓ₀
      U₀ = λ a → a <| U′ , <|-prop a U′

      down-closed : IsDownwardClosed (λ - → - <| U′)
      down-closed aεU₁ a₀⊑a = lem1 (U-down _ _) a₀⊑a aεU₁

  𝕛-nuclear : IsNuclear F↓ 𝕛
  𝕛-nuclear = N₀ , N₁ , N₂
    where
      -- We reason by antisymmetry and prove in (d) 𝕛 (a₀ ⊓ a₁) ⊑ (𝕛 a₀) ⊓ (𝕛 a₁) and
      -- in (u) (𝕛 a₀) ⊓ (𝕛 a₁) ⊑ 𝕛 (a₀ ⊓ a₁).
      N₀ : (a₀ a₁ : ∣ F↓ ∣F) → 𝕛 (a₀ ⊓ a₁) ≡ (𝕛 a₀) ⊓ (𝕛 a₁)
      N₀ 𝕌@(U , U-down) 𝕍@(V , V-down) = ◀-antisym (𝕛 (𝕌 ⊓ 𝕍)) (𝕛 𝕌 ⊓ 𝕛 𝕍) d u
        where
          U′ = _is-true ∘ U
          V′ = _is-true ∘ V

          U-down′ : IsDownwardClosed (_is-true ∘ U)
          U-down′ = U-down _ _

          V-down′ : IsDownwardClosed (_is-true ∘ V)
          V-down′ = V-down _ _

          d : 𝕛 (𝕌 ⊓ 𝕍) << (𝕛 𝕌 ⊓ 𝕛 𝕍) is-true
          d a (dir p)        = dir (π₀ p) , dir (π₁ p)
          d a (branch b f)   = branch b (π₀ ∘ IH) , branch b (π₁ ∘ IH)
            where
              IH : (c : out-D b) → π₀ (𝕛 𝕌 ⊓ 𝕛 𝕍) (rev-D c) is-true
              IH c = d (rev-D c) (f c)
          d a (squash p q i) = squash (π₀ IH₀) (π₀ IH₁) i , squash (π₁ IH₀) (π₁ IH₁) i
            where
              IH₀ = d a p
              IH₁ = d a q

          u : (𝕛 𝕌 ⊓ 𝕛 𝕍) << 𝕛 (𝕌 ⊓ 𝕍) is-true
          u a p = lem3 U′ V′ U-down′ V-down′ a a (⊑-refl a) (π₀ p) (π₁ p)

      N₁ : (𝕌 : ∣ F↓ ∣F) → 𝕌 << (𝕛 𝕌) is-true
      N₁ 𝕌@(U , U-down) a₀ p = lem1 (U-down _ _) (⊑-refl a₀) (dir p)

      N₂ : (a : ∣ F↓ ∣F) → 𝕛 (𝕛 a) << (𝕛 a) is-true
      N₂ 𝕌@(U , U-down) a′ p = lem4 a′ (λ a → π₀ (𝕛 𝕌) a is-true) U′ p (λ _ q → q)
        where
          U′ = _is-true ∘ U
```

```
  NN : Nucleus F↓
  NN = 𝕛 , 𝕛-nuclear
```

## The frame of fixed points

```
  fixed-point-frame : Frame (suc ℓ₀ ⊔ ℓ₁) ℓ₀ ℓ₀
  fixed-point-frame = nuclear-fixed-point-frame F↓ NN
```
