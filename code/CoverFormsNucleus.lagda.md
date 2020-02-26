```
{-# OPTIONS --cubical --safe #-}

module CoverFormsNucleus where

open import Basis        hiding (A)
open import Poset        renaming (IsDownwardClosed to IsDownwardClosed′)
open import Frame
open import HITCoverage  hiding (Type)
open import Nucleus      using  (IsNuclear; Nucleus; nuclear-fixed-point-frame)
open import Powerset
open import TreeType     renaming (pos to pos′)

module _ (F : FormalTopology ℓ₀ ℓ₁) where

  private
    D       = π₀ F
    D-sim   = π₁ F
    P       = pos′ (π₀ F)
    ⊑-refl  = ⊑[ P ]-refl
    F↓      = downward-subset-frame (TreeType.pos D)
    stage-D = TreeType.stage   D
    exp-D   = TreeType.exp     D
    out-D   = TreeType.outcome D
    rev-D   = TreeType.revise  D
    mono-D  = π₁ D
    _⊑_     = λ (x y : stage-D) → x ⊑[ P ] y is-true

  sim : (a₀ a : stage-D)
      → a₀ ⊑ a → (b : exp-D a)
      → Σ (exp-D a₀) (λ b₀ → (c₀ : out-D b₀) → Σ (out-D b) (λ c → rev-D c₀ ⊑ rev-D c))
  sim a₀ a a₀⊑a b =
    b₀ , λ c₀ → π₁ (D-sim a a₀ a₀⊑a b) (rev-D c₀) (c₀ , ⊑-refl (rev-D c₀))
    where
      b₀ : exp-D a₀
      b₀ = π₀ (D-sim a a₀ a₀⊑a b)


  open Test stage-D _⊑_ exp-D out-D rev-D (π₁ mono-D) sim

  𝕛 : ∣ F↓ ∣F → ∣ F↓ ∣F
  𝕛 (U , U-down) = U₀ , λ _ _ → down-closed
    where
      -- This is not  h-propositional unless we force it to be using the HIT definition.
      U₀ : stage-D → Ω ℓ₀
      U₀ = λ a → a <| (_is-true ∘ U) , <|-prop a (_is-true ∘ U)

      down-closed : IsDownwardClosed (λ - → - <| (_is-true ∘ U))
      down-closed aεU₁ a₀⊑a = lem1 (U-down _ _) a₀⊑a aεU₁

  _<<_ : ∣ F↓ ∣F → ∣ F↓ ∣F → hProp ℓ₀
  x << y = x ⊑[ pos F↓ ] y

  ◀-antisym = ⊑[ pos F↓ ]-antisym

  𝕛-nuclear : IsNuclear F↓ 𝕛
  𝕛-nuclear = N₀ , N₁ , N₂
    where
      -- We reason by antisymmetry and prove in (d) 𝕛 (a₀ ⊓ a₁) ⊑ (𝕛 a₀) ⊓ (𝕛 a₁) and
      -- in (u) (𝕛 a₀) ⊓ (𝕛 a₁) ⊑ 𝕛 (a₀ ⊓ a₁).
      N₀ : (a₀ a₁ : ∣ F↓ ∣F) → 𝕛 (a₀ ⊓[ F↓ ] a₁) ≡ (𝕛 a₀) ⊓[ F↓ ] (𝕛 a₁)
      N₀ 𝕌@(U , U-down) 𝕍@(V , V-down) =
        ◀-antisym (𝕛 (𝕌 ⊓[ F↓ ] 𝕍)) (𝕛 𝕌 ⊓[ F↓ ] 𝕛 𝕍) d u
        where
          U′ = _is-true ∘ U
          V′ = _is-true ∘ V

          U-down′ : IsDownwardClosed (_is-true ∘ U)
          U-down′ = U-down _ _

          V-down′ : IsDownwardClosed (_is-true ∘ V)
          V-down′ = V-down _ _

          d : 𝕛 (𝕌 ⊓[ F↓ ] 𝕍) << (𝕛 𝕌 ⊓[ F↓ ] 𝕛 𝕍) is-true
          d a (dir p)        = dir (π₀ p) , dir (π₁ p)
          d a (branch b f)   = branch b (π₀ ∘ IH) , branch b (π₁ ∘ IH)
            where
              IH : (c : out-D b) → π₀ (𝕛 𝕌 ⊓[ F↓ ] 𝕛 𝕍) (rev-D c) is-true
              IH c = d (rev-D c) (f c)
          d a (squash p q i) = squash (π₀ IH₀) (π₀ IH₁) i , squash (π₁ IH₀) (π₁ IH₁) i
            where
              IH₀ = d a p
              IH₁ = d a q

          u : (𝕛 𝕌 ⊓[ F↓ ] 𝕛 𝕍) << 𝕛 (𝕌 ⊓[ F↓ ] 𝕍) is-true
          u a p = lem3 U′ V′ U-down′ V-down′ a a (⊑-refl a) (π₀ p) (π₁ p)

      N₁ : (𝕌 : ∣ F↓ ∣F) → 𝕌 << (𝕛 𝕌) is-true
      N₁ 𝕌@(U , U-down) a₀ p = lem1 (U-down _ _) (⊑-refl a₀) (dir p)

      N₂ : (a : ∣ F↓ ∣F) → 𝕛 (𝕛 a) << (𝕛 a) is-true
      N₂ 𝕌@(U , U-down) a′ p = lem4 a′ (λ a → π₀ (𝕛 𝕌) a is-true) U′ p (λ _ q → q)
        where
          U′ = _is-true ∘ U

  gen : Frame (suc ℓ₀ ⊔ ℓ₁) ℓ₀ ℓ₀
  gen = nuclear-fixed-point-frame F↓ (𝕛 , 𝕛-nuclear)

{--
down-closure : (F : FormalTopology ℓ ℓ) → stage (π₀ F) → ∣ gen F ∣F
down-closure F x = x↓ , fixed
  where
    pos-F  = pos′ (π₀ F)
    A      = ∣ pos-F ∣ₚ
    _⊑_    = λ (x y : A) → x ⊑[ pos-F ] y is-true
    exp-A  = exp (π₀ F)
    out-A  = outcome (π₀ F)
    rev-A  = revise (π₀ F)
    D-sim  = π₁ F
    F↓     = downward-subset-frame pos-F

    IsBelow-x   = λ y → y ⊑[ pos-F ] x

    down-DC : IsDownwardClosed′ pos-F IsBelow-x is-true
    down-DC z y z⊑x y⊑z = ⊑[ pos-F ]-trans y z x y⊑z z⊑x

    x↓ = IsBelow-x , down-DC

    fixed : 𝕛 F x↓ ≡ x↓
    fixed = ⊑[ pos F↓ ]-antisym _ _ below above
      where
        below : 𝕛 F x↓ ⊑[ pos F↓ ] x↓ is-true
        below y (Test.dir x)               = x
        below y (Test.branch b f)          = {!!}
        below y (Test.squash yε𝕛D yε𝕛D₁ i) = {!!}

        above : x↓ ⊑[ pos F↓ ] 𝕛 F x↓ is-true
        above = π₀ (π₁ (𝕛-nuclear F)) x↓

down-closure-m : (F : FormalTopology ℓ ℓ) → (pos′ (π₀ F)) ─m→ pos (gen F)
down-closure-m F = down-closure F , is-mono
  where
    is-mono : IsMonotonic (pos′ (π₀ F)) (pos (gen F)) (down-closure F)
    is-mono x y x⊑y z z⊑x = ⊑[ pos′ (π₀ F) ]-trans z x y z⊑x x⊑y
--}

represents : (F : FormalTopology ℓ ℓ) (L : Frame (suc ℓ) ℓ ℓ)
           → (m : pos′ (π₀ F) ─m→ pos L)
           → Type ℓ
represents F L m =
  (x : A) (y : exp (π₀ F) x) →
    (m $ₘ x) ⊑[ pos L ] (⋃[ L ] (outcome (π₀ F) y , λ u → m $ₘ (revise (π₀ F) u))) is-true
  where
    A = ∣ pos′ (π₀ F) ∣ₚ

-- ↓-represents : (F : FormalTopology ℓ ℓ) → represents F (gen F) (down-closure-m F)
-- ↓-represents = {!!}

-- universal : (F : FormalTopology ℓ ℓ) (L : Frame (suc ℓ) ℓ ℓ)
          -- → (f : pos′ (π₀ F) ─m→ pos L)
          -- → represents F L f
          -- → Σ[ m ∈ (pos′ (π₀ F) ─m→ pos L) ] (m ∘m (down-closure-m F)) ≡ f
-- universal = {!!}

-- Universal property: Given a formal topology A and a function from f_A : A → free(A), for any function
-- f : A → L, where L is any frame, there exists an m : free(A) → L, that makes the diagram commute and is
-- unique: Σ![m ∈ free(A) → L ] m ∘ f_A = f.

-- We don't need an extra condition on the elements of A because
```

```
```
