```
{-# OPTIONS --cubical --safe #-}

module CoverFormsNucleus where

open import Basis          hiding (A)
open import Poset          renaming (IsDownwardClosed to IsDownwardClosed′)
open import Frame
open import HITCoverage    hiding (Type)
open import Nucleus        using  (IsNuclear; Nucleus; nuclear-fixed-point-frame)
open import Powerset
open import FormalTopology renaming (pos to pos′)

module _ (F : FormalTopology ℓ₀ ℓ₀) where

  private
    D       = π₀ F
    D-sim   = π₁ F
    P       = pos′ (π₀ F)
    ⊑-refl  = ⊑[ P ]-refl
    F↓      = downward-subset-frame (pos′ D)
    mono-D  = π₁ D
    _⊑_     = λ (x y : stage D) → x ⊑[ P ] y is-true

  open Test (stage D) _⊑_ (exp D) (outcome D) (next D) (π₁ mono-D) D-sim

  𝕛 : ∣ F↓ ∣F → ∣ F↓ ∣F
  𝕛 (U , U-down) = U₀ , λ _ _ → down-closed
    where
      -- This is not  h-propositional unless we force it to be using the HIT definition.
      U₀ : stage D → hProp ℓ₀
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
              IH : (c : outcome D b) → π₀ (𝕛 𝕌 ⊓[ F↓ ] 𝕛 𝕍) (next D c) is-true
              IH c = d (next D c) (f c)
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

  gen : Frame (suc ℓ₀) ℓ₀ ℓ₀
  gen = nuclear-fixed-point-frame F↓ (𝕛 , 𝕛-nuclear)

  down-closure : stage (π₀ F) → ∣ F↓ ∣F
  down-closure x = x↓ , down-DC
    where
      x↓ = λ y → y ⊑[ P ] x
      down-DC : IsDownwardClosed′ P x↓ is-true
      down-DC z y z⊑x y⊑z = ⊑[ P ]-trans y z x y⊑z z⊑x

      -- fixed : 𝕛 x↓ ≡ x↓
      -- fixed =  ⊑[ pos F↓ ]-antisym _ _ below above
        -- where
          -- NTS : ∀ y → y <| (_is-true ∘ IsBelow-x) → y ⊑[ P ] x is-true
          -- NTS y (dir p) = p
          -- NTS y (branch b f) = {!!}
            -- where
              -- IH : (c : out-D b) → (rev-D c) ⊑[ P ] x is-true
              -- IH c = NTS (rev-D c) (f c)
          -- NTS y (squash p q i) = {!!}
          -- below : 𝕛 x↓ ⊑[ pos F↓ ] x↓ is-true
          -- below = NTS
          -- above : x↓ ⊑[ pos F↓ ] 𝕛 x↓ is-true
          -- above = π₀ (π₁ 𝕛-nuclear) x↓

  η : stage (π₀ F) → ∣ F↓ ∣F
  η z = (λ a → (a <| (_is-true ∘ (π₀ (down-closure z)))) , squash) , NTS
    where
      NTS : IsDownwardClosed′ (π₀ (pos′ D) , π₁ (pos′ D)) (λ a → (a <| (λ - → π₀ (down-closure z) - is-true)) , squash) is-true
      NTS x y p q = lem1 rem q p
        where
          rem : IsDownwardClosed (λ - → - ⊑[ P ] z is-true)
          rem p q =  ⊑[ P ]-trans _ _ z q p

  compose′ : stage (π₀ F) → ∣ gen ∣F
  compose′ x = (η x) , fixing
    where
      P↓ = pos (downward-subset-frame (pos′ (π₀ F)))
      NTS : ∀ y → π₀ (𝕛 (η x)) y is-true → π₀ (η x) y is-true
      NTS y (dir p) = p
      NTS y (branch b f) = branch b (λ c → NTS (next D c) (f c))
      NTS y (squash p q i) = squash (NTS y p) (NTS y q) i
      up : η x ⊑[ P↓ ] 𝕛 (η x) is-true
      up = π₀ (π₁ 𝕛-nuclear) (η x)
      fixing : 𝕛 (η x) ≡ η x
      fixing = ⊑[ P↓ ]-antisym (𝕛 (η x)) (η x) NTS up

down-closure-m : (F : FormalTopology ℓ ℓ)
               → (pos′ (π₀ F)) ─m→ (pos (downward-subset-frame (pos′ (π₀ F))))
down-closure-m F = down-closure F , NTS
  where
    NTS : IsMonotonic (pos′ (π₀ F)) (pos (downward-subset-frame (pos′ (π₀ F)))) (down-closure F)
    NTS x y x⊑y z z⊑x = ⊑[ pos′ (π₀ F) ]-trans z x y z⊑x x⊑y

represents : (F : FormalTopology ℓ ℓ) (L : Frame (suc ℓ) ℓ ℓ)
           → (m : pos′ (π₀ F) ─m→ pos L)
           → Type ℓ
represents F L m =
  (x : A) (y : exp (π₀ F) x) →
    (m $ₘ x) ⊑[ pos L ] (⋃[ L ] (outcome (π₀ F) y , λ u → m $ₘ (next (π₀ F) u))) is-true
  where
    A = ∣ pos′ (π₀ F) ∣ₚ

-- ↓-represents : (F : FormalTopology ℓ ℓ) → represents F (gen F) (down-closure-m F)
-- ↓-represents = {!!}

{--
universal : (F : FormalTopology ℓ ℓ) (L : Frame (suc ℓ) ℓ ℓ)
          → (f : pos′ (π₀ F) ─m→ pos L)
          → represents F L f
          →
            let
              P = pos′ (π₀ F)
              Q = pos (downward-subset-frame (pos′ (π₀ F)))
            in
              Σ[ m ∈ (Q ─m→ pos L) ] (_∘m_ {P = P} {Q = Q} {R = pos L} m (down-closure-m F)) ≡ f
universal = {!!}
--}
```
