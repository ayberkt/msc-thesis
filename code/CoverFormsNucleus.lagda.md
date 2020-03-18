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
```

We use an anonymous module that takes some formal topology `F` as a parameter to reduce
parameter-passing.

```
module _ (F : FormalTopology ℓ₀ ℓ₀) where
```

We refer to the underlying poset of `F` as `P` and the frame of downwards-closed subsets
of `P` as `F↓`. `sim` and `mono` refer to the simulation and monotonicity properties of
`F`.

```
  private
    D       = π₀ F
    P       = pos′ (π₀ F)
    F↓      = downward-subset-frame P
    P↓      = pos F↓
    sim     = π₁ F
    mono    = π₁ D
    _⊑_     = λ (x y : stage D) → x ⊑[ P ] y is-true

  open Test (stage D) _⊑_ (exp D) (outcome D) (next D) (π₁ mono) sim
```

Now, we define the *covering nucleus* which we denote by `𝕛`. At its heart, this is
nothing but the map `U ↦ - <| U`.

```
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
          u a p = lem3 U′ V′ U-down′ V-down′ a a (⊑[ P ]-refl a) (π₀ p) (π₁ p)

      N₁ : (𝕌 : ∣ F↓ ∣F) → 𝕌 << (𝕛 𝕌) is-true
      N₁ 𝕌@(U , U-down) a₀ p = lem1 (U-down _ _) (⊑[ P ]-refl a₀) (dir p)

      N₂ : (a : ∣ F↓ ∣F) → 𝕛 (𝕛 a) << (𝕛 a) is-true
      N₂ 𝕌@(U , U-down) a′ p = lem4 a′ (λ a → π₀ (𝕛 𝕌) a is-true) U′ p (λ _ q → q)
        where
          U′ = _is-true ∘ U
```

We denote by `L` the frame of fixed points for `𝕛`.

```
  L : Frame (suc ℓ₀) ℓ₀ ℓ₀
  L = nuclear-fixed-point-frame F↓ (𝕛 , 𝕛-nuclear)
```

Given some `x` in `F`, we define a map taking `x` to its *downwards-closure*.

```
  ↓-clos : stage D → ∣ F↓ ∣F
  ↓-clos x = x↓ , down-DC
    where
      x↓ = λ y → y ⊑[ P ] x
      down-DC : IsDownwardClosed′ P x↓ is-true
      down-DC z y z⊑x y⊑z = ⊑[ P ]-trans y z x y⊑z z⊑x
```

By composing this with the covering nucleus, we define a map `e` from `F` to `F↓`.

```
  e : stage D → ∣ F↓ ∣F
  e z = (λ a → (a <| (_is-true ∘ (π₀ (↓-clos z)))) , squash) , NTS
    where
      NTS : IsDownwardClosed′ (π₀ (pos′ D) , π₁ (pos′ D)) (λ a → (a <| (λ - → π₀ (↓-clos z) - is-true)) , squash) is-true
      NTS x y p q = lem1 (λ p q → ⊑[ P ]-trans _ _ z q p) q p
```

We can further refine the codomain of `e` to `L`. In other words, we can prove that `j (e
x) = e x` for every `x`. We call the version `e` with the refined codomain `η`.

```
  fixing : (x : stage D) → 𝕛 (e x) ≡ e x
  fixing x = ⊑[ P↓ ]-antisym (𝕛 (e x)) (e x) NTS up
    where
      NTS : ∀ y → π₀ (𝕛 (e x)) y is-true → π₀ (e x) y is-true
      NTS y (dir p)        = p
      NTS y (branch b f)   = branch b (λ c → NTS (next D c) (f c))
      NTS y (squash p q i) = squash (NTS y p) (NTS y q) i
      up : e x ⊑[ P↓ ] 𝕛 (e x) is-true
      up = π₀ (π₁ 𝕛-nuclear) (e x)

  η : stage (π₀ F) → ∣ L ∣F
  η x = (e x) , (fixing x)
```

Furthermore, `η` is a monotonic map.

```
  ηm : P ─m→ pos L
  ηm = η , η-mono
    where
      open PosetReasoning (pos L) using (_⊑⟨_⟩_; _■)
      η-mono : IsMonotonic P (pos L) η
      η-mono x y x⊑y = lemma
        where
          NTS : IsDownwardClosed′ (π₀ P , π₁ P) (λ a → (a <| (λ x₁ → π₀ (↓-clos x) x₁ is-true)) , squash) is-true
          NTS x′ y′ p q = lem1 (λ p′ q′ → ⊑[ P ]-trans _ _ x q′ p′) q p
          NTS′ : IsDownwardClosed′ (π₀ P , π₁ P) (λ a → (a <| (λ x₁ → π₀ (↓-clos y) x₁ is-true)) , squash) is-true
          NTS′ x′ y′ p q = lem1 (λ p′ q′ → ⊑[ P ]-trans _ _ y q′ p′) q p
          lemma : (((λ a → (a <| (_is-true ∘ (π₀ (↓-clos x)))) , squash) , NTS)  , (fixing x)) ⊑[ pos L ] (((λ a → (a <| (_is-true ∘ (π₀ (↓-clos y)))) , squash) , NTS′) , (fixing y)) is-true
          lemma a (dir p) = dir (⊑[ P ]-trans a x y p x⊑y)
          lemma a (branch b f) = branch b IH
            where
              IH : (c : outcome D b) → next D c <| (_is-true ∘ π₀ (↓-clos y))
              IH c = lemma (next D c) (f c)
          lemma a (squash p q i) = squash (lemma a p) (lemma a q) i
          foo : η x ≡ ((e x) , (fixing x))
          foo = refl
```

```
↓-clos-mono : (F : FormalTopology ℓ ℓ)
            → (pos′ (π₀ F)) ─m→ (pos (downward-subset-frame (pos′ (π₀ F))))
↓-clos-mono F = ↓-clos F , NTS
  where
    NTS : IsMonotonic (pos′ (π₀ F)) (pos (downward-subset-frame (pos′ (π₀ F)))) (↓-clos F)
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
