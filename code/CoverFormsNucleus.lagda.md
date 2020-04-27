```
{-# OPTIONS --cubical --safe #-}

module CoverFormsNucleus where

open import Basis          hiding (A)
open import Poset
open import Frame
open import HITCoverage
open import Nucleus        using  (IsNuclear; Nucleus; nuclear-fixed-point-frame; idem)
open import Family         using  (Sub; _⟨$⟩_; _$_; _ε_; index)
open import Truncation     renaming (squash to squash′)
open import Data.Bool      using    (Bool; true; false)
open import Powerset
open import FormalTopology renaming (pos to pos′)
open import PowFamEquivalence
```

We use an anonymous module that takes some formal topology `F` as a parameter to reduce
parameter-passing.

```
module NucleusFrom (F : FormalTopology ℓ₀ ℓ₀) where
```

We refer to the underlying poset of `F` as `P` and the frame of downwards-closed subsets
of `P` as `F↓`. `sim` and `mono` refer to the simulation and monotonicity properties of
`F`.

```
  private
    D       = π₀ F
    P       = pos′ (π₀ F)
    𝔉       = ∣ P ∣ₚ
    F↓      = downward-subset-frame P
    P↓      = pos F↓
    sim     = π₁ F
    mono    = π₁ D
    _⊑_     = λ (x y : stage D) → x ⊑[ P ] y

  open Test F public
```

Now, we define the *covering nucleus* which we denote by `𝕛`. At its heart, this is
nothing but the map `U ↦ - <| U`.

```
  𝕛 : ∣ F↓ ∣F → ∣ F↓ ∣F
  𝕛 (U , U-down) = U₀ , U₀-dc
    where
      -- This is not  h-propositional unless we force it to be using the HIT definition.
      U₀ : stage D → hProp ℓ₀
      U₀ = λ a → a <| U , squash

      U₀-dc : IsDownwardClosed P (λ - → (- <| U) , squash) is-true
      U₀-dc a a₀ aεU₁ a₀⊑a = lem1 U-down a₀⊑a aεU₁

  _<<_ : ∣ F↓ ∣F → ∣ F↓ ∣F → hProp ℓ₀
  x << y = x ⊑[ pos F↓ ] y

  <<-antisym = ⊑[ pos F↓ ]-antisym

  𝕛-nuclear : IsNuclear F↓ 𝕛
  𝕛-nuclear = N₀ , N₁ , N₂
    where
      -- We reason by antisymmetry and prove in (d) 𝕛 (a₀ ⊓ a₁) ⊑ (𝕛 a₀) ⊓ (𝕛 a₁) and
      -- in (u) (𝕛 a₀) ⊓ (𝕛 a₁) ⊑ 𝕛 (a₀ ⊓ a₁).
      N₀ : (𝔘 𝔙 : ∣ F↓ ∣F) → 𝕛 (𝔘 ⊓[ F↓ ] 𝔙) ≡ (𝕛 𝔘) ⊓[ F↓ ] (𝕛 𝔙)
      N₀ 𝕌@(U , U-down) 𝕍@(V , V-down) =
        <<-antisym (𝕛 (𝕌 ⊓[ F↓ ] 𝕍)) (𝕛 𝕌 ⊓[ F↓ ] 𝕛 𝕍) d u
        where
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
          u a p = lem3 U V U-down V-down a a (⊑[ P ]-refl a) (π₀ p) (π₁ p)

      N₁ : (𝔘 : ∣ F↓ ∣F) → 𝔘 << (𝕛 𝔘) is-true
      N₁ _ a₀ a∈U = dir a∈U

      N₂ : (𝔘 : ∣ F↓ ∣F) → π₀ (𝕛 (𝕛 𝔘)) ⊆ π₀ (𝕛 𝔘) is-true
      N₂ 𝔘@(U , _) = lem4 (π₀ (𝕛 𝔘)) U (λ _ q → q)
```

We denote by `L` the frame of fixed points for `𝕛`.

```
  L : Frame (suc ℓ₀) ℓ₀ ℓ₀
  L = nuclear-fixed-point-frame F↓ (𝕛 , 𝕛-nuclear)

  ⦅_⦆ : ∣ L ∣F → 𝒫 ∣ P ∣ₚ
  ⦅ ((U , _) , _) ⦆ = U
```

Given some `x` in `F`, we define a map taking `x` to its *downwards-closure*.

```
  ↓-clos : stage D → ∣ F↓ ∣F
  ↓-clos x = x↓ , down-DC
    where
      x↓ = λ y → y ⊑[ P ] x
      down-DC : IsDownwardClosed P x↓ is-true
      down-DC z y z⊑x y⊑z = ⊑[ P ]-trans y z x y⊑z z⊑x

  x◀x↓ : (x : stage D) → x <| (λ - → - ⊑[ P ] x)
  x◀x↓ x = dir (⊑[ P ]-refl x)
```

By composing this with the covering nucleus, we define a map `e` from `F` to `F↓`.

```
  e : stage D → ∣ F↓ ∣F
  e z = (λ a → (a <| (π₀ (↓-clos z))) , squash) , NTS
    where
      NTS : IsDownwardClosed P (λ a → (a <| (λ - → - ⊑[ P ] z)) , squash) is-true
      NTS _ _ x y = lem1 (λ _ _ x⊑y y⊑z → ⊑[ P ]-trans _ _ z y⊑z x⊑y) y x
```

We can further refine the codomain of `e` to `L`. In other words, we can prove that `j (e
x) = e x` for every `x`. We call the version `e` with the refined codomain `η`.

```
  fixing : (x : stage D) → 𝕛 (e x) ≡ e x
  fixing x = ⊑[ P↓ ]-antisym (𝕛 (e x)) (e x) NTS up
    where
      NTS : ∀ y → π₀ (𝕛 (e x)) y is-true → π₀ (e x) y is-true
      NTS = lem4 (π₀ (e x)) (π₀ (↓-clos x)) (λ _ q → q)
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
      η-mono : IsMonotonic P (pos L) η
      η-mono x y x⊑y a (dir p)        = dir (⊑[ P ]-trans a x y p x⊑y)
      η-mono x y x⊑y a (branch b f)   = branch b (λ c → η-mono x y x⊑y (next D c) (f c))
      η-mono x y x⊑y a (squash p q i) = squash (η-mono x y x⊑y a p) (η-mono x y x⊑y a q) i
```
