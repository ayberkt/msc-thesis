{-# OPTIONS --cubical #-}

open import Data.Nat using (ℕ)
open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude using (isProp)
open import Data.Product using (_×_; _,_)
open import Function using (flip)

data 𝔻  : Type₀ where
  []    : 𝔻
  _⌢_   : 𝔻 → ℕ → 𝔻

IsDC : (𝔻 → Type₀) → Type₀
IsDC P = (σ : 𝔻) (n : ℕ) → P σ → P (σ ⌢ n)

data _◀_ (σ : 𝔻) (P : 𝔻 → Type₀) : Type₀ where
  dir      : P σ → σ ◀ P
  branch   : ((n : ℕ) → (σ ⌢ n) ◀ P) → σ ◀ P
  squash   : (φ ψ : σ ◀ P) → φ ≡ ψ

variable
  m n : ℕ; σ τ : 𝔻; P Q : 𝔻 → Type₀

◀-prop : isProp (σ ◀ P)
◀-prop = squash

δ : σ ◀ P → ((v : 𝔻) → P v → v ◀ Q) → σ ◀ Q
δ (dir     uεP)         φ  = φ _ uεP
δ (branch  f)           φ  = branch (λ n → δ (f n) φ)
δ (squash  u◀P₀ u◀P₁ i) φ  = squash (δ u◀P₀ φ) (δ u◀P₁ φ) i

δ-corollary : σ ◀ (λ - → - ◀ P) → σ ◀ P
δ-corollary u◀◀P = δ u◀◀P (λ _ v◀P → v◀P)

ζ : (n : ℕ) → IsDC P → σ ◀ P → (σ ⌢ n) ◀ P
ζ n dc (dir     σεP)         = dir (dc _ n σεP)
ζ n dc (branch  f)           = branch λ m → ζ m dc (f n)
ζ n dc (squash  σ◀P σ◀P′ i)  = squash (ζ n dc σ◀P) (ζ n dc σ◀P′) i

ζ′ : IsDC P → IsDC (λ - → - ◀ P)
ζ′ P-dc σ n σ◀P = ζ n P-dc σ◀P

-- Meet preservation.
-- mp : IsDC P → IsDC Q → σ ◀ P → σ ◀ Q → σ ◀ (λ - → P - × Q -)
-- mp P-dc Q-dc σ◀P                  (squash σ◀Q₀ σ◀Q₁ i) = squash (mp P-dc Q-dc σ◀P σ◀Q₀) (mp P-dc Q-dc σ◀P σ◀Q₁) i
-- mp P-dc Q-dc (squash σ◀P₀ σ◀P₁ i) σ◀Q                  = squash (mp P-dc Q-dc σ◀P₀ σ◀Q) (mp P-dc Q-dc σ◀P₁ σ◀Q) i
-- mp P-dc Q-dc (dir σεP)            (dir σεQ)            = dir (σεP , σεQ)
-- mp P-dc Q-dc (dir σεP)            (branch g)           = branch (λ n → mp P-dc Q-dc (dir (P-dc _ n σεP)) (g n))
-- mp P-dc Q-dc (branch f)           (dir σεQ)            = branch (λ n → mp P-dc Q-dc (f n) {!dir (Q-dc _ n σεQ)!})
-- mp P-dc Q-dc (branch f)           (branch g)           = branch (λ n → mp P-dc Q-dc (f n) (g n))

