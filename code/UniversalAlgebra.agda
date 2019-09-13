module UniversalAlgebra (Var : Set) where

open import Data.Product using (_×_; _,_)
open import Data.List    using (List)
open import Data.Vec     using (Vec; _∷_; []; map)
open import Function     using (_∘_)
open import Data.Nat     using (ℕ; zero; suc)
open import Data.Unit    using (⊤)

record Signature : Set₁ where
  no-eta-equality
  field
    Σ  : Set
    ar : Σ → ℕ

record Algebra (𝒮 : Signature) : Set₁ where
  no-eta-equality
  open Signature 𝒮

  field
    A   : Set
    ⟦_⟧ : (op : Σ) → Vec A (ar op) → A

data Term (𝒮 : Signature) : Set where
  `_  : Var → Term 𝒮
  _$_ : (op : Signature.Σ 𝒮) → Vec (Term 𝒮) (Signature.ar 𝒮 op) → Term 𝒮

∣_∣ : Signature → Set
∣_∣ = Signature.Σ

Assignment : {𝒮 : Signature} → Algebra 𝒮 → Set
Assignment 𝒜 = Var → Algebra.A 𝒜

mutual

  _♯ : {𝒮 : Signature} {𝒜 : Algebra 𝒮} → Assignment 𝒜 → Term 𝒮 → Algebra.A 𝒜
  (g ♯) (` x)           = g x
  _♯ {_} {𝒜} g (f $ ts) =
    let open Algebra 𝒜 using (⟦_⟧) in ⟦ f ⟧ (_♯⋆ g ts)

  _♯⋆ : {𝒮 : Signature} {𝒜 : Algebra 𝒮} {n : ℕ}
      → Assignment 𝒜 → Vec (Term 𝒮) n → Vec (Algebra.A 𝒜) n
  (g ♯⋆) []       = []
  (g ♯⋆) (t ∷ ts) = (g ♯) t ∷ _♯⋆ g ts

Equation : Signature → Set
Equation 𝒮 = Term 𝒮 × Term 𝒮

Theory : Signature → Set
Theory = List ∘ Equation
