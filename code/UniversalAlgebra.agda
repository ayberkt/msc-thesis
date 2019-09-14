module UniversalAlgebra (Var : Set) where

open import Relation.Binary.PropositionalEquality as Eq

open        Eq           using (_≡_; refl)
open import Data.Product using (_×_; _,_)
open import Data.List    using (List)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Vec     using (Vec; _∷_; []; map)
open import Function     using (_∘_)
open import Data.Nat     using (ℕ; zero; suc)
open import Data.Unit    using (⊤)

record Signature : Set₁ where
  field
    Σ  : Set
    ar : Σ → ℕ

∣_∣ : Signature → Set
∣_∣ = Signature.Σ

data Term (𝒮 : Signature) : Set where
  `_  : Var → Term 𝒮
  _$_ : (op : Signature.Σ 𝒮) → Vec (Term 𝒮) (Signature.ar 𝒮 op) → Term 𝒮

record Algebra (𝒮 : Signature) : Set₁ where
  open Signature 𝒮

  field
    A   : Set
    ⟦_⟧ : (op : Σ) → Vec A (ar op) → A

  mutual
    ext : (Var → A) → Term 𝒮 → A
    ext g (` x)    = g x
    ext g (f $ ts) = ⟦ f ⟧ (ext⋆ g ts)

    ext⋆ : {n : ℕ} → (Var → A)→ Vec (Term 𝒮) n → Vec A n
    ext⋆ _ []       = []
    ext⋆ g (t ∷ ts) = ext g t ∷ ext⋆ g ts

open Algebra

∣_∣A : {𝒮 : Signature} → Algebra 𝒮 → Set
∣_∣A = Algebra.A

Equation : Signature → Set
Equation 𝒮 = Term 𝒮 × Term 𝒮

Theory : Signature → Set
Theory = List ∘ Equation

_holds-in_ : {𝒮 : Signature} → Equation 𝒮 → Algebra 𝒮 → Set
(s , t) holds-in 𝒜 = (g : Var → ∣ 𝒜 ∣A) → ext 𝒜 g s ≡ ext 𝒜 g t

_models_ : {𝒮 : Signature} → Algebra 𝒮 → Theory 𝒮 → Set
_models_ {𝒮} 𝒜 𝒯 = (eq : Equation 𝒮) → eq ∈ 𝒯 → eq holds-in 𝒜

-- -}
-- -}
-- -}
