module UniversalAlgebra (Var : Set) where

open import Relation.Binary.PropositionalEquality as Eq

open        Eq           using (_≡_; refl)
open import Data.Product using (_×_; _,_; Σ-syntax; proj₁; proj₂)
open import Data.List    using (List)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Vec     using (Vec; _∷_; []; map)
open import Data.Fin     using (Fin) renaming (suc to S; zero to Z)
open import Function     using (_∘_)
open import Data.Nat     using (ℕ; zero; suc)
open import Data.Unit    using (⊤)

record Signature : Set₁ where
  field
    Σ  : Set
    ar : Σ → ℕ

∣_∣ : Signature → Set
∣_∣ = Signature.Σ

data Term (𝒮 : Signature) (X : Set) : Set where
  `_  : X → Term 𝒮 X
  _$_ : (op : Signature.Σ 𝒮) → Vec (Term 𝒮 X) (Signature.ar 𝒮 op) → Term 𝒮 X

record Algebra (𝒮 : Signature) : Set₁ where
  open Signature 𝒮

  field
    A   : Set
    ⟦_⟧ : (op : Σ) → Vec A (ar op) → A

  mutual
    ext : (Var → A) → Term 𝒮 Var → A
    ext g (` x)    = g x
    ext g (f $ ts) = ⟦ f ⟧ (ext⋆ g ts)

    ext⋆ : {n : ℕ} → (Var → A)→ Vec (Term 𝒮 Var) n → Vec A n
    ext⋆ _ []       = []
    ext⋆ g (t ∷ ts) = ext g t ∷ ext⋆ g ts

∣_∣A : {𝒮 : Signature} → Algebra 𝒮 → Set
∣_∣A = Algebra.A

Equation : Signature → Set
Equation 𝒮 = Term 𝒮 Var × Term 𝒮 Var

Theory : Signature → Set₁
Theory 𝒮 = Σ[ I ∈ Set ] (I → Equation 𝒮)

_holds-in_ : {𝒮 : Signature} → Equation 𝒮 → Algebra 𝒮 → Set
(s , t) holds-in 𝒜 = (g : Var → ∣ 𝒜 ∣A) → Algebra.ext 𝒜 g s ≡ Algebra.ext 𝒜 g t

_is-a_ : {𝒮 : Signature} → Algebra 𝒮 → Theory 𝒮 → Set
_is-a_ {𝒮} 𝒜 𝕋@(I , ℰ) = (i : I) → (ℰ i) holds-in 𝒜

_generated-by_ : {𝒮 : Signature} → (𝒜 : Algebra 𝒮) → (Var → ∣ 𝒜 ∣A) → Set
_generated-by_ {𝒮} 𝒜 g = (a : ∣ 𝒜 ∣A) → Σ[ t ∈ (Term 𝒮 Var) ] Algebra.ext 𝒜 g t ≡ a

Relation : Set → Set₁
Relation A = A → A → Set

record Presentation (𝒮 : Signature) : Set₁ where
  constructor _⟨_||_⟩

  field
    𝕋 : Theory 𝒮
    G : Set
    R : Σ[ n ∈ ℕ ] (Fin n → Relation G)

record Model (𝒮 : Signature) (ℙ : Presentation 𝒮) : Set₁ where
  field
    A : Algebra 𝒮

  𝕋         = Presentation.𝕋 ℙ
  ∣ℛ∣       = proj₁ (Presentation.R ℙ)
  ℛ         = proj₂ (Presentation.R ℙ)
  generator = Presentation.G ℙ

  field
    is-𝕋-algebra : A is-a 𝕋
    ⟦_⟧          : generator → ∣ A ∣A

  -- TODO: complete missing law.

-- -}
-- -}
-- -}
