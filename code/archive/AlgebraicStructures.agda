module AlgebraicStructures where

open import Data.Nat using (ℕ; suc; zero; _+_)
open import Data.Nat.Properties using (+-identity; +-assoc)
open import Data.Fin using (Fin) renaming (suc to S; zero to Z)
open import Data.Vec using (Vec; _∷_; [])
open import Data.Product using (Σ-syntax; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Data.List.Membership.Propositional

data Var : Set where
  𝓍 𝓎 𝓏 : Var

open import UniversalAlgebra Var

data MonoidOp : Set where
  mempty  : MonoidOp
  mappend : MonoidOp

MonoidSyntax : Signature
(Signature.Σ  MonoidSyntax)         = MonoidOp
(Signature.ar MonoidSyntax) mempty  = 0
(Signature.ar MonoidSyntax) mappend = 2

Monoid : Theory MonoidSyntax
Monoid = Fin 3 , ℰ
  where
    open Signature MonoidSyntax
    _·_ : Term MonoidSyntax Var → Term MonoidSyntax Var → Term MonoidSyntax Var
    a · b =  mappend $ (a ∷ b ∷ [])
    ε = mempty $ []
    ℰ : Fin 3 → Equation MonoidSyntax
    ℰ Z         = ((` 𝓍) · ε) , (` 𝓍)
    ℰ (S Z)     = (ε · (` 𝓍)) , (` 𝓍)
    ℰ (S (S Z)) = ((` 𝓍) · (` 𝓎)) · (` 𝓏) , (` 𝓍) · ((` 𝓎) · (` 𝓏))

ℕ-+-0 : Algebra MonoidSyntax
ℕ-+-0 = record { A = ℕ ; ⟦_⟧ = ⟦_⟧ }
  where
    ⟦_⟧ : (op : Signature.Σ MonoidSyntax) → Vec ℕ (Signature.ar MonoidSyntax op) → ℕ
    ⟦ mempty  ⟧ []           = zero
    ⟦ mappend ⟧ (a ∷ b ∷ []) = a + b

foo : ℕ-+-0 is-a Monoid
foo Z         g = proj₂ +-identity (g 𝓍)
foo (S Z)     g = refl
foo (S (S Z)) g = +-assoc (g 𝓍) (g 𝓎) (g 𝓏)

data SemilatticeOp : Set where
  true meet : SemilatticeOp

SemilatticeSyntax : Signature
SemilatticeSyntax = record { Σ = SemilatticeOp ; ar = λ { true → 0 ; meet → 2 } }

Semilattice : Theory SemilatticeSyntax
Semilattice = Fin 4 , ℰ
  where
    _∧_ : Term SemilatticeSyntax Var → Term SemilatticeSyntax Var → Term SemilatticeSyntax Var
    x ∧ y = meet $ (x ∷ y ∷ [])
    ⊤ : Term SemilatticeSyntax Var
    ⊤ = true $ []
    ℰ : Fin 4 → Equation SemilatticeSyntax
    ℰ Z             = (` 𝓍) , (` 𝓍)
    ℰ (S Z)         = ((` 𝓍) ∧ (` 𝓎)) ∧ (` 𝓏) , (` 𝓍) ∧ ((` 𝓎) ∧ (` 𝓏))
    ℰ (S (S Z))     = (` 𝓍) ∧ ⊤ , (` 𝓍)
    ℰ (S (S (S Z))) = (` 𝓍) ∧ (` 𝓍) , (` 𝓍)
