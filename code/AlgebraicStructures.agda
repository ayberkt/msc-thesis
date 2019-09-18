module AlgebraicStructures where

open import Data.Nat  using (ℕ; suc; zero)
open import Data.List using (List; _∷_; [])
open import Data.Vec using (Vec) renaming (_∷_ to _∷V_; [] to []V)
open import Data.Product using (Σ-syntax; _,_)

data Var : Set where
  x y z w : Var

open import UniversalAlgebra Var

data MonoidOp : Set where
  mempty  : MonoidOp
  mappend : MonoidOp

MonoidSyntax : Signature
(Signature.Σ  MonoidSyntax)         = MonoidOp
(Signature.ar MonoidSyntax) mempty  = 0
(Signature.ar MonoidSyntax) mappend = 2

Monoid : Theory MonoidSyntax
Monoid =
      ((` x) · ε , (` x))                                   -- left identity.
    ∷ (ε · (` x) , (` x))                                   -- right identity.
    ∷ (((` x) · (` y)) · (` z) , ((` x) · ((` y) · (` z)))) -- associativity.
    ∷ []
  where
    open Signature MonoidSyntax
    _·_ : Term MonoidSyntax → Term MonoidSyntax → Term MonoidSyntax
    a · b =  mappend $ (a ∷V b ∷V []V)
    ε = mempty $ []V
