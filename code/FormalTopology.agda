module FormalTopology where

open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Product                          using (Σ-syntax)

Subset : Set → Set₁
Subset S = S → Set


-- Definition 1.2.
record FormalTopology (S : Set) : Set₁ where

  field
    𝟏   : S
    _·_ : S → S → S
    _◀_ : S → Subset S → Set
    Pos : S → Set

  _◀ₛ_ : Subset S → Subset S → Set
  U ◀ₛ V = (b : S) → U b → b ◀ V

  [_] : S → Subset S
  [ s ] = λ x → x ≡ s

  field
    refl   : (a   : S) (U   : Subset S) → U a → a ◀ U
    trans  : (a   : S) (U V : Subset S) → a ◀ U → U ◀ₛ V → a ◀ V
    ·-inj₁ : (a b : S) (U   : Subset S) → a ◀ U → (a · b) ◀ U
    ·-inj₂ : (a b : S) (U   : Subset S) → b ◀ U → (a · b) ◀ U
    top    : (a   : S)                  → a ◀ [ 𝟏 ]

    mono   : (a   : S) (U   : Subset S) → Σ[ b ∈ S ](U b → Pos b)
    posit  : (a   : S) (U   : Subset S) → (Pos a → a ◀ U) → a ◀ U
