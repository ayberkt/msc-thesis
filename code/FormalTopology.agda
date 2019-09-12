module FormalTopology where

open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Product                          using (Σ-syntax)
open import Subset


-- Definition 1.2.
record FormalTopology (S : Set) : Set₁ where

  field
    𝟏   : S
    _∙_ : S → S → S
    _◀_ : S → Subset S → Set
    Pos : S → Set

  _◀ₛ_ : Subset S → Subset S → Set
  U ◀ₛ V = (b : S) → U b → b ◀ V

  _∙ₛ_ : Subset S → Subset S → Subset S
  U ∙ₛ V = λ x → Σ[ u ∈ S ] Σ[ v ∈ S ] (u ∈ U → v ∈ V → x ≡ (u ∙ v))

  [_] : S → Subset S
  [ s ] = λ x → x ≡ s

  field
    refl    : (a   : S) (U   : Subset S) → a ∈ U → a ◀ U
    trans   : (a   : S) (U V : Subset S) → a ◀ U → U ◀ₛ V → a ◀ V
    ·-right : (a   : S) (U V : Subset S) → a ◀ U → a ◀ V → a ◀ (U ∙ₛ V)
    ·-left₁ : (a b : S) (U V : Subset S) → a ◀ U → (a ∙ b) ◀ V
    ·-left₂ : (a b : S) (U V : Subset S) → b ◀ U → (a ∙ b) ◀ V
    top     : (a   : S)                  → a ◀ [ 𝟏 ]

    mono    : (a   : S) (U   : Subset S) → Pos a → a ◀ U → Σ[ b ∈ S ](b ∈ U → Pos b)
    posit   : (a   : S) (U   : Subset S) → (Pos a → a ◀ U) → a ◀ U
