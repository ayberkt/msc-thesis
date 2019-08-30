module FormalTopology where

open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Product                          using (Σ-syntax)

Subset : Set → Set₁
Subset S = S → Set

_∈_ : {S : Set} → S → Subset S → Set
x ∈ U = U x


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
    refl   : (x   : S) (U   : Subset S) → x ∈ U → x ◀ U
    trans  : (a   : S) (U V : Subset S) → a ◀ U → U ◀ₛ V → a ◀ V
    ·-pair : (a   : S) (U V : Subset S) → a ◀ U → a ◀ V → a ◀ (U ∙ₛ V)
    ·-inj₁ : (a b : S) (U   : Subset S) → a ◀ U → (a ∙ b) ◀ U
    ·-inj₂ : (a b : S) (U   : Subset S) → b ◀ U → (a ∙ b) ◀ U
    top    : (a   : S)                  → a ◀ [ 𝟏 ]

    mono   : (a   : S) (U   : Subset S) → Σ[ b ∈ S ](U b → Pos b)
    posit  : (a   : S) (U   : Subset S) → (Pos a → a ◀ U) → a ◀ U
