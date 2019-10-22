open import Truncation

module FormalTopologySambin (pt : TruncationExists) where

open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Product                          using (Σ-syntax; _,_)
open import Homotopy
open import Level

open TruncationExists pt

-- Definition 1.2.
record IsFormalTopology {ℓ : Level} (S : Set ℓ) : Set (suc ℓ) where

  field
    𝟏   : S
    _∙_ : S → S → S
    _◀_ : S → 𝒫 S → Set
    Pos : S → Set

  field
    S-set : IsSet S

  _◀ₛ_ : 𝒫 S → 𝒫 S → Set ℓ
  U ◀ₛ V = (b : S) → b ∈ U holds → b ◀ V

  _∙ₛ_ : 𝒫 S → 𝒫 S → 𝒫 S
  U ∙ₛ V = λ x → ∥ Σ[ u ∈ S ] Σ[ v ∈ S ] (u ∈ U holds → v ∈ V holds → x ≡ u ∙ v) ∥
         , ∥∥-prop _

  [_] : S → 𝒫 S
  [ s ] x = (x ≡ s) , (S-set x s)

  field
    refl    : (a   : S) (U   : 𝒫 S) → a ∈ U holds → a ◀ U
    trans   : (a   : S) (U V : 𝒫 S) → a ◀ U → U ◀ₛ V → a ◀ V
    ·-right : (a   : S) (U V : 𝒫 S) → a ◀ U → a ◀ V → a ◀ (U ∙ₛ V)
    ·-left₀ : (a b : S) (U V : 𝒫 S) → a ◀ U → (a ∙ b) ◀ V
    ·-left₁ : (a b : S) (U V : 𝒫 S) → b ◀ U → (a ∙ b) ◀ V
    top     : (a   : S)             → a ◀ [ 𝟏 ]

    mono    : (a   : S) (U   : 𝒫 S) → Pos a → a ◀ U → Σ[ b ∈ S ](b ∈ U holds → Pos b)
    posit   : (a   : S) (U   : 𝒫 S) → (Pos a → a ◀ U) → a ◀ U

FormalTopology : (ℓ : Level) → Set (suc ℓ)
FormalTopology ℓ = Σ[ S ∈ (Set ℓ) ] IsFormalTopology S
