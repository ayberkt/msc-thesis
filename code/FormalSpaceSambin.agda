module FormalSpaceSambin where

open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Product                          using (Σ-syntax; _,_)
open import Homotopy
open import Level


-- Definition 1.2.
record FormalSpaceStr {ℓ : Level} (S : Set ℓ) : Set (suc ℓ) where

  field
    𝟏   : S
    _∙_ : S → S → S
    _◀_ : S → 𝒫 S → Set
    Pos : S → Set

  _◀ₛ_ : 𝒫 S → 𝒫 S → Set ℓ
  U ◀ₛ V = (b : S) → b ∈ U holds → b ◀ V

  _∙ₛ_ : 𝒫 S → 𝒫 S → 𝒫 S
  U ∙ₛ V = λ x → (Σ[ u ∈ S ] Σ[ v ∈ S ] (u ∈ U holds → v ∈ V holds → x ≡ (u ∙ v)))
         , {!Σ-resp-prop!}
  -- (λ x → Σ[ u ∈ S ] Σ[ v ∈ S ] (u ∈ U holds → v ∈ V holds → x ≡ (u ∙ v))) , ?

  [_] : S → 𝒫 S
  [ s ] = {!!} -- (λ x → x ≡ s) , ?

  field
    refl    : (a   : S) (U   : 𝒫 S) → a ∈ U holds → a ◀ U
    trans   : (a   : S) (U V : 𝒫 S) → a ◀ U → U ◀ₛ V → a ◀ V
    ·-right : (a   : S) (U V : 𝒫 S) → a ◀ U → a ◀ V → a ◀ (U ∙ₛ V)
    ·-left₁ : (a b : S) (U V : 𝒫 S) → a ◀ U → (a ∙ b) ◀ V
    ·-left₂ : (a b : S) (U V : 𝒫 S) → b ◀ U → (a ∙ b) ◀ V
    top     : (a   : S)                  → a ◀ [ 𝟏 ]

    mono    : (a   : S) (U   : 𝒫 S) → Pos a → a ◀ U → Σ[ b ∈ S ](b ∈ U holds → Pos b)
    posit   : (a   : S) (U   : 𝒫 S) → (Pos a → a ◀ U) → a ◀ U
