module FramePresentation where

open import Common

open import Data.Nat     using (ℕ) renaming (suc to S; zero to Z)
open import Data.Fin     using (Fin)

open import Poset
open import Frame

data Basis {ℓ : Level} (G : Set ℓ) : Set ℓ where
  subbasic : G → Basis G
  _∧_      : Basis G → Basis G → Basis G

data Open {ℓ : Level} (G : Set ℓ) : Set (suc ℓ) where
  ∨_ : Sub (Basis G) → Open G

data Equality {ℓ : Level} (X : Set ℓ) : Set ℓ where
  _≈_ : X → X → Equality X

lhs : {ℓ : Level} {X : Set ℓ} → Equality X → X
lhs (l ≈ _) = l

rhs : {ℓ : Level} {X : Set ℓ} → Equality X → X
rhs (_ ≈ r) = r

record Presentation {ℓ : Level} : Set (suc ℓ) where
  constructor Fr⟨_,_⟩

  field
    gens : Set ℓ
    rels : Σ[ n ∈ ℕ ] (Fin n → Equality (Open gens))

-- The data of a model is simply a function from the set of generators to the underlying
-- set of the frame.
RawModel : Frame → Presentation → Set
RawModel F Fr⟨ gens , rels ⟩ = gens → (proj₁ (Frame.P F))

module _ (F : Frame) (P : Presentation) (⟦_⟧ : RawModel F P) where

  open Presentation P
  ∣R∣ = proj₁ rels
  R   = proj₂ rels

  ∣F∣ = proj₁ (Frame.P F)

  ⟦_⟧B : Basis gens → ∣F∣
  ⟦ subbasic x ⟧B = ⟦ x ⟧
  ⟦ b₀ ∧ b₁    ⟧B = Frame._⊓_ F ⟦ b₀ ⟧B ⟦ b₁ ⟧B

  ⟦_⟧O : Open gens → ∣F∣
  ⟦ ∨ (I , ℱ) ⟧O = (Frame.⊔ F) (I , λ i → ⟦ ℱ i ⟧B)

  resp-rels : Set
  resp-rels = (i : Fin ∣R∣) → ⟦ lhs (R i) ⟧O ≡ ⟦ rhs (R i) ⟧O

-- A model is a raw model that respects the relations of the presentation.
_models_ : Presentation → Frame → Set
P models F = Σ[ ⟦_⟧ ∈ (RawModel F P) ] (resp-rels F P ⟦_⟧)

-- A presentation P *presents* the frame F if it is the least model for F.
_presents_ : Presentation → Frame → Set₁
P presents F = Σ[ M ∈ (P models F) ]
  ((F′ : Frame) → (M′ : P models F′) →
     let
       open Presentation P using (gens)
       ⟦_⟧F  = proj₁ M
       ⟦_⟧F′ = proj₁ M′
     in
       Σ![ θ ∈ (F ─f→ F′) ] ((g : gens) → θ $f ⟦ g ⟧F ≡ ⟦ g ⟧F′))
