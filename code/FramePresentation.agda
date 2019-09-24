module FramePresentation where

open import Data.Product using (_×_; _,_; Σ-syntax; proj₁; proj₂)
open import Data.Nat     using (ℕ; suc; zero)
open import Data.Fin     using (Fin)
open import Level

open import Poset
open import Frame
open import Relation.Binary.PropositionalEquality using (_≡_)

data Basis (G : Set) : Set where
  subbasic : G → Basis G
  _∧_      : Basis G → Basis G → Basis G

data Open (G : Set) : Set₁ where
  ∨_ : Sub (Basis G) → Open G

data Equality {ℓ : Level} (X : Set ℓ) : Set ℓ where
  _≈_ : X → X → Equality X

lhs : {ℓ : Level} {X : Set ℓ} → Equality X → X
lhs (l ≈ _) = l

rhs : {ℓ : Level} {X : Set ℓ} → Equality X → X
rhs (_ ≈ r) = r

record Presentation : Set₁ where
  constructor Fr⟨_,_⟩

  field
    gens : Set
    rels : Σ[ n ∈ ℕ ] (Fin n → Equality (Open gens))

RawModel : Frame → Presentation → Set
RawModel F P = Presentation.gens P → (proj₁ (Frame.P F))

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

_models_ : Presentation → Frame → Set
P models F = Σ[ ⟦_⟧ ∈ (RawModel F P) ] (resp-rels F P ⟦_⟧)

_presents_ : Presentation → Frame → Set₁
P presents F = Σ[ M ∈ (P models F) ]
  ((F′ : Frame) → (M′ : P models F′) →
     let
       open Presentation P using (gens)
       ⟦_⟧F  = proj₁ M
       ⟦_⟧F′ = proj₁ M′
     in
       Σ[ θ ∈ (F ─f→ F′) ] ((g : gens) → θ $f ⟦ g ⟧F ≡ ⟦ g ⟧F′))
