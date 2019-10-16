{-# OPTIONS --without-K #-}

open import Truncation

module Frame (pt : TruncationExists) where

open import Common
open import Truncation
open import Homotopy
open import Unit        using (tt)
open import Poset

import AlgebraicProperties

open TruncationExists pt

private
  variable
    ℓ ℓ′ ℓ₀ ℓ₁ ℓ₂ : Level

Sub : (ℓ : Level) → Set ℓ′ → Set (ℓ′ ⊔ suc ℓ)
Sub ℓ A = Σ[ I ∈ Set ℓ ] (I → A)

index : {X : Set ℓ} → Sub ℓ′ X → Set ℓ′
index (I , _) = I

-- Application of a family over X to an index.
_€_ : {X : Set ℓ} → (ℱ : Sub ℓ′ X) → index ℱ → X
_€_ (_ , f) = f

infixr 7 _€_

-- Composition of a family with a function.
_⊚_ : {X : Set ℓ₀} {Y : Set ℓ₁} → (g : X → Y) → (ℱ : Sub ℓ₂ X) → Sub ℓ₂ Y
g ⊚ ℱ = (index ℱ) , g ∘ (_€_ ℱ)

-- Membership for families.
_ε_ : {X : Set ℓ} → X → Sub ℓ′ X → Set (ℓ ⊔ ℓ′)
x ε S = Σ[ i ∈ index S ] (S € i) ≡ x

record Frame (ℓ₀ ℓ₁ ℓ₂ : Level) : Set (suc (ℓ₀ ⊔ ℓ₁ ⊔ ℓ₂)) where

  field
    P   : Poset ℓ₀ ℓ₁

  O   = proj₁ P
  _⊑_ = PosetStr._⊑_ (proj₂ P)

  field
    𝟏   : O
    _⊓_ : O → O → O
    ⊔_  : Sub ℓ₂ O → O

  field

    -- Greatest lower bound.
    -- Consider merging the following three requirements and prove that equivalent to
    -- this. Thanks to univalence, one can alternate between the two styles if one happens
    -- to be more preferable than the other in certain cases.
    top         : (o     : O) → o ⊑ 𝟏 holds
    ⊓-lower₀    : (o p   : O) → (o ⊓ p) ⊑ o holds
    ⊓-lower₁    : (o p   : O) → (o ⊓ p) ⊑ p holds
    ⊓-greatest  : (o p q : O) → q ⊑ o holds → q ⊑ p holds → q ⊑ (o ⊓ p) holds

    -- Least upper bound.
    ⊔-upper : (ℱ : Sub ℓ₂ O) → (o : O) → o ε ℱ → o ⊑ (⊔ ℱ) holds
    ⊔-least : (ℱ : Sub ℓ₂ O) → (p : O) → ((o : O) → o ε ℱ → o ⊑ p holds) → (⊔ ℱ) ⊑ p holds

    -- Binary meety distribute over arbitrary joins.
    dist : (o : O) (ℱ : Sub ℓ₂ O) → o ⊓ (⊔ ℱ) ≡ ⊔ (index ℱ , λ i → o ⊓ (ℱ € i))

-- Projection for the carrier set of a frame i.e., the carrier set of the underlying poset.
∣_∣F : Frame ℓ₀ ℓ₁ ℓ₂ → Set ℓ₀
∣_∣F = proj₁ ∘ Frame.P

record _─f→_ {ℓ ℓ′ ℓ₂ : Level} (F₀ F₁ : Frame ℓ ℓ′ ℓ₂) : Set (ℓ ⊔ ℓ′ ⊔ suc ℓ₂) where
  open Frame F₀ using () renaming (P to P₀; _⊓_ to _⊓₀_; ⊔_ to ⊔₀_; 𝟏 to 𝟏₀)
  open Frame F₁ using () renaming (P to P₁; _⊓_ to _⊓₁_; ⊔_ to ⊔₁_; 𝟏 to 𝟏₁)

  field
    m : P₀ ─m→ P₁

  field
     resp-id : m $ₘ 𝟏₀ ≡ 𝟏₁
     resp-⊓  : (x y : ∣ P₀ ∣ₚ) → m $ₘ (x ⊓₀ y) ≡ (m $ₘ x) ⊓₁ (m $ₘ y)
     resp-⊔  : (ℱ : Sub ℓ₂ ∣ P₀ ∣ₚ) → m $ₘ (⊔₀ ℱ) ≡ (⊔₁ (proj₁ ℱ , λ i → m $ₘ (ℱ € i)))

-- Convenient notation for frame homomorphism application.
_$f_ : {F₀ : Frame ℓ ℓ′ ℓ₂} {F₁ : Frame ℓ ℓ′ ℓ₂}
     → (F₀ ─f→ F₁) → (proj₁ (Frame.P F₀)) → (proj₁ (Frame.P F₁))
_$f_ = proj₁ ∘ _─f→_.m

-- An element of the poset is like a finite observation whereas an element of the
-- frame of downward closed posets is like a general observation.

-- The set of downward-closed subsets of a poset forms a frame.
downward-subset-poset : (P : Poset ℓ ℓ′) → Poset (suc ℓ ⊔ ℓ′) ℓ
downward-subset-poset {ℓ = ℓ} {ℓ′} (X , P) =
  𝔻 , posetstr _<<_ A-set <<-refl <<-trans <<-antisym
  where
    open PosetStr P using (_⊑_; ⊑-refl; ⊑-trans; ⊑-antisym)

    𝔻 = DownwardClosedSubset (X , P)

    A-set : IsSet (DownwardClosedSubset (X , P))
    A-set = DownwardClosedSubset-set (X , P)

    inc : 𝔻 → 𝔻 → Set ℓ
    inc (S , _) (T , _) = S ⊆ T

    <<-prop : (S T : 𝔻) → IsProp (inc S T)
    <<-prop (S , _) (T , _) = ⊆-prop S T

    open AlgebraicProperties A-set (λ S T → inc S T , <<-prop S T)
       renaming ( IsReflexive  to <<-IsReflexive
                ; IsTransitive to <<-IsTransitive
                ; IsAntisym    to <<-IsAntisym)

    _<<_ : 𝔻 → 𝔻 → Ω ℓ
    S << T = (inc S T) , (<<-prop S T)

    <<-refl : <<-IsReflexive holds
    <<-refl = ⊆-refl ∘ proj₁

    <<-trans : <<-IsTransitive holds
    <<-trans (S , _) (T , _) (U , _) = ⊆-trans S T U

    <<-antisym : <<-IsAntisym holds
    <<-antisym (S , _) (T , _) S⊆T T⊆S =
      to-subtype-≡ (holds-prop ∘ IsDownwardClosed (X , P)) (⊆-antisym S⊆T T⊆S)

-- The set of downward-closed subsets of a poset forms a frame.
downward-subset-frame : {ℓ ℓ′ : Level} (P : Poset ℓ ℓ′) → Frame (suc ℓ ⊔ ℓ′) ℓ ℓ
downward-subset-frame {ℓ = ℓ} {ℓ′} (X , P) =
  record
    { P           =  𝔻ₚ
    ; 𝟏           =  𝟏
    ; _⊓_         =  _⊓_
    ; ⊔_          =  ⊔_
    ; top         =  𝟏-top
    ; ⊓-lower₀    =  ⊓-lower₀
    ; ⊓-lower₁    =  ⊓-lower₁
    ; ⊓-greatest  =  ⊓-greatest
    ; ⊔-upper     =  ⊔-upper
    ; ⊔-least     =  ⊔-least
    ; dist        =  dist
    }
  where
    𝔻ₚ = downward-subset-poset (X , P)
    𝔻  = ∣ 𝔻ₚ ∣ₚ

    ∣_∣𝔻 : 𝔻 → 𝒫 X
    ∣ S , _ ∣𝔻 = S

    open PosetStr (proj₂ 𝔻ₚ) using    ()
                             renaming ( _⊑_       to  _<<_
                                      ; ⊑-refl    to  <<-refl
                                      ; ⊑-antisym to  <<-antisym)
    open PosetStr P          using    (_⊑_)

    𝟏 = entirety , λ _ _ _ _ → tt

    ∩-down : (S T : 𝒫 X)
           → IsDownwardClosed (X , P) S holds
           → IsDownwardClosed (X , P) T holds
           → IsDownwardClosed (X , P) (S ∩ T) holds
    ∩-down S T S↓ T↓ x y x∈S∩T y⊑x = S↓ x y (proj₁ x∈S∩T) y⊑x , T↓ x y (proj₂ x∈S∩T) y⊑x

    _⊓_ : 𝔻 → 𝔻 → 𝔻
    (S , S-dc) ⊓ (T , T-dc) = (S ∩ T) , ∩-down S T S-dc T-dc

    𝟏-top : (D : 𝔻) → (D << 𝟏) holds
    𝟏-top D _ _ = tt

    -- Given a family ℱ over 𝔻 and some x : X, `in-some-set ℱ x` holds iff there is some
    -- set S among ℱ such that x ∈ S.
    in-some-set-of : (ℱ : Sub ℓ 𝔻) → X → Set ℓ
    in-some-set-of ℱ x = Σ[ i ∈ index ℱ ] (x ∈ ∣ ℱ € i ∣𝔻) holds

    ⊔_ : Sub ℓ 𝔻 → 𝔻
    ⊔ ℱ = (λ x → ∥ in-some-set-of ℱ x ∥ , ∥∥-prop _) , ⊔ℱ↓
      where
        ind : (x y : X) → y ⊑ x holds → in-some-set-of ℱ x → ∥ in-some-set-of ℱ y ∥
        ind x y y⊑x (i , x∈ℱᵢ) = ∣ i , proj₂ (ℱ € i) x y x∈ℱᵢ y⊑x ∣

        ⊔ℱ↓ : IsDownwardClosed (X , P) (λ x → ∥ in-some-set-of ℱ x ∥ , ∥∥-prop _) holds
        ⊔ℱ↓ x y ∣p∣ y⊑x = ∥∥-rec (∥∥-prop _) (ind x y y⊑x) ∣p∣

    ⊔-upper : (ℱ : Sub ℓ 𝔻) (D : 𝔻) → D ε ℱ → D << (⊔ ℱ) holds
    ⊔-upper ℱ D DεS@(i , p) x x∈D = ∣ i , transport (λ - → x ∈ ∣ - ∣𝔻 holds) (sym p) x∈D ∣

    ⊔-least : (ℱ : Sub ℓ 𝔻) (z : 𝔻) → ((o : 𝔻) → o ε ℱ → (o << z) holds) → (⊔ ℱ) << z holds
    ⊔-least ℱ D φ x x∈⊔S = ∥∥-rec (proj₂ (∣ D ∣𝔻 x)) ind x∈⊔S
      where
        ind : in-some-set-of ℱ x → x ∈ ∣ D ∣𝔻 holds
        ind (i , x∈ℱᵢ) = φ (ℱ € i) (i , refl) x x∈ℱᵢ

    ⊓-lower₀ : (D E : 𝔻) → (D ⊓ E) << D holds
    ⊓-lower₀ D E x (x∈D , _) = x∈D

    ⊓-lower₁ : (D E : 𝔻) → (D ⊓ E) << E holds
    ⊓-lower₁ D E x (_ , x∈F) = x∈F

    ⊓-greatest : (D E F : 𝔻) → (F << D) holds → (F << E) holds → F << (D ⊓ E) holds
    ⊓-greatest D E F F<<D F<<E x x∈F = (F<<D x x∈F) , (F<<E x x∈F)

    dist : (D : 𝔻) (ℱ : Sub ℓ 𝔻) → D ⊓ (⊔ ℱ) ≡ ⊔ (index ℱ , λ i → D ⊓ (ℱ € i))
    dist D ℱ = <<-antisym (D ⊓ (⊔ ℱ)) (⊔ (index ℱ , λ i → D ⊓ (ℱ € i))) down up
      where
        𝒜 = ∣ D ⊓ (⊔ ℱ) ∣𝔻
        ℬ = ∣ ⊔ (index ℱ , (λ i → D ⊓ (ℱ € i))) ∣𝔻

        down : (x : X) → x ∈ 𝒜 holds → x ∈ ℬ holds
        down x x∈𝒜@(x∈D , x∈⊔ℱ) = ∥∥-rec (∥∥-prop _) ind x∈⊔ℱ
          where
            ind : in-some-set-of ℱ x → ∥ in-some-set-of (index ℱ , λ i → D ⊓ (ℱ € i)) x ∥
            ind (i , x∈ℱᵢ) = ∣ i , x∈D , x∈ℱᵢ ∣

        up : (x : X) → x ∈ ℬ holds → x ∈ 𝒜 holds
        up x x∈ℬ =
          ∥∥-rec (Σ-resp-prop (holds-prop (x ∈ ∣ D ∣𝔻)) λ _ →
            holds-prop (x ∈ ∣ ⊔ ℱ ∣𝔻)) φ x∈ℬ
          where
            φ : in-some-set-of (index ℱ , λ j → D ⊓ (ℱ € j)) x
              → x ∈ ∣ D ∣𝔻 holds × x ∈ ∣ ⊔ ℱ ∣𝔻 holds
            φ (i , x∈D , x∈ℱᵢ) = x∈D , ∣ i , x∈ℱᵢ ∣

-- -}
-- -}
-- -}
