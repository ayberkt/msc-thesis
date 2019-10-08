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
    top    : (x     : O) → x ⊑ 𝟏 holds
    ⊓-low₁ : (x y   : O) → (x ⊓ y) ⊑ x holds
    ⊓-low₂ : (x y   : O) → (x ⊓ y) ⊑ y holds
    ⊓-max  : (x y z : O) → (z ⊑ x) holds → z ⊑ y holds → (z ⊑ (x ⊓ y)) holds

    -- Least upper bound.
    ⊔-up   : (S : Sub ℓ₂ O) → (o : O) → o ε S → o ⊑ (⊔ S) holds
    ⊔-min  : (S : Sub ℓ₂ O) → (z : O) → ((o : O) → o ε S → (o ⊑ z) holds) → (⊔ S) ⊑ z holds

    -- Binary meety distribute over arbitrary joins.
    dist   : (x : O) (S : Sub ℓ₂ O) → x ⊓ (⊔ S) ≡ ⊔ (proj₁ S , λ i → x ⊓ proj₂ S i)

-- Projection for the carrier set of a frame i.e., the carrier set of the underlying poset.
∣_∣F : Frame ℓ₀ ℓ₁ ℓ₂ → Set ℓ₀
∣_∣F = proj₁ ∘ Frame.P

record _─f→_ {ℓ ℓ′ ℓ₂ : Level} (F₀ : Frame ℓ ℓ′ ℓ₂) (F₁ : Frame ℓ ℓ′ ℓ₂) : Set (ℓ ⊔ ℓ′ ⊔ suc ℓ₂) where
  open Frame F₀ using () renaming (P to P₀; _⊓_ to _⊓₀_; ⊔_ to ⊔₀_; 𝟏 to 𝟏₀)
  open Frame F₁ using () renaming (P to P₁; _⊓_ to _⊓₁_; ⊔_ to ⊔₁_; 𝟏 to 𝟏₁)

  field
    m : strₚ P₀ ─m→ strₚ P₁

  field
     resp-id : m $ 𝟏₀ ≡ 𝟏₁
     resp-⊓  : (x y : ∣ P₀ ∣ₚ) → m $ (x ⊓₀ y) ≡ (m $ x) ⊓₁ (m $ y)
     resp-⊔  : (ℱ : Sub ℓ₂ ∣ P₀ ∣ₚ) → m $ (⊔₀ ℱ) ≡ (⊔₁ (proj₁ ℱ , λ i → m $ (ℱ € i)))

_$f_ : {F₀ : Frame ℓ ℓ′ ℓ₂} {F₁ : Frame ℓ ℓ′ ℓ₂}
     → (F₀ ─f→ F₁) → (proj₁ (Frame.P F₀)) → (proj₁ (Frame.P F₁))
_$f_ = proj₁ ∘ _─f→_.m

-- An element of the poset is like a finite observation whereas an element of the
-- frame of downward closed posets is like a general observation.

downward : (P : Poset ℓ ℓ′) → Poset (suc ℓ ⊔ ℓ′) ℓ
downward {ℓ = ℓ} {ℓ′} (X , P) = 𝔻 , (posetstr _<<_ A-set <<-refl <<-trans <<-antisym)
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

downward-frame : {ℓ ℓ′ : Level} (P : Poset ℓ ℓ′) → Frame (suc ℓ ⊔ ℓ′) ℓ ℓ
downward-frame {ℓ = ℓ} {ℓ′} (X , P) =
  record
    { P       =  𝔻ₚ
    ; 𝟏       =  𝟏
    ; _⊓_     =  _⊓_
    ; ⊔_      =  ⊔_
    ; top     =  𝟏-top
    ; ⊓-low₁  =  ⊓-low₀
    ; ⊓-low₂  =  ⊓-low₁
    ; ⊓-max   =  ⊓-max
    ; ⊔-up    =  ⊔-up
    ; ⊔-min   =  ⊔-min
    ; dist    =  dist
    }
  where
    𝔻ₚ = downward (X , P)
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
    ∩-down S T S↓ T↓ x y x∈S∩T y⊑x =
      S↓ x y (proj₁ x∈S∩T) y⊑x , T↓ x y (proj₂ x∈S∩T) y⊑x

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

    ⊔-up : (ℱ : Sub ℓ 𝔻) (D : 𝔻) → D ε ℱ → D << (⊔ ℱ) holds
    ⊔-up ℱ D DεS@(i , p) x x∈D = ∣ i , transport (λ - → x ∈ ∣ - ∣𝔻 holds) (sym p) x∈D ∣

    ⊔-min : (ℱ : Sub ℓ 𝔻) (z : 𝔻) → ((o : 𝔻) → o ε ℱ → (o << z) holds) → (⊔ ℱ) << z holds
    ⊔-min ℱ D φ x x∈⊔S = ∥∥-rec (proj₂ (∣ D ∣𝔻 x)) foo x∈⊔S
      where
        foo : Σ[ i ∈ index ℱ ] ∣ ℱ € i ∣𝔻 x holds → x ∈ ∣ D ∣𝔻 holds
        foo (i , x∈ℱᵢ) = φ (ℱ € i) (i , refl) x x∈ℱᵢ

    ⊓-low₀ : (D E : 𝔻) → (D ⊓ E) << D holds
    ⊓-low₀ D E x (x∈D , _) = x∈D

    ⊓-low₁ : (D E : 𝔻) → (D ⊓ E) << E holds
    ⊓-low₁ D E x (_ , x∈F) = x∈F

    ⊓-max : (D E F : 𝔻) → (F << D) holds → (F << E) holds → F << (D ⊓ E) holds
    ⊓-max D E F F<<D F<<E x x∈F = (F<<D x x∈F) , (F<<E x x∈F)

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
        up x x∈ℬ = ∥∥-rec (Σ-resp-prop (holds-prop (x ∈ ∣ D ∣𝔻)) λ _ → holds-prop (x ∈ ∣ ⊔ ℱ ∣𝔻)) lemma x∈ℬ
          where
            lemma : in-some-set-of (index ℱ , λ j → D ⊓ (ℱ € j)) x → Σ (x ∈ ∣ D ∣𝔻 holds) (λ _ → x ∈ ∣ ⊔ ℱ ∣𝔻 holds)
            lemma (i , x∈D , x∈ℱᵢ) = x∈D , ∣ i , x∈ℱᵢ ∣

-- -}
-- -}
-- -}
