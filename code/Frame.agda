module Frame where

open import Level
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Product                          using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Unit                                  using (tt)
open import Function                              using (_∘_)
import AlgebraicProperties
open import Homotopy
-- open import Subset                                using (SubP)
open import Poset

Sub : {ℓ : Level} → Set ℓ → Set (suc ℓ)
Sub {ℓ} A = Σ[ I ∈ Set ℓ ] (I → A)

record Frame (ℓ ℓ′ : Level) : Set (suc ℓ ⊔ suc ℓ′) where

  field
    P   : Poset ℓ ℓ′

  O   = proj₁ P
  _⊑_ = PosetStr._⊑_ (proj₂ P)

  field
    𝟏   : O
    _⊓_ : O → O → O
    ⊔_  : Sub O → O

  field
    top    : (x     : O)         → (x ⊑ 𝟏) holds
    -- Consider merging the following three requirements alternate between this
    -- using univalence.
    ⊓-low₁ : (x y   : O)         → ((x ⊓ y) ⊑ x) holds
    ⊓-low₂ : (x y   : O)         → ((x ⊓ y) ⊑ y) holds
    ⊓-max  : (x y z : O)         → (z ⊑ x) holds → (z ⊑ y) holds → (z ⊑ (x ⊓ y)) holds
    ⊔-up   : (S     : Sub O)     → (o : O) → (o ⊑ (⊔ S)) holds
    ⊔-min  : (S     : Sub O)     → (z : O) → ((o : O) → (o ⊑ z) holds) → ((⊔ S) ⊑ z) holds
    dist   : (x : O) (S : Sub O) → x ⊓ (⊔ S) ≡ ⊔ (proj₁ S , λ i → x ⊓ proj₂ S i)

record _─f→_ {ℓ ℓ′ : Level} (F₀ : Frame ℓ ℓ′) (F₁ : Frame ℓ ℓ′) : Set (suc ℓ ⊔ ℓ′) where
  open Frame F₀ using () renaming (P to P₀; _⊓_ to _⊓₀_; ⊔_ to ⊔₀_; 𝟏 to 𝟏₀)
  open Frame F₁ using () renaming (P to P₁; _⊓_ to _⊓₁_; ⊔_ to ⊔₁_; 𝟏 to 𝟏₁)
  A₀ = proj₁ P₀
  A₁ = proj₁ P₁

  field
    m : (proj₂ P₀) ─m→ (proj₂ P₁)

  field
     resp-id : m $ 𝟏₀ ≡ 𝟏₁
     resp-⊓  : (x y : A₀) → m $ (x ⊓₀ y) ≡ (m $ x) ⊓₁ (m $ y)
     resp-⊔  : (ℱ : Sub A₀) → m $ (⊔₀ ℱ) ≡ (⊔₁ (proj₁ ℱ , λ i → m $ (proj₂ ℱ i)))

_$f_ : {ℓ ℓ′ : Level} {F₀ : Frame ℓ ℓ′} {F₁ : Frame ℓ ℓ′}
     → (F₀ ─f→ F₁) → (proj₁ (Frame.P F₀)) → (proj₁ (Frame.P F₁))
_$f_ = proj₁ ∘ _─f→_.m

-- An element of the poset is like a finite observation whereas an element of the
-- frame of downward closed posets is like a general observation.

downward : {ℓ ℓ′ : Level} (P : Poset ℓ ℓ′) → Poset (suc ℓ ⊔ ℓ′) ℓ
downward {ℓ = ℓ} {ℓ′} (X , P) = A , (posetstr _<<_ A-set <<-refl <<-trans <<-antisym)
  where
    open PosetStr P using    (_⊑_)
                    renaming (refl to ⊑-refl; trans to ⊑-trans; sym⁻¹ to ⊑-antisym)
    A = DownwardClosedSubset (X , P)
    A-set : IsSet (DownwardClosedSubset (X , P))
    A-set = DownwardClosedSubset-set (X , P)
    inc : A → A → Set ℓ
    inc (S , _) (T , _) = S ⊆ T
    <<-prop : (S T : A) → IsProp (inc S T)
    <<-prop (S , _) (T , _) = ⊆-prop S T
    open AlgebraicProperties A-set (λ S T → inc S T , <<-prop S T)
       renaming (IsReflexive to <<-IsReflexive; IsTransitive to <<-IsTransitive; IsAntisym to <<-IsAntisym)
    _<<_ : A → A → Ω ℓ
    S << T = (inc S T) , (<<-prop S T)
    <<-refl : <<-IsReflexive holds
    <<-refl = ⊆-refl ∘ proj₁
    <<-trans : <<-IsTransitive holds
    <<-trans (S , _) (T , _) (U , _) = ⊆-trans S T U
    <<-antisym : <<-IsAntisym holds
    <<-antisym (S , _) (T , _) S⊆T T⊆S =
      to-subtype-≡ (holds-prop ∘ IsDownwardClosed (X , P)) (⊆-antisym S⊆T T⊆S)

downward-frame : {ℓ ℓ′ : Level} (P : Poset ℓ ℓ′) → Frame {!!} {!!}
downward-frame {ℓ = ℓ} {ℓ′} (X , P) =
  record
    { P       =  downward (X , P)
    ; 𝟏       =  𝟏
    ; _⊓_     =  _⊓_
    ; ⊔_      =  {!!}
    ; top     =  𝟏-top
    ; ⊓-low₁  =  ⊓-low₀
    ; ⊓-low₂  =  ⊓-low₁
    ; ⊓-max   =  ⊓-max
    ; ⊔-up    =  {!!}
    ; ⊔-min   =  {!!}
    ; dist    =  {!!}
    }
  where
    𝔻 = ∣ downward (X , P) ∣
    open PosetStr (proj₂ (downward (X , P))) renaming (_⊑_ to _<<_)
    𝟏 = entirety , λ _ _ _ _ → tt
    ∩-down : (S T : 𝒫 X)
           → IsDownwardClosed (X , P) S       holds
           → IsDownwardClosed (X , P) T       holds
           → IsDownwardClosed (X , P) (S ∩ T) holds
    ∩-down S T S-dc T-dc x y x∈S∩T y⊑x = S-dc x y (proj₁ x∈S∩T) y⊑x , T-dc x y (proj₂ x∈S∩T) y⊑x
    _⊓_ : 𝔻 → 𝔻 → 𝔻
    (S , S-dc) ⊓ (T , T-dc) = (S ∩ T) , ∩-down S T S-dc T-dc
    𝟏-top : (D : ∣ downward (X , P) ∣) → (D << 𝟏) holds
    𝟏-top D _ _ = tt
    ⊓-low₀ : (D E : 𝔻) → ((D ⊓ E) << D) holds
    ⊓-low₀ D E x (x∈D , _) = x∈D
    ⊓-low₁ : (D E : 𝔻) → ((D ⊓ E) << E) holds
    ⊓-low₁ D E x (_ , x∈F) = x∈F
    ⊓-max : (D E F : 𝔻) → (F << D) holds → (F << E) holds → (F << (D ⊓ E)) holds
    ⊓-max D E F F<<D F<<E x x∈F = (F<<D x x∈F) , (F<<E x x∈F)

-- -}
-- -}
-- -}
