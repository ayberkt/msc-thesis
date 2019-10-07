module Frame where

open import Level
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Product                          using (Σ-syntax; _×_; _,_; proj₁; proj₂)
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

-- -}
-- -}
-- -}
