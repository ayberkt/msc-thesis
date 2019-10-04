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

downward : {ℓ ℓ′ : Level} (P : Poset ℓ ℓ′) → Poset (suc ℓ ⊔ ℓ′) (ℓ ⊔ ℓ′)
downward {ℓ = ℓ} {ℓ′} (X , P) = A , posetstr _⊑d′_ A-set ⊑d-refl ⊑d-trans {!!}
  where
    open PosetStr P using    (_⊑_)
                    renaming (refl to ⊑-refl; trans to ⊑-trans; sym⁻¹ to ⊑-antisym)
    A = DownwardClosedSubset (X , P)
    A-set : IsSet (DownwardClosedSubset (X , P))
    A-set = DownwardClosedSubset-set (X , P)
    _⊑d_ : A → A → Set (ℓ ⊔ ℓ′)
    _⊑d_ (S , _) (T , _) = (x : X) → x ∈ S → Σ[ y ∈ X ] (y ∈ T × (x ⊑ y) holds)
    ⊑d-prop : (S T : A) → IsProp (S ⊑d T)
    ⊑d-prop S T = {!!}
    open AlgebraicProperties A-set (λ S T → S ⊑d T , ⊑d-prop S T)
       renaming (IsTransitive to IsTransitive-⊑d; IsAntisym to IsAntisym-⊑d)
    _⊑d′_ : A → A → Ω (ℓ ⊔ ℓ′)
    _⊑d′_ S T = S ⊑d T , ⊑d-prop S T
    ⊑d-refl : (S : A) → (S ⊑d′ S) holds
    ⊑d-refl S x x∈S = x , (x∈S , ⊑-refl x)
    ⊑d-trans : IsTransitive-⊑d holds
    ⊑d-trans S T U p q s s∈S with p s s∈S
    ⊑d-trans S T U p q s s∈S | t , t∈T , s⊑t with q t t∈T
    ⊑d-trans S T U p q s s∈S | t , t∈T , s⊑t | u , u∈U , t⊑u =
      u , u∈U , (⊑-trans s t u s⊑t t⊑u)
    ⊑d-antisym : IsAntisym-⊑d holds
    ⊑d-antisym S T S⊑T T⊑S =
      to-subtype-≡ (proj₂ ∘ IsDownwardClosed (X , P)) (subsetext S⊆T T⊆S)
        where
          S⊆T : (proj₁ S) ⊆ (proj₁ T)
          S⊆T s s∈S with S⊑T s s∈S
          S⊆T s s∈S | t , t∈T , s⊑t with T⊑S t t∈T
          S⊆T s s∈S | t , t∈T , s⊑t | s′ , s′∈S , t⊑s′ = {!!}
          T⊆S : (proj₁ T) ⊆ (proj₁ S)
          T⊆S t t∈S = {!!}
