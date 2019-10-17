{-# OPTIONS --without-K #-}

open import Truncation

module Nucleus (pt : TruncationExists) where

open import Common
open import Homotopy
open import Poset
open import Frame pt
import AlgebraicProperties

open TruncationExists pt

private
  variable
    ℓ₀ ℓ₁ ℓ₂ : Level
    L : Frame ℓ₀ ℓ₁ ℓ₂

IsNuclear : (L : Frame ℓ₀ ℓ₁ ℓ₂) → (∣ L ∣F → ∣ L ∣F) → Set (ℓ₀ ⊔ ℓ₁)
IsNuclear L j = N₀ × N₁ × N₂
  where
    open Frame L using (P; _⊓_; _⊑_)
    N₀ = (a b : ∣ L ∣F) → j (a ⊓ b) ≡ (j a) ⊓ (j b)
    N₁ = (a   : ∣ L ∣F) → a ⊑ (j a) holds
    N₂ = (a   : ∣ L ∣F) → j (j a) ⊑ j a holds

Nucleus : Frame ℓ₀ ℓ₁ ℓ₂ → Set (ℓ₀ ⊔ ℓ₁)
Nucleus L = Σ (∣ L ∣F → ∣ L ∣F) (IsNuclear L)

IsInvertible : {X : Set ℓ₀} {Y : Set ℓ₁} → (X → Y) → Set (ℓ₀ ⊔ ℓ₁)
IsInvertible {X = X} {Y} f = Σ[ g ∈ (Y → X) ] (g ∘ f) ~ id × (f ∘ g) ~ id

postulate
  invertible⇒equiv : {X : Set ℓ₀} {Y : Set ℓ₁} → (f : X → Y) → IsInvertible f → isequiv f

invertibility→≃ : {X : Set ℓ₀} {Y : Set ℓ₁} (f : X → Y) → IsInvertible f → X ≃ Y
invertibility→≃ f inv = f , (invertible⇒equiv f inv)

nuclear-image : (L : Frame ℓ₀ ℓ₁ ℓ₂)
              → let ∣L∣ = ∣ L ∣F in (j : ∣L∣ → ∣L∣)
              → IsNuclear L j
              → (Σ[ b ∈ ∣L∣ ] ∥ Σ[ a ∈ ∣L∣ ] (b ≡ j a) ∥) ≡ (Σ[ a ∈ ∣L∣ ] (j a ≡ a))
nuclear-image L j (n₀ , n₁ , n₂) = equivtoid (invertibility→≃ f (g , lc , rc))
  where
    open Frame L using (P)
    open PosetStr (proj₂ P) using (A-set; ⊑-antisym; ⊑-refl)
    f : (Σ[ b ∈ ∣ L ∣F ] ∥ Σ[ a ∈ ∣ L ∣F ] (b ≡ j a) ∥) → (Σ[ a ∈ ∣ L ∣F ] (j a ≡ a))
    f (b , img) = b , ∥∥-rec (A-set (j b) b) ind img
      where
        ind : Σ[ a ∈ ∣ L ∣F ](b ≡ j a) → j b ≡ b
        ind (a , img) =
          j b     ≡⟨ cong j img ⟩
          j (j a) ≡⟨ ⊑-antisym (j (j a)) (j a) (n₂ a) (n₁ (j a)) ⟩
          j a     ≡⟨ sym img ⟩
          b       ∎
    g : (Σ[ a ∈ ∣ L ∣F ] (j a ≡ a)) → (Σ[ b ∈ ∣ L ∣F ] ∥ Σ[ a ∈ ∣ L ∣F ] (b ≡ j a) ∥)
    g (a , a-fix) = a , ∣ a , (sym a-fix) ∣
    lc : ∀ x → g (f x) ≡ x
    lc (a , img) = to-subtype-≡ (λ _ → ∥∥-prop _) refl
    rc : ∀ x → f (g x) ≡ x
    rc (a , a-fixed) = to-subtype-≡ (λ x → A-set (j x) x) refl

nuclear-poset : (L : Frame ℓ₀ ℓ₁ ℓ₂) → (N : Nucleus L) → Poset ℓ₀ ℓ₁
nuclear-poset {ℓ₀ = ℓ₀} {ℓ₁} L (j , n₀ , n₁ , n₂) =
  𝔽 , posetstr _≤_ 𝔽-set ≤-refl ≤-trans ≤-antisym
  where
    open Frame L            using (P)
    open PosetStr (proj₂ P) using (A-set; _⊑_; ⊑-refl; ⊑-trans; ⊑-antisym)

    𝔽 : Set ℓ₀
    𝔽 = Σ[ a ∈ ∣ L ∣F ] j a ≡ a

    𝔽-set : IsSet 𝔽
    𝔽-set = Σ-set A-set (λ a → prop⇒set (A-set (j a) a))

    _≤_ : 𝔽 → 𝔽 → Ω ℓ₁
    (a , _) ≤ (b , _) = a ⊑ b holds , holds-prop (a ⊑ b)

    open AlgebraicProperties 𝔽-set _≤_

    ≤-refl : IsReflexive holds
    ≤-refl (x , _) = ⊑-refl x

    ≤-trans : IsTransitive holds
    ≤-trans (x , _) (y , _) (z , _) x≤y y≤x = ⊑-trans x y z x≤y y≤x

    ≤-antisym : IsAntisym holds
    ≤-antisym (x , _) (y , _) x≤y y≤x =
      to-subtype-≡ (λ z → A-set (j z) z) (⊑-antisym x y x≤y y≤x)

nuclear-frame : (L : Frame ℓ₀ ℓ₁ ℓ₂) → (N : Nucleus L) → Frame ℓ₀ ℓ₁ ℓ₂
nuclear-frame {ℓ₂ = ℓ₂} L N@(j , n₀ , n₁ , n₂) =
  record
    { P          =  nuclear-poset L N
    ; 𝟏          =  𝟏L , 𝟏-fixed
    ; _⊓_        =  _⊓_
    ; ⊔_         =  ⊔_
    ; top        =  top
    ; ⊓-lower₀   =  ⊓-lower₀
    ; ⊓-lower₁   =  ⊓-lower₁
    ; ⊓-greatest =  ⊓-greatest
    ; ⊔-upper    =  {!!}
    ; ⊔-least    =  {!!}
    ; dist       =  {!!}
    }
  where
    A = proj₁ (nuclear-poset L N)
    open PosetStr (proj₂ (Frame.P L)) using (_⊑_; ⊑-antisym; ⊑-refl; ⊑-trans)
    open PosetStr (proj₂ (nuclear-poset L N)) using () renaming (_⊑_ to _⊑N_)
    open Frame L using (P) renaming (𝟏 to 𝟏L; _⊓_ to _⊓L_; ⊔_ to ⊔L_; top to topL
                                    ; ⊓-greatest to ⊓L-greatest
                                    ; ⊓-lower₀ to ⊓L-lower₀
                                    ; ⊓-lower₁ to ⊓L-lower₁
                                    ; ⊔-least  to ⊔L-least
                                    ; ⊔-upper  to ⊔L-upper)
    𝟏-fixed : j 𝟏L ≡ 𝟏L
    𝟏-fixed = ⊑-antisym (j 𝟏L) 𝟏L (topL (j 𝟏L)) (n₁ 𝟏L)

    _⊓_ : A → A → A
    _⊓_ (x , x-f) (y , y-f) = x ⊓L y , ⊑-antisym (j (x ⊓L y)) (x ⊓L y) φ (n₁ (x ⊓L y))
      where
        ⊑jx : j (x ⊓L y) ⊑ j x holds
        ⊑jx = ⊑-trans _ (j x ⊓L j y) _ (≡⇒⊑ P (n₀ x y)) (⊓L-lower₀ (j x) (j y))
        ⊑jy : j (x ⊓L y) ⊑ j y holds
        ⊑jy = ⊑-trans _ (j x ⊓L j y) _ (≡⇒⊑ P (n₀ x y)) (⊓L-lower₁ (j x) (j y))

        ⊑x : j (x ⊓L y) ⊑ x holds
        ⊑x = transport (λ z → j (x ⊓L y) ⊑ z holds) x-f ⊑jx
        ⊑y : j (x ⊓L y) ⊑ y holds
        ⊑y = transport (λ z → j (x ⊓L y) ⊑ z holds) y-f ⊑jy

        φ : j (x ⊓L y) ⊑ (x ⊓L y) holds
        φ = ⊓L-greatest x y (j (x ⊓L y)) ⊑x ⊑y

    ⊔_ : Sub ℓ₂ A → A
    ⊔ (I , F) = j (⊔L 𝒢) , j⊔L-fixed
      where
        𝒢 = I , proj₁ ∘ F
        j⊔L-fixed : j (j (⊔L 𝒢)) ≡ j (⊔L 𝒢)
        j⊔L-fixed = ⊑-antisym (j (j (⊔L 𝒢))) (j (⊔L 𝒢)) (n₂ (⊔L 𝒢)) (n₁ (j (⊔L 𝒢)))

    top : (o : A) → (o ⊑N (𝟏L , 𝟏-fixed)) holds
    top = topL ∘ proj₁

    ⊓-lower₀ : (o p : A) → (o ⊓ p) ⊑N o holds
    ⊓-lower₀ (o , _) (p , _) = ⊓L-lower₀ o p

    ⊓-lower₁ : (o p : A) → (o ⊓ p) ⊑N p holds
    ⊓-lower₁ (o , _) (p , _) = ⊓L-lower₁ o p

    ⊓-greatest : (o p q : A) → q ⊑N o holds → q ⊑N p holds → q ⊑N (o ⊓ p) holds
    ⊓-greatest (o , _) (p , _) (q , _) q⊑o q⊑p = ⊓L-greatest o p q q⊑o q⊑p
