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

-- A predicate expressing whether a function is a nucleus.
IsNuclear : (L : Frame ℓ₀ ℓ₁ ℓ₂) → (∣ L ∣F → ∣ L ∣F) → Set (ℓ₀ ⊔ ℓ₁)
IsNuclear L j = N₀ × N₁ × N₂ × N₃
  where
    open Frame L using (P; _⊓_; _⊑_)
    N₀ = (a b : ∣ L ∣F) → j (a ⊓ b) ≡ (j a) ⊓ (j b)
    N₁ = (a   : ∣ L ∣F) → a ⊑ (j a) holds
    N₂ = (a   : ∣ L ∣F) → j (j a) ⊑ j a holds
    N₃ = (a b : ∣ L ∣F) → a ⊑ b holds → j a ⊑ j b holds

-- The type of nuclei.
Nucleus : Frame ℓ₀ ℓ₁ ℓ₂ → Set (ℓ₀ ⊔ ℓ₁)
Nucleus L = Σ (∣ L ∣F → ∣ L ∣F) (IsNuclear L)

idem : (L : Frame ℓ₀ ℓ₁ ℓ₂)
     → (N : Nucleus L)
     → let j = proj₁ N in (x : ∣ L ∣F) → j (j x) ≡ j x
idem L (j , n₀ , n₁ , n₂ , n₃) x = ⊑-antisym (j (j x)) (j x) (n₂ x) (n₁ (j x))
  where
    open PosetStr (proj₂ (Frame.P L)) using (_⊑_; ⊑-antisym)

-- The set of fixed points for nucleus `j` is equivalent hence equal to its image.
-- This is essentially due to the fact that j (j ())
nuclear-image : (L : Frame ℓ₀ ℓ₁ ℓ₂)
              → let ∣L∣ = ∣ L ∣F in (j : ∣L∣ → ∣L∣)
              → IsNuclear L j
              → (Σ[ b ∈ ∣L∣ ] ∥ Σ[ a ∈ ∣L∣ ] (b ≡ j a) ∥) ≡ (Σ[ a ∈ ∣L∣ ] (j a ≡ a))
nuclear-image L j N@(n₀ , n₁ , n₂ , n₃) = equivtoid (invertibility→≃ f (g , lc , rc))
  where
    open Frame L            using (P)
    open PosetStr (proj₂ P) using (A-set; ⊑-antisym; ⊑-refl)

    f : (Σ[ b ∈ ∣ L ∣F ] ∥ Σ[ a ∈ ∣ L ∣F ] (b ≡ j a) ∥) → Σ[ a ∈ ∣ L ∣F ] (j a ≡ a)
    f (b , img) = b , ∥∥-rec (A-set (j b) b) ind img
      where
        ind : Σ[ a ∈ ∣ L ∣F ](b ≡ j a) → j b ≡ b
        ind (a , img) =
          j b     ≡⟨ cong j img ⟩
          j (j a) ≡⟨ idem L (j , N) a ⟩
          j a     ≡⟨ sym img ⟩
          b       ∎

    g : (Σ[ a ∈ ∣ L ∣F ] (j a ≡ a)) → (Σ[ b ∈ ∣ L ∣F ] ∥ Σ[ a ∈ ∣ L ∣F ] (b ≡ j a) ∥)
    g (a , a-fix) = a , ∣ a , (sym a-fix) ∣

    lc : (x : Σ ∣ L ∣F (λ b → ∥ Σ-syntax ∣ L ∣F (λ a → b ≡ j a) ∥)) → g (f x) ≡ x
    lc (a , img) = to-subtype-≡ (λ _ → ∥∥-prop _) refl

    rc : (x : Σ ∣ L ∣F (λ y → j y ≡ y)) → f (g x) ≡ x
    rc (a , _) = to-subtype-≡ (λ x → A-set (j x) x) refl

-- The set of fixed points for a nucleus `j` forms a poset.
nuclear-fixed-point-poset : (L : Frame ℓ₀ ℓ₁ ℓ₂) → (N : Nucleus L) → Poset ℓ₀ ℓ₁
nuclear-fixed-point-poset {ℓ₀ = ℓ₀} {ℓ₁} L (j , n₀ , n₁ , n₂) =
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

nuclear-fixed-point-frame : (L : Frame ℓ₀ ℓ₁ ℓ₂) → (N : Nucleus L) → Frame ℓ₀ ℓ₁ ℓ₂
nuclear-fixed-point-frame {ℓ₂ = ℓ₂} L N@(j , n₀ , n₁ , n₂ , n₃) =
  record
    { P          =  nuclear-fixed-point-poset L N
    ; 𝟏          =  𝟏L , 𝟏-fixed
    ; _⊓_        =  _⊓_
    ; ⊔_         =  ⊔_
    ; top        =  top
    ; ⊓-lower₀   =  ⊓-lower₀
    ; ⊓-lower₁   =  ⊓-lower₁
    ; ⊓-greatest =  ⊓-greatest
    ; ⊔-upper    =  ⊔-upper
    ; ⊔-least    =  ⊔-least
    ; dist       =  dist
    }
  where
    A = proj₁ (nuclear-fixed-point-poset L N)
    open PosetStr (proj₂ (Frame.P L))
      using (_⊑_; ⊑-antisym; ⊑-refl; _⊑⟨_⟩_; _■) renaming (A-set to X-set)
    open PosetStr (proj₂ (nuclear-fixed-point-poset L N))
      using (A-set) renaming ( _⊑_ to _⊑N_; ⊑-antisym to ⊑N-antisym)
    open Frame L using (P) renaming ( 𝟏          to 𝟏L
                                    ; _⊓_        to _⊓L_
                                    ; ⊔_         to ⊔L_
                                    ; top        to topL
                                    ; ⊓-greatest to ⊓L-greatest
                                    ; ⊓-lower₀   to ⊓L-lower₀
                                    ; ⊓-lower₁   to ⊓L-lower₁
                                    ; ⊔-least    to ⊔L-least
                                    ; ⊔-upper    to ⊔L-upper
                                    ; dist       to distL)
    𝟏-fixed : j 𝟏L ≡ 𝟏L
    𝟏-fixed = ⊑-antisym (j 𝟏L) 𝟏L (topL (j 𝟏L)) (n₁ 𝟏L)

    _⊓_ : A → A → A
    _⊓_ (x , x-f) (y , y-f) = x ⊓L y , ⊑-antisym (j (x ⊓L y)) (x ⊓L y) φ (n₁ (x ⊓L y))
      where
        ⊑jx : j (x ⊓L y) ⊑ j x holds
        ⊑jx = j (x ⊓L y) ⊑⟨ ≡⇒⊑ P (n₀ x y) ⟩ j x ⊓L j y ⊑⟨ ⊓L-lower₀ (j x) (j y) ⟩ j x ■
        ⊑jy : j (x ⊓L y) ⊑ j y holds
        ⊑jy = j (x ⊓L y) ⊑⟨ ≡⇒⊑ P (n₀ x y) ⟩ j x ⊓L j y ⊑⟨ ⊓L-lower₁ (j x) (j y) ⟩ j y ■

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

    ⊔-least : (ℱ : Sub ℓ₂ A) (p : A)
            → ((o : A) → o ε ℱ → o ⊑N p holds) → ((⊔ ℱ) ⊑N p) holds
    ⊔-least ℱ p@(p′ , eq) ℱ⊑p = φ
      where
        𝒢 : Sub ℓ₂ ∣ P ∣ₚ
        𝒢 = index ℱ , λ i → proj₁ (ℱ € i)

        ϑ : (o : ∣ P ∣ₚ) → o ε 𝒢 → o ⊑ p′ holds
        ϑ o o∈𝒢@(i , eq′) rewrite sym eq′ = ℱ⊑p (𝒢 € i , proj₂ (ℱ € i)) (i , refl)

        ψ : j (⊔L 𝒢) ⊑ (j p′) holds
        ψ = n₃ (⊔L 𝒢) p′ (⊔L-least 𝒢 p′ ϑ)

        φ : j (⊔L 𝒢) ⊑ p′ holds
        φ = transport (λ k → (j (⊔L 𝒢) ⊑ k) holds) eq ψ

    ⊔-upper : (ℱ : Sub ℓ₂ A) (o : A) → o ε ℱ → (o ⊑N (⊔ ℱ)) holds
    ⊔-upper ℱ (o , _) o∈ℱ@(i , eq) =
      o                  ⊑⟨ φ ⟩
      ⊔L (proj₁ ⊚ ℱ)     ⊑⟨ n₁ (⊔L (proj₁ ⊚ ℱ)) ⟩
      j (⊔L (proj₁ ⊚ ℱ)) ■
      where
        φ : o ⊑ (⊔L (proj₁ ⊚ ℱ)) holds
        φ = ⊔L-upper (proj₁ ⊚ ℱ) o (i , Σ-resp₀ o _ _ eq)

    dist : (o : A) (ℱ : Sub ℓ₂ A) → o ⊓ (⊔ ℱ) ≡ ⊔ (index ℱ , (λ i → o ⊓ (ℱ € i)))
    dist o@(o′ , j-fix-o′) ℱ@(I , F) = Σ= _ (idem L N _) φ (X-set _ _ _ _)
      where
        𝒢 : Sub ℓ₂ ∣ P ∣ₚ
        𝒢 = proj₁ ⊚ ℱ

        φ :  proj₁ (o ⊓ (⊔ ℱ)) ≡ proj₁ (⊔ (I , (λ i → o ⊓ (ℱ € i))))
        φ =
          proj₁ (o ⊓ (⊔ ℱ))                   ≡⟨ refl                                     ⟩
          o′ ⊓L j (⊔L 𝒢)                      ≡⟨ cong (λ - → - ⊓L j (⊔L 𝒢)) (j-fix-o′ ⁻¹) ⟩
          j o′ ⊓L (j (⊔L 𝒢))                  ≡⟨ sym (n₀ o′ (⊔L 𝒢))                       ⟩
          j (o′ ⊓L (⊔L 𝒢))                    ≡⟨ cong j (distL o′ 𝒢)                      ⟩
          j (⊔L (I , (λ i → o′ ⊓L (𝒢 € i))))  ≡⟨ refl                                     ⟩
          proj₁ (⊔ (I , (λ i → o ⊓ (ℱ € i)))) ∎
