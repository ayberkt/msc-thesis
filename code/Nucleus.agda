{-# OPTIONS --without-K --cubical --safe #-}

open import Truncation

module Nucleus where

open import Basis
open import Family
open import Poset
open import Frame
import AlgebraicProperties

-- A predicate expressing whether a function is a nucleus.
IsNuclear : (L : Frame ℓ₀ ℓ₁ ℓ₂) → (∣ L ∣F → ∣ L ∣F) → Set (ℓ₀ ⊔ ℓ₁)
IsNuclear L j = N₀ × N₁ × N₂
  where
    open Frame.Frame L using (P; _⊓_; _⊑_)
    N₀ = (a b : ∣ L ∣F) → j (a ⊓ b) ≡ (j a) ⊓ (j b)
    N₁ = (a   : ∣ L ∣F) → a ⊑ (j a) is-true
    N₂ = (a   : ∣ L ∣F) → j (j a) ⊑ j a is-true

-- The type of nuclei.
Nucleus : Frame ℓ₀ ℓ₁ ℓ₂ → Set (ℓ₀ ⊔ ℓ₁)
Nucleus L = Σ (∣ L ∣F → ∣ L ∣F) (IsNuclear L)

idem : (L : Frame ℓ₀ ℓ₁ ℓ₂)
     → (N : Nucleus L)
     → let j = π₀ N in (x : ∣ L ∣F) → j (j x) ≡ j x
idem L (j , n₀ , n₁ , n₂) x = ⊑-antisym (j (j x)) (j x) (n₂ x) (n₁ (j x))
  where
    open PosetStr (strₚ (Frame.P L)) using (_⊑_; ⊑-antisym)

mono : (L : Frame ℓ₀ ℓ₁ ℓ₂) → (N : Nucleus L)
     → let j = π₀ N
       in (x y : ∣ L ∣F) → x ⊑[ pos L ] y is-true → (j x) ⊑[ pos L ] (j y) is-true
mono L (j , n₀ , n₁ , n₂) x y x⊑y =
  j x         ⊑⟨ ≡⇒⊑ (pos L) (cong j x≡x⊓y) ⟩
  j (x ⊓ y)   ⊑⟨ ≡⇒⊑ (pos L) (n₀ x y) ⟩
  j x ⊓ j y   ⊑⟨ ⊓-lower₁ (j x) (j y) ⟩
  j y         ■
  where
    open PosetStr (strₚ (pos L))  using (_⊑_; ⊑-trans; ⊑-refl; ⊑-antisym; _⊑⟨_⟩_; _■)
    open Frame.Frame    L         using (𝟏; _⊓_; ⊓-greatest; ⊓-lower₀; ⊓-lower₁; top)

    x⊑x⊓y : x ⊑ (x ⊓ y) is-true
    x⊑x⊓y = ⊓-greatest x y x (⊑-refl x) x⊑y

    x≡x⊓y : x ≡ (x ⊓ y)
    x≡x⊓y = ⊑-antisym x (x ⊓ y) x⊑x⊓y (⊓-lower₀ x y)

-- The set of fixed points for nucleus `j` is equivalent hence equal to its image.
-- This is essentially due to the fact that j (j ())
nuclear-image : (L : Frame ℓ₀ ℓ₁ ℓ₂)
              → let ∣L∣ = ∣ L ∣F in (j : ∣L∣ → ∣L∣)
              → IsNuclear L j
              → (Σ[ b ∈ ∣L∣ ] ∥ Σ[ a ∈ ∣L∣ ] (b ≡ j a) ∥) ≡ (Σ[ a ∈ ∣L∣ ] (j a ≡ a))
nuclear-image L j N@(n₀ , n₁ , n₂) = isoToPath (iso f g sec-f-g ret-f-g)
  where
    open Frame.Frame L      using (P)
    open PosetStr (π₁ P) using (A-set; ⊑-antisym; ⊑-refl)

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

    sec-f-g : section f g
    sec-f-g (x , jx=x) = ΣProp≡ (λ y → A-set (j y) y) refl

    ret-f-g : retract f g
    ret-f-g (x , p) = ΣProp≡ (λ y → ∥∥-prop (Σ[ a ∈ ∣ L ∣F ] y ≡ j a)) refl

-- The set of fixed points for a nucleus `j` forms a poset.
nuclear-fixed-point-poset : (L : Frame ℓ₀ ℓ₁ ℓ₂) → (N : Nucleus L) → Poset ℓ₀ ℓ₁
nuclear-fixed-point-poset {ℓ₀ = ℓ₀} {ℓ₁} L (j , n₀ , n₁ , n₂) =
  𝔽 , posetstr _≤_ 𝔽-set ≤-refl ≤-trans ≤-antisym
  where
    open Frame.Frame L   using (P)
    open PosetStr (π₁ P) using (A-set; _⊑_; ⊑-refl; ⊑-trans; ⊑-antisym)

    𝔽 : Set ℓ₀
    𝔽 = Σ[ a ∈ ∣ L ∣F ] j a ≡ a

    𝔽-set : IsSet 𝔽
    𝔽-set = Σ-set A-set (λ a → prop⇒set (A-set (j a) a))

    _≤_ : 𝔽 → 𝔽 → Ω ℓ₁
    (a , _) ≤ (b , _) = a ⊑ b is-true , is-true-prop (a ⊑ b)

    open AlgebraicProperties 𝔽-set _≤_

    ≤-refl : IsReflexive is-true
    ≤-refl (x , _) = ⊑-refl x

    ≤-trans : IsTransitive is-true
    ≤-trans (x , _) (y , _) (z , _) x≤y y≤x = ⊑-trans x y z x≤y y≤x

    ≤-antisym : IsAntisym is-true
    ≤-antisym (x , _) (y , _) x≤y y≤x =
      ΣProp≡ (λ z → A-set (j z) z) (⊑-antisym x y x≤y y≤x)

-- The set of fixed points of a nucleus `j` forms a frame.
-- The join of this frame is define as ⊔ᵢ ℱᵢ := j (⊔′ᵢ ℱᵢ) where ⊔′ denotes the join of L.
nuclear-fixed-point-frame : (L : Frame ℓ₀ ℓ₁ ℓ₂) → (N : Nucleus L) → Frame ℓ₀ ℓ₁ ℓ₂
nuclear-fixed-point-frame {ℓ₂ = ℓ₂} L N@(j , n₀ , n₁ , n₂) =
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
    𝒜 = π₀ (nuclear-fixed-point-poset L N)

    open PosetStr (π₁ (Frame.P L))
      using (_⊑_; ⊑-antisym; ⊑-refl; _⊑⟨_⟩_; _■) renaming (A-set to X-set)
    open PosetStr (π₁ (nuclear-fixed-point-poset L N))
      using (A-set) renaming ( _⊑_ to _⊑N_; ⊑-antisym to ⊑N-antisym)
    open Frame.Frame L using (P) renaming ( 𝟏          to 𝟏L
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

    _⊓_ : 𝒜 → 𝒜 → 𝒜
    _⊓_ (x , x-f) (y , y-f) = x ⊓L y , ⊑-antisym (j (x ⊓L y)) (x ⊓L y) φ (n₁ (x ⊓L y))
      where
        ⊑jx : j (x ⊓L y) ⊑ j x is-true
        ⊑jx = j (x ⊓L y) ⊑⟨ ≡⇒⊑ P (n₀ x y) ⟩ j x ⊓L j y ⊑⟨ ⊓L-lower₀ (j x) (j y) ⟩ j x ■
        ⊑jy : j (x ⊓L y) ⊑ j y is-true
        ⊑jy = j (x ⊓L y) ⊑⟨ ≡⇒⊑ P (n₀ x y) ⟩ j x ⊓L j y ⊑⟨ ⊓L-lower₁ (j x) (j y) ⟩ j y ■

        ⊑x : j (x ⊓L y) ⊑ x is-true
        ⊑x = subst (λ z → j (x ⊓L y) ⊑ z is-true) x-f ⊑jx
        ⊑y : j (x ⊓L y) ⊑ y is-true
        ⊑y = subst (λ z → j (x ⊓L y) ⊑ z is-true) y-f ⊑jy

        φ : j (x ⊓L y) ⊑ (x ⊓L y) is-true
        φ = ⊓L-greatest x y (j (x ⊓L y)) ⊑x ⊑y

    ⊔_ : Sub ℓ₂ 𝒜 → 𝒜
    ⊔ (I , F) = j (⊔L 𝒢) , j⊔L-fixed
      where
        𝒢 = I , π₀ ∘ F
        j⊔L-fixed : j (j (⊔L 𝒢)) ≡ j (⊔L 𝒢)
        j⊔L-fixed = ⊑-antisym (j (j (⊔L 𝒢))) (j (⊔L 𝒢)) (n₂ (⊔L 𝒢)) (n₁ (j (⊔L 𝒢)))

    top : (o : 𝒜) → (o ⊑N (𝟏L , 𝟏-fixed)) is-true
    top = topL ∘ π₀

    ⊓-lower₀ : (o p : 𝒜) → (o ⊓ p) ⊑N o is-true
    ⊓-lower₀ (o , _) (p , _) = ⊓L-lower₀ o p

    ⊓-lower₁ : (o p : 𝒜) → (o ⊓ p) ⊑N p is-true
    ⊓-lower₁ (o , _) (p , _) = ⊓L-lower₁ o p

    ⊓-greatest : (o p q : 𝒜) → q ⊑N o is-true → q ⊑N p is-true → q ⊑N (o ⊓ p) is-true
    ⊓-greatest (o , _) (p , _) (q , _) q⊑o q⊑p = ⊓L-greatest o p q q⊑o q⊑p

    ⊔-least : (ℱ : Sub ℓ₂ 𝒜) (p : 𝒜)
            → ((o : 𝒜) → o ε ℱ → o ⊑N p is-true) → ((⊔ ℱ) ⊑N p) is-true
    ⊔-least ℱ p@(p′ , eq) ℱ⊑p = φ
      where
        𝒢 : Sub ℓ₂ ∣ P ∣ₚ
        𝒢 = index ℱ , λ i → π₀ (ℱ € i)

        ϑ : (o : ∣ P ∣ₚ) → o ε 𝒢 → o ⊑ p′ is-true
        ϑ o o∈𝒢@(i , eq′) = o     ⊑⟨ ≡⇒⊑ P (sym eq′)                     ⟩
                            𝒢 € i ⊑⟨ ℱ⊑p (𝒢 € i , π₁ (ℱ € i)) (i , refl) ⟩
                            p′    ■

        ψ : j (⊔L 𝒢) ⊑ (j p′) is-true
        ψ = mono L N (⊔L 𝒢) p′ (⊔L-least 𝒢 p′ ϑ)

        φ : j (⊔L 𝒢) ⊑ p′ is-true
        φ = subst (λ k → (j (⊔L 𝒢) ⊑ k) is-true) eq ψ

    ⊔-upper : (ℱ : Sub ℓ₂ 𝒜) (o : 𝒜) → o ε ℱ → (o ⊑N (⊔ ℱ)) is-true
    ⊔-upper ℱ (o , _) o∈ℱ@(i , eq) =
      o               ⊑⟨ φ ⟩
      ⊔L (π₀ ⊚ ℱ)     ⊑⟨ n₁ (⊔L (π₀ ⊚ ℱ)) ⟩
      j (⊔L (π₀ ⊚ ℱ)) ■
      where
        φ : o ⊑ (⊔L (π₀ ⊚ ℱ)) is-true
        φ = ⊔L-upper (π₀ ⊚ ℱ) o (i , λ j → π₀ (eq j))

    dist : (o : 𝒜) (ℱ : Sub ℓ₂ 𝒜) → o ⊓ (⊔ ℱ) ≡ ⊔ (index ℱ , (λ i → o ⊓ (ℱ € i)))
    dist o@(o′ , j-fix-o′) ℱ@(I , F) = sigmaPath→pathSigma _ _ (φ , X-set _ _ _ _)
      where
        𝒢 : Sub ℓ₂ ∣ P ∣ₚ
        𝒢 = π₀ ⊚ ℱ

        φ :  π₀ (o ⊓ (⊔ ℱ)) ≡ π₀ (⊔ (I , (λ i → o ⊓ (ℱ € i))))
        φ =
          π₀ (o ⊓ (⊔ ℱ))                   ≡⟨ refl                                      ⟩
          o′ ⊓L j (⊔L 𝒢)                   ≡⟨ cong (λ - → - ⊓L j (⊔L 𝒢)) (sym j-fix-o′) ⟩
          j o′ ⊓L (j (⊔L 𝒢))               ≡⟨ sym (n₀ o′ (⊔L 𝒢))                        ⟩
          j (o′ ⊓L (⊔L 𝒢))                 ≡⟨ cong j (distL o′ 𝒢)                       ⟩
          j (⊔L (I , λ i → o′ ⊓L (𝒢 € i))) ≡⟨ refl                                      ⟩
          π₀ (⊔ (I , λ i → o ⊓ (ℱ € i)))   ∎

-- --}
-- --}
-- --}
