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
    N₀ = (a b : ∣ L ∣F) → j (a ⊓[ L ] b) ≡ (j a) ⊓[ L ] (j b)
    N₁ = (a   : ∣ L ∣F) → a ⊑[ pos L ] (j a) is-true
    N₂ = (a   : ∣ L ∣F) → j (j a) ⊑[ pos L ] j a is-true

-- The type of nuclei.
Nucleus : Frame ℓ₀ ℓ₁ ℓ₂ → Set (ℓ₀ ⊔ ℓ₁)
Nucleus L = Σ (∣ L ∣F → ∣ L ∣F) (IsNuclear L)

idem : (L : Frame ℓ₀ ℓ₁ ℓ₂)
     → (N : Nucleus L)
     → let j = π₀ N in (x : ∣ L ∣F) → j (j x) ≡ j x
idem L (j , n₀ , n₁ , n₂) x = ⊑[ pos L ]-antisym (j (j x)) (j x) (n₂ x) (n₁ (j x))

mono : (L : Frame ℓ₀ ℓ₁ ℓ₂) → (N : Nucleus L)
     → let j = π₀ N
       in (x y : ∣ L ∣F) → x ⊑[ pos L ] y is-true → (j x) ⊑[ pos L ] (j y) is-true
mono L (j , n₀ , n₁ , n₂) x y x⊑y =
  j x             ⊑⟨ ≡⇒⊑ (pos L) (cong j x≡x⊓y) ⟩
  j (x ⊓[ L ] y)  ⊑⟨ ≡⇒⊑ (pos L) (n₀ x y)       ⟩
  j x ⊓[ L ] j y  ⊑⟨ ⊓[ L ]-lower₁ (j x) (j y)  ⟩
  j y         ■
  where
    open PosetReasoning (pos L) using (_⊑⟨_⟩_; _■)

    x⊑x⊓y : x ⊑[ pos L ] (x ⊓[ L ] y) is-true
    x⊑x⊓y = ⊓[ L ]-greatest x y x (⊑[ pos L ]-refl x) x⊑y

    x≡x⊓y : x ≡ (x ⊓[ L ] y)
    x≡x⊓y = ⊑[ pos L ]-antisym x (x ⊓[ L ] y) x⊑x⊓y (⊓[ L ]-lower₀ x y)

-- The set of fixed points for nucleus `j` is equivalent hence equal to its image.
-- This is essentially due to the fact that j (j ())
nuclear-image : (L : Frame ℓ₀ ℓ₁ ℓ₂)
              → let ∣L∣ = ∣ L ∣F in (j : ∣L∣ → ∣L∣)
              → IsNuclear L j
              → (Σ[ b ∈ ∣L∣ ] ∥ Σ[ a ∈ ∣L∣ ] (b ≡ j a) ∥) ≡ (Σ[ a ∈ ∣L∣ ] (j a ≡ a))
nuclear-image L j N@(n₀ , n₁ , n₂) = isoToPath (iso f g sec-f-g ret-f-g)
  where
    A-set = carrier-is-set (pos L)

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
  𝔽 , (_≤_ , 𝔽-set) , ≤-refl , ≤-trans , ≤-antisym
  where
    P = pos L
    A-set = carrier-is-set (pos L)

    𝔽 : Set ℓ₀
    𝔽 = Σ[ a ∈ ∣ L ∣F ] j a ≡ a

    𝔽-set : IsSet 𝔽
    𝔽-set = Σ-set A-set (λ a → prop⇒set (A-set (j a) a))

    _≤_ : 𝔽 → 𝔽 → Ω ℓ₁
    (a , _) ≤ (b , _) = a ⊑[ P ] b is-true , is-true-prop (a ⊑[ P ] b)

    open AlgebraicProperties 𝔽-set _≤_

    ≤-refl : IsReflexive is-true
    ≤-refl (x , _) = ⊑[ P ]-refl x

    ≤-trans : IsTransitive is-true
    ≤-trans (x , _) (y , _) (z , _) x≤y y≤x = ⊑[ P ]-trans x y z x≤y y≤x

    ≤-antisym : IsAntisym is-true
    ≤-antisym (x , _) (y , _) x≤y y≤x =
      ΣProp≡ (λ z → A-set (j z) z) (⊑[ P ]-antisym x y x≤y y≤x)

-- The set of fixed points of a nucleus `j` forms a frame.
-- The join of this frame is define as ⊔ᵢ ℱᵢ := j (⊔′ᵢ ℱᵢ) where ⊔′ denotes the join of L.
nuclear-fixed-point-frame : (L : Frame ℓ₀ ℓ₁ ℓ₂) → (N : Nucleus L) → Frame ℓ₀ ℓ₁ ℓ₂
nuclear-fixed-point-frame {ℓ₁ = ℓ₁} {ℓ₂ = ℓ₂} L N@(j , n₀ , n₁ , n₂) =
    ∣ nuclear-fixed-point-poset L N ∣ₚ
  , (strₚ (nuclear-fixed-point-poset L N)
  , (𝟏[ L ] , 𝟏-fixed)
  , _⊓_ , ⊔_)
  , top , ⊓-lower₀ , ⊓-lower₁ , ⊓-greatest , ⊔-upper , ⊔-least , distr
  where
    𝒜 = π₀ (nuclear-fixed-point-poset L N)

    P          = pos L
    _⊑_ : ∣ pos L ∣ₚ → ∣ pos L ∣ₚ → hProp ℓ₁
    _⊑_        = λ x y → x ⊑[ pos L ] y

    _⊑N_ : 𝒜 → 𝒜 → hProp ℓ₁
    _⊑N_  = λ x y → x ⊑[ nuclear-fixed-point-poset L N ] y

    ⋃L_ : Sub ℓ₂ ∣ L ∣F → ∣ L ∣F
    ⋃L x = ⋃[ L ] x

    ⊑N-antisym = ⊑[ nuclear-fixed-point-poset L N ]-antisym
    A-set      = carrier-is-set (nuclear-fixed-point-poset L N)

    𝟏-fixed : j 𝟏[ L ] ≡ 𝟏[ L ]
    𝟏-fixed = ⊑[ pos L ]-antisym (j 𝟏[ L ]) 𝟏[ L ] (𝟏[ L ]-top (j 𝟏[ L ])) (n₁ 𝟏[ L ])

    open PosetReasoning (pos L) using (_⊑⟨_⟩_; _■)

    _⊓_ : 𝒜 → 𝒜 → 𝒜
    _⊓_ (x , x-f) (y , y-f) =
      x ⊓[ L ] y , ⊑[ P ]-antisym (j (x ⊓[ L ] y)) (x ⊓[ L ] y) φ (n₁ (x ⊓[ L ] y))
      where
        ⊑jx : j (x ⊓[ L ] y) ⊑ j x is-true
        ⊑jx = j (x ⊓[ L ] y) ⊑⟨ ≡⇒⊑ P (n₀ x y)            ⟩
              j x ⊓[ L ] j y ⊑⟨ ⊓[ L ]-lower₀ (j x) (j y) ⟩
              j x ■
        ⊑jy : j (x ⊓[ L ] y) ⊑ j y is-true
        ⊑jy = j (x ⊓[ L ] y) ⊑⟨ ≡⇒⊑ P (n₀ x y)            ⟩
              j x ⊓[ L ] j y ⊑⟨ ⊓[ L ]-lower₁ (j x) (j y) ⟩
              j y ■

        ⊑x : j (x ⊓[ L ] y) ⊑ x is-true
        ⊑x = subst (λ z → j (x ⊓[ L ] y) ⊑ z is-true) x-f ⊑jx
        ⊑y : j (x ⊓[ L ] y) ⊑ y is-true
        ⊑y = subst (λ z → j (x ⊓[ L ] y) ⊑ z is-true) y-f ⊑jy

        φ : j (x ⊓[ L ] y) ⊑ (x ⊓[ L ] y) is-true
        φ = ⊓[ L ]-greatest x y (j (x ⊓[ L ] y)) ⊑x ⊑y

    ⊔_ : Sub ℓ₂ 𝒜 → 𝒜
    ⊔ (I , F) = j (⋃[ L ] 𝒢) , j⊔L-fixed
      where
        𝒢 = I , π₀ ∘ F
        j⊔L-fixed : j (j (⋃[ L ] 𝒢)) ≡ j (⋃[ L ] 𝒢)
        j⊔L-fixed = ⊑[ P ]-antisym _ _ (n₂ (⋃[ L ] 𝒢)) (n₁ (j (⋃[ L ] 𝒢)))

    top : (o : 𝒜) → (o ⊑N (𝟏[ L ] , 𝟏-fixed)) is-true
    top = 𝟏[ L ]-top ∘ π₀

    ⊓-lower₀ : (o p : 𝒜) → (o ⊓ p) ⊑N o is-true
    ⊓-lower₀ (o , _) (p , _) = ⊓[ L ]-lower₀ o p

    ⊓-lower₁ : (o p : 𝒜) → (o ⊓ p) ⊑N p is-true
    ⊓-lower₁ (o , _) (p , _) = ⊓[ L ]-lower₁ o p

    ⊓-greatest : (o p q : 𝒜) → q ⊑N o is-true → q ⊑N p is-true → q ⊑N (o ⊓ p) is-true
    ⊓-greatest (o , _) (p , _) (q , _) q⊑o q⊑p = ⊓[ L ]-greatest o p q q⊑o q⊑p

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

        ψ : j (⋃[ L ] 𝒢) ⊑ (j p′) is-true
        ψ = mono L N (⋃[ L ] 𝒢) p′ (⋃[ L ]-least 𝒢 p′ ϑ)

        φ : j (⋃[ L ] 𝒢) ⊑ p′ is-true
        φ = subst (λ k → (j (⋃[ L ] 𝒢) ⊑ k) is-true) eq ψ

    ⊔-upper : (ℱ : Sub ℓ₂ 𝒜) (o : 𝒜) → o ε ℱ → (o ⊑N (⊔ ℱ)) is-true
    ⊔-upper ℱ (o , _) o∈ℱ@(i , eq) =
      o               ⊑⟨ φ ⟩
      ⋃[ L ] (π₀ ⊚ ℱ) ⊑⟨ n₁ (⋃[ L ] (π₀ ⊚ ℱ)) ⟩
      j (⋃[ L ] (π₀ ⊚ ℱ)) ■
      where
        φ : o ⊑ (⋃[ L ] (π₀ ⊚ ℱ)) is-true
        φ = ⋃[ L ]-upper (π₀ ⊚ ℱ) o (i , λ j → π₀ (eq j))

    distr : (o : 𝒜) (ℱ : Sub ℓ₂ 𝒜) → o ⊓ (⊔ ℱ) ≡ ⊔ (index ℱ , (λ i → o ⊓ (ℱ € i)))
    distr o@(o′ , jo′=o′) ℱ@(I , F) =
      sigmaPath→pathSigma _ _ (φ , carrier-is-set (pos L) _ _ _ _)
      where
        𝒢 : Sub ℓ₂ ∣ P ∣ₚ
        𝒢 = π₀ ⊚ ℱ

        o′=jo′ : o′ ≡ j o′
        o′=jo′ = sym jo′=o′

        φ :  π₀ (o ⊓ (⊔ ℱ)) ≡ π₀ (⊔ (I , (λ i → o ⊓ (ℱ € i))))
        φ =
          π₀ (o ⊓ (⊔ ℱ))                   ≡⟨ refl                                  ⟩
          o′ ⊓[ L ] j (⋃L 𝒢)               ≡⟨ cong (λ - → - ⊓[ L ] j (⋃L 𝒢)) o′=jo′ ⟩
          j o′ ⊓[ L ] (j (⋃L 𝒢))           ≡⟨ sym (n₀ o′ (⋃[ L ] 𝒢))                ⟩
          j (o′ ⊓[ L ] (⋃L 𝒢))             ≡⟨ cong j (dist L o′ 𝒢)                  ⟩
          j (⋃L ((λ - → o′ ⊓[ L ] -) ⊚ 𝒢)) ≡⟨ refl                                  ⟩
          π₀ (⊔ (I , λ i → o ⊓ (ℱ € i)))   ∎

-- --}
-- --}
-- --}
