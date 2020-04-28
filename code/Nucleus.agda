{-# OPTIONS --without-K --cubical --safe #-}

open import Truncation

module Nucleus where

open import Basis
open import Family
open import Poset
open import Frame

-- A predicate expressing whether a function is a nucleus.
IsNuclear : (L : Frame ℓ₀ ℓ₁ ℓ₂) → (∣ L ∣F → ∣ L ∣F) → Type (ℓ₀ ⊔ ℓ₁)
IsNuclear L j = N₀ × N₁ × N₂
  where
    N₀ = (x y : ∣ L ∣F) → j (x ⊓[ L ] y) ≡ (j x) ⊓[ L ] (j y)
    N₁ = (x   : ∣ L ∣F) → [ x ⊑[ pos L ] (j x) ]
    N₂ = (x   : ∣ L ∣F) → [ j (j x) ⊑[ pos L ] j x ]

-- The type of nuclei.
Nucleus : Frame ℓ₀ ℓ₁ ℓ₂ → Type (ℓ₀ ⊔ ℓ₁)
Nucleus L = Σ (∣ L ∣F → ∣ L ∣F) (IsNuclear L)

-- Every nucleus is idempotent.
idem : (L : Frame ℓ₀ ℓ₁ ℓ₂)
     → (N : Nucleus L)
     → let j = π₀ N in (x : ∣ L ∣F) → j (j x) ≡ j x
idem L (j , N₀ , N₁ , N₂) x = ⊑[ pos L ]-antisym _ _ (N₂ x) (N₁ (j x))

-- Every nucleus is monotonic.
mono : (L : Frame ℓ₀ ℓ₁ ℓ₂) → (N : Nucleus L)
     → let j = π₀ N
       in (x y : ∣ L ∣F) → [ x ⊑[ pos L ] y ] → [ (j x) ⊑[ pos L ] (j y) ]
mono L (j , N₀ , N₁ , N₂) x y x⊑y =
  j x             ⊑⟨ ≡⇒⊑ (pos L) (cong j x≡x⊓y) ⟩
  j (x ⊓[ L ] y)  ⊑⟨ ≡⇒⊑ (pos L) (N₀ x y)       ⟩
  j x ⊓[ L ] j y  ⊑⟨ ⊓[ L ]-lower₁ (j x) (j y)  ⟩
  j y         ■
  where
    open PosetReasoning (pos L) using (_⊑⟨_⟩_; _■)

    x⊑x⊓y : [ x ⊑[ pos L ] (x ⊓[ L ] y) ]
    x⊑x⊓y = ⊓[ L ]-greatest x y x (⊑[ pos L ]-refl x) x⊑y

    x≡x⊓y : x ≡ x ⊓[ L ] y
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
  𝔽 , _≤_ , 𝔽-set , ≤-refl , ≤-trans , ≤-antisym
  where
    P = pos L
    A-set = carrier-is-set (pos L)

    𝔽 : Type ℓ₀
    𝔽 = Σ[ a ∈ ∣ L ∣F ] j a ≡ a

    𝔽-set : isSet 𝔽
    𝔽-set = isSetΣ A-set (λ a → isProp→isSet (A-set (j a) a))

    _≤_ : 𝔽 → 𝔽 → hProp ℓ₁
    (a , _) ≤ (b , _) = [ a ⊑[ P ] b ] , is-true-prop (a ⊑[ P ] b)

    ≤-refl : [ isReflexive _≤_ ]
    ≤-refl (x , _) = ⊑[ P ]-refl x

    ≤-trans : [ isTransitive _≤_ ]
    ≤-trans (x , _) (y , _) (z , _) x≤y y≤x = ⊑[ P ]-trans x y z x≤y y≤x

    ≤-antisym : [ isAntisym 𝔽-set _≤_ ]
    ≤-antisym (x , _) (y , _) x≤y y≤x =
      ΣProp≡ (λ z → A-set (j z) z) (⊑[ P ]-antisym x y x≤y y≤x)

-- The set of fixed points of a nucleus `j` forms a frame.
-- The join of this frame is define as ⊔ᵢ ℱᵢ := j (⊔′ᵢ ℱᵢ) where ⊔′ denotes the join of L.
nuclear-fixed-point-frame : (L : Frame ℓ₀ ℓ₁ ℓ₂) → (N : Nucleus L) → Frame ℓ₀ ℓ₁ ℓ₂
nuclear-fixed-point-frame {ℓ₁ = ℓ₁} {ℓ₂ = ℓ₂} L N@(j , n₀ , n₁ , n₂) =
                          ∣ nuclear-fixed-point-poset L N ∣ₚ
  , (strₚ (nuclear-fixed-point-poset L N) , (𝟏[ L ] , 𝟏-fixed) , _∧_ , ⊔_)
  , top
  , ( (λ x y → ⊓-lower₀ x y , ⊓-lower₁ x y)
    , λ { x y z (z⊑x , x⊑y) → ⊓-greatest x y z z⊑x x⊑y })
  , ((⊔-upper , ⊔-least) , distr)
  where
    𝒜 = π₀ (nuclear-fixed-point-poset L N)

    _⊑_ : ∣ pos L ∣ₚ → ∣ pos L ∣ₚ → hProp ℓ₁
    _⊑_        = λ x y → x ⊑[ pos L ] y

    _⊑N_ : 𝒜 → 𝒜 → hProp ℓ₁
    _⊑N_  = λ x y → x ⊑[ nuclear-fixed-point-poset L N ] y

    ⋃L_ : Sub ℓ₂ ∣ L ∣F → ∣ L ∣F
    ⋃L x = ⋃[ L ] x

    ⊑N-antisym = ⊑[ nuclear-fixed-point-poset L N ]-antisym
    A-set      = carrier-is-set (nuclear-fixed-point-poset L N)

    𝟏-fixed : j 𝟏[ L ] ≡ 𝟏[ L ]
    𝟏-fixed = ⊑[ pos L ]-antisym _ _ (𝟏[ L ]-top (j 𝟏[ L ])) (n₁ 𝟏[ L ])

    open PosetReasoning (pos L) using (_⊑⟨_⟩_; _■)

    _∧_ : 𝒜 → 𝒜 → 𝒜
    _∧_ (x , x-f) (y , y-f) =
      x ⊓[ L ] y , ⊑[ pos L ]-antisym _ _ φ (n₁ (x ⊓[ L ] y))
      where
        ⊑jx : [ j (x ⊓[ L ] y) ⊑ j x ]
        ⊑jx = j (x ⊓[ L ] y) ⊑⟨ ≡⇒⊑ (pos L) (n₀ x y)      ⟩
              j x ⊓[ L ] j y ⊑⟨ ⊓[ L ]-lower₀ (j x) (j y) ⟩
              j x ■
        ⊑jy : [ j (x ⊓[ L ] y) ⊑ j y ]
        ⊑jy = j (x ⊓[ L ] y) ⊑⟨ ≡⇒⊑ (pos L) (n₀ x y)      ⟩
              j x ⊓[ L ] j y ⊑⟨ ⊓[ L ]-lower₁ (j x) (j y) ⟩
              j y ■

        ⊑x : [ j (x ⊓[ L ] y) ⊑ x ]
        ⊑x = subst (λ z → [ j (x ⊓[ L ] y) ⊑ z ]) x-f ⊑jx
        ⊑y : [ j (x ⊓[ L ] y) ⊑ y ]
        ⊑y = subst (λ z → [ j (x ⊓[ L ] y) ⊑ z ]) y-f ⊑jy

        φ : [ j (x ⊓[ L ] y) ⊑ (x ⊓[ L ] y) ]
        φ = ⊓[ L ]-greatest x y (j (x ⊓[ L ] y)) ⊑x ⊑y

    ⊔_ : Sub ℓ₂ 𝒜 → 𝒜
    ⊔ (I , F) = j (⋃[ L ] 𝒢) , j⊔L-fixed
      where
        𝒢 = I , π₀ ∘ F
        j⊔L-fixed : j (j (⋃[ L ] 𝒢)) ≡ j (⋃[ L ] 𝒢)
        j⊔L-fixed = ⊑[ pos L ]-antisym _ _ (n₂ (⋃[ L ] 𝒢)) (n₁ (j (⋃[ L ] 𝒢)))

    top : (o : 𝒜) → [ o ⊑N (𝟏[ L ] , 𝟏-fixed) ]
    top = 𝟏[ L ]-top ∘ π₀

    ⊓-lower₀ : (o p : 𝒜) → [ (o ∧ p) ⊑N o ]
    ⊓-lower₀ (o , _) (p , _) = ⊓[ L ]-lower₀ o p

    ⊓-lower₁ : (o p : 𝒜) → [ (o ∧ p) ⊑N p ]
    ⊓-lower₁ (o , _) (p , _) = ⊓[ L ]-lower₁ o p

    ⊓-greatest : (o p q : 𝒜) → [ q ⊑N o ] → [ q ⊑N p ] → [ q ⊑N (o ∧ p) ]
    ⊓-greatest (o , _) (p , _) (q , _) q⊑o q⊑p = ⊓[ L ]-greatest o p q q⊑o q⊑p

    ⊔-least : (ℱ : Sub ℓ₂ 𝒜) (u : 𝒜) → [ ∀[ x ε ℱ ] (x ⊑N u) ] → [ (⊔ ℱ) ⊑N u ]
    ⊔-least ℱ (u , fix) ℱ⊑u = subst (λ - → [ j (⋃[ L ] 𝒢) ⊑ - ]) fix NTS₀
      where
        𝒢 : Sub ℓ₂ ∣ pos L ∣ₚ
        𝒢 = π₀ ⟨$⟩ ℱ

        𝒢⊑u : [ ∀[ o ε 𝒢 ] (o ⊑ u) ]
        𝒢⊑u o (i , eq′) = o     ⊑⟨ ≡⇒⊑ (pos L) (sym eq′)               ⟩
                          𝒢 $ i ⊑⟨ ℱ⊑u (𝒢 $ i , π₁ (ℱ $ i)) (i , refl) ⟩
                          u     ■

        NTS₀ : [ j (⋃[ L ] 𝒢) ⊑ j u ]
        NTS₀ = mono L N (⋃[ L ] 𝒢) u (⋃[ L ]-least 𝒢 u 𝒢⊑u)

    ⊔-upper : (ℱ : Sub ℓ₂ 𝒜) (x : 𝒜) → x ε ℱ → [ x ⊑N (⊔ ℱ) ]
    ⊔-upper ℱ (x , _) o∈ℱ@(i , eq) =
      x                   ⊑⟨ NTS                  ⟩
      ⋃[ L ] (π₀ ⟨$⟩ ℱ)     ⊑⟨ n₁ (⋃[ L ] (π₀ ⟨$⟩ ℱ)) ⟩
      j (⋃[ L ] (π₀ ⟨$⟩ ℱ)) ■
      where
        NTS : [ x ⊑ (⋃[ L ] (π₀ ⟨$⟩ ℱ)) ]
        NTS = ⋃[ L ]-upper (π₀ ⟨$⟩ ℱ) x (i , λ j → π₀ (eq j))

    distr : (o : 𝒜) (ℱ : Sub ℓ₂ 𝒜) → o ∧ (⊔ ℱ) ≡ ⊔ (index ℱ , (λ i → o ∧ (ℱ $ i)))
    distr 𝒶@(o , jo=o) ℱ@(I , F) =
      sigmaPath→pathSigma _ _ (φ , carrier-is-set (pos L) _ _ _ _)
      where
        𝒢 : Sub ℓ₂ ∣ pos L ∣ₚ
        𝒢 = π₀ ⟨$⟩ ℱ

        φ :  π₀ (𝒶 ∧ (⊔ ℱ)) ≡ π₀ (⊔ (I , (λ i → 𝒶 ∧ (ℱ $ i))))
        φ =
          π₀ (𝒶 ∧ (⊔ ℱ))                    ≡⟨ refl                                      ⟩
          o ⊓[ L ] j (⋃L 𝒢)                 ≡⟨ cong (λ - → - ⊓[ L ] j (⋃L 𝒢)) (sym jo=o) ⟩
          j o ⊓[ L ] j (⋃L 𝒢)               ≡⟨ sym (n₀ o (⋃[ L ] 𝒢))                     ⟩
          j (o ⊓[ L ] (⋃L 𝒢))               ≡⟨ cong j (dist L o 𝒢)                       ⟩
          j (⋃L ((λ - → o ⊓[ L ] -) ⟨$⟩ 𝒢)) ≡⟨ refl                                      ⟩
          π₀ (⊔ (I , λ i → 𝒶 ∧ (ℱ $ i)))    ∎

-- --}
-- --}
-- --}
