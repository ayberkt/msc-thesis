{-# OPTIONS --without-K --cubical --safe #-}

open import Truncation

module Frame where

open import Basis
open import Family
open import Truncation
open import Poset
open import Powerset
open import Unit

import AlgebraicProperties

RawFrameStr : (ℓ₁ ℓ₂ : Level) → Type ℓ₀ → Type (ℓ₀ ⊔ suc ℓ₁ ⊔ suc ℓ₂)
RawFrameStr ℓ₁ ℓ₂ A = (PosetStr ℓ₁ A) × A × (A → A → A) × (Sub ℓ₂ A → A)

frame-axioms : (A : Type ℓ₀) → RawFrameStr ℓ₁ ℓ₂ A → Set (ℓ₀ ⊔ ℓ₁ ⊔ suc ℓ₂)
frame-axioms {ℓ₀ = ℓ₀} {ℓ₁ = ℓ₁} {ℓ₂ = ℓ₂} O (((_⊑_ , _) , _) , 𝟏 , _⊓_ , ⋃_) =
    ((o : O)       → o ⊑ 𝟏 is-true)
  × ((o p : O)     → (o ⊓ p) ⊑ o is-true)
  × ((o p : O)     → (o ⊓ p) ⊑ p is-true)
  × ((o p q : O)   → q ⊑ o is-true → q ⊑ p is-true → q ⊑ (o ⊓ p) is-true)
  × ((ℱ : Sub ℓ₂ O) → (o : O) → o ε ℱ → o ⊑ (⋃ ℱ) is-true)
  × ((ℱ : Sub ℓ₂ O) → (p : O) → ((o : O) → o ε ℱ → o ⊑ p is-true) → (⋃ ℱ) ⊑ p is-true)
  × ((o : O) (ℱ : Sub ℓ₂ O) → o ⊓ (⋃ ℱ) ≡ ⋃ (index ℱ , λ i → o ⊓ (ℱ € i)))

FrameStr : (ℓ₁ ℓ₂ : Level) → Type ℓ₀ → Type (ℓ₀ ⊔ suc ℓ₁ ⊔ suc ℓ₂)
FrameStr ℓ₁ ℓ₂ = add-to-structure (RawFrameStr ℓ₁ ℓ₂) frame-axioms

Frame : (ℓ₀ ℓ₁ ℓ₂ : Level) → Type (suc ℓ₀ ⊔ suc ℓ₁ ⊔ suc ℓ₂)
Frame ℓ₀ ℓ₁ ℓ₂ = Σ (Type ℓ₀) (FrameStr ℓ₁ ℓ₂)

-- Projection for the carrier set of a frame
-- i.e., the carrier set of the underlying poset.
∣_∣F : Frame ℓ₀ ℓ₁ ℓ₂ → Type ℓ₀
∣ A , _ ∣F = A

-- The underlying poset of a frame.
pos : Frame ℓ₀ ℓ₁ ℓ₂ → Poset ℓ₀ ℓ₁
pos (A , (P , _) , _) = A , P

𝟏[_] : (F : Frame ℓ₀ ℓ₁ ℓ₂) → ∣ F ∣F
𝟏[ _ , (_ , (𝟏 , _)) , _ ] = 𝟏

glb-of : (F : Frame ℓ₀ ℓ₁ ℓ₂) → ∣ F ∣F → ∣ F ∣F → ∣ F ∣F
glb-of (_ , (_ , _ , _⊓_ , _) , _) = _⊓_

syntax glb-of F o p = o ⊓[ F ] p

⋃[_]_ : (F : Frame ℓ₀ ℓ₁ ℓ₂) → Sub ℓ₂ ∣ F ∣F → ∣ F ∣F
⋃[ (_ , (_ , (_ , _ , ⋃_)) , _) ] ℱ = ⋃ ℱ

module _ (F : Frame ℓ₀ ℓ₁ ℓ₂) where

  private
    P = pos F

    _⊑_ : ∣ F ∣F → ∣ F ∣F → hProp ℓ₁
    x ⊑ y = x ⊑[ P ] y

  𝟏[_]-top : (o : ∣ F ∣F) → o ⊑[ pos F ] 𝟏[ F ] is-true
  𝟏[_]-top = let (_ , _ , (top , _)) = F in top

  ⊓[_]-lower₀ : (o p : ∣ F ∣F) → (o ⊓[ F ] p) ⊑[ pos F ] o is-true
  ⊓[_]-lower₀ = let (_ , (_ , _ , (φ , _))) = F in φ

  ⊓[_]-lower₁ : (o p : ∣ F ∣F) → (o ⊓[ F ] p) ⊑[ pos F ] p is-true
  ⊓[_]-lower₁ = let (_ , (_ , _ , (_ , φ , _))) = F in φ

  ⊓[_]-greatest : (o p q : ∣ F ∣F)
                → q ⊑[ pos F ] o is-true
                → q ⊑[ pos F ] p is-true
                → q ⊑[ pos F ] (o ⊓[ F ] p) is-true
  ⊓[_]-greatest = let (_ , (_ , _ , (_ , _ , φ , _))) = F in φ

  ⋃[_]-upper : (ℱ : Sub ℓ₂ ∣ F ∣F) (o : ∣ F ∣F) → o ε ℱ → o ⊑[ pos F ] (⋃[ F ] ℱ) is-true
  ⋃[_]-upper = let (_ , (_ , _ , (_ , _ , _ , φ , _))) = F in φ

  ⋃[_]-least : (ℱ : Sub ℓ₂ ∣ F ∣F) (p : ∣ F ∣F)
            → ((o : ∣ F ∣F) → o ε ℱ → o ⊑[ pos F ] p is-true)
            → (⋃[ F ] ℱ) ⊑[ pos F ] p is-true
  ⋃[_]-least = let (_ , (_ , _ , (_ , _ , _ , _ , φ , _))) = F in φ

  dist : (o : ∣ F ∣F) (ℱ : Sub ℓ₂ ∣ F ∣F)
       → o ⊓[ F ] (⋃[ F ] ℱ) ≡ ⋃[ F ] ((λ - → o ⊓[ F ] -) ⊚ ℱ)
  dist = let (_ , (_ , _ , (_ , _ , _ , _ , _ , φ))) = F in φ

  top-unique : (z : ∣ F ∣F)
            → ((o : ∣ F ∣F) → o ⊑[ pos F ] z is-true) → z ≡ 𝟏[ F ]
  top-unique z z-top = ⊑[ pos F ]-antisym z 𝟏[ F ] (𝟏[_]-top z) (z-top 𝟏[ F ])

  ⊓-unique : (x y z : ∣ F ∣F)
          → z ⊑[ P ] x is-true
          → z ⊑[ P ] y is-true
          → ((w : ∣ F ∣F) → w ⊑[ P ] x is-true → w ⊑[ P ] y is-true → w ⊑[ P ] z is-true)
          → z ≡ x ⊓[ F ] y
  ⊓-unique x y z z⊑x z⊑y greatest =
    ⊑[ P ]-antisym z (x ⊓[ F ] y) (⊓[_]-greatest x y z z⊑x z⊑y) NTS
    where
      NTS : (x ⊓[ F ] y) ⊑[ P ] z is-true
      NTS = greatest (x ⊓[ F ] y) (⊓[_]-lower₀ x y) (⊓[_]-lower₁ x y)

  ⋃-unique : (ℱ : Sub ℓ₂ ∣ F ∣F) (z : ∣ F ∣F)
          → ((o : ∣ F ∣F) → o ε ℱ → o ⊑ z is-true)
          → ((w : ∣ F ∣F) → ((o : ∣ F ∣F) → o ε ℱ → o ⊑ w is-true) → z ⊑ w is-true)
          → z ≡ ⋃[ F ] ℱ
  ⋃-unique ℱ z upper least =
    ⊑[ P ]-antisym z (⋃[ F ] ℱ) (least (⋃[ F ] ℱ) (⋃[_]-upper ℱ)) NTS
    where
      NTS : (⋃[ F ] ℱ) ⊑ z is-true
      NTS = ⋃[_]-least ℱ z upper

  comm : (x y : ∣ F ∣F) → x ⊓[ F ] y ≡ y ⊓[ F ] x
  comm x y = ⊓-unique y x _ (⊓[_]-lower₁ x y) (⊓[_]-lower₀ x y) NTS
    where
      NTS = λ w w⊑y w⊑x → ⊓[_]-greatest x y w w⊑x w⊑y

  family-iff : {ℱ 𝒢 : Sub ℓ₂ ∣ F ∣F}
             → ((x : ∣ F ∣F) → (x ε ℱ → x ε 𝒢) × (x ε 𝒢 → x ε ℱ))
             → ⋃[ F ] ℱ ≡ ⋃[ F ] 𝒢
  family-iff {ℱ = ℱ} {𝒢 = 𝒢} h = ⋃-unique _ _ ub least
    where
      ub : (o : ∣ F ∣F) → o ε 𝒢 → (o ⊑ (⋃[ F ] ℱ)) is-true
      ub o (i , p) = subst
                       (λ - → - ⊑[ pos F ] (⋃[ F ] ℱ) is-true)
                       p
                       (⋃[ _ ]-upper _ (π₁ (h (𝒢 € i)) (i , refl)))
      least : (w : ∣ F ∣F)
            → ((o : ∣ F ∣F) → o ε 𝒢 → o ⊑ w is-true)
            → (⋃[ F ] ℱ) ⊑ w is-true
      least w f = ⋃[ _ ]-least _ λ o oεℱ → f o (π₀ (h o) oεℱ)

  flatten : (I : Type ℓ₂) (J : I → Type ℓ₂) (f : (i : I) → J i → ∣ F ∣F)
          → ⋃[ F ] (Σ I J , λ { (x , y) → f x y })
          ≡ ⋃[ F ] (I , λ i → ⋃[ F ] (J i , λ y → f i y))
  flatten I J f = ⊑[ pos F ]-antisym _ _ down up
    where
      open PosetReasoning (pos F) using (_⊑⟨_⟩_; _■)

      LHS = ⋃[ F ] (Σ I J , (λ { (x , y) → f x y }))
      RHS = ⋃[ F ] (I , (λ i → ⋃[ F ] (J i , f i)))

      down : LHS ⊑[ pos F ] RHS is-true
      down = ⋃[_]-least _ _ isUB
        where
          isUB : (o : ∣ F ∣F)
               → o ε (Σ I J , (λ { (x , y) → f x y }))
               → o ⊑[ pos F ] RHS is-true
          isUB o ((i , j) , eq) =
              o                          ⊑⟨ ≡⇒⊑ (pos F) (sym eq) ⟩
              f i j                      ⊑⟨ ⋃[_]-upper _ _ (j , refl) ⟩
              ⋃[ F ] (J i , λ - → f i -) ⊑⟨ ⋃[_]-upper _ _ (i , refl) ⟩
              RHS                        ■

      up : RHS ⊑[ pos F ] LHS is-true
      up = ⋃[_]-least _ _ isUB
        where
          isUB : (o : ∣ F ∣F)
               → o ε (I , (λ i → ⋃[ F ] (J i , f i)))
               → o ⊑[ pos F ] (⋃[ F ] (Σ I J , (λ { (x , y) → f x y }))) is-true
          isUB o (i , eq) =
            o                                        ⊑⟨ ≡⇒⊑ (pos F) (sym eq) ⟩
            ⋃[ F ] (J i , λ y → f i y)               ⊑⟨ ⋃[_]-least _ _ isUB′ ⟩
            ⋃[ F ] (Σ I J , (λ { (x , y) → f x y })) ■
            where
              isUB′ : (z : ∣ F ∣F) → z ε (J i , (λ y → f i y)) → z ⊑[ pos F ] LHS is-true
              isUB′ z (j , eq′) = ⋃[_]-upper _ _ ((i , j) , eq′)

-- Frame homomorphisms.
IsFrameHomomorphism : (F G : Frame ℓ₀ ℓ₁ ℓ₂)
                    → (m : pos F ─m→ pos G)
                    → Type (ℓ₀ ⊔ suc ℓ₂)
IsFrameHomomorphism {ℓ₀ = ℓ₀} {ℓ₁ = ℓ₁} {ℓ₂ = ℓ₂} F G m =
  resp-𝟏 × resp-⊓ × resp-⋃
  where
    resp-𝟏 : Type ℓ₀
    resp-𝟏 = m $ₘ 𝟏[ F ] ≡ 𝟏[ G ]

    resp-⊓ : Type ℓ₀
    resp-⊓ = (x y : ∣ F ∣F) → m $ₘ (x ⊓[ F ] y) ≡ (m $ₘ x) ⊓[ G ] (m $ₘ y)

    resp-⋃ : Type (ℓ₀ ⊔ suc ℓ₂)
    resp-⋃ = (ℱ : Sub ℓ₂ ∣ F ∣F) → m $ₘ (⋃[ F ] ℱ) ≡ ⋃[ G ] (π₀ m ⊚ ℱ)

IsFrameHomomorphism-prop : (F G : Frame ℓ₀ ℓ₁ ℓ₂)
                         → (m : pos F ─m→ pos G)
                         → IsProp (IsFrameHomomorphism F G m)
IsFrameHomomorphism-prop F G m =
  isOfHLevelΣ 1 (carrier-is-set (pos G) _ _) λ _ →
  isOfHLevelΣ 1 (∏-prop λ x → ∏-prop λ y → carrier-is-set (pos G) _ _) λ _ →
    ∏-prop λ ℱ → carrier-is-set (pos G) _ _

_─f→_ : Frame ℓ₀ ℓ₁ ℓ₂ → Frame ℓ₀ ℓ₁ ℓ₂ → Type (ℓ₀ ⊔ ℓ₁ ⊔ suc ℓ₂)
_─f→_ {ℓ₀ = ℓ₀} {ℓ₁ = ℓ₁} {ℓ₂ = ℓ₂} F G = Σ (pos F ─m→ pos G) (IsFrameHomomorphism F G)

_$f_ : {F G : Frame ℓ₀ ℓ₁ ℓ₂} → F ─f→ G → ∣ F ∣F → ∣ G ∣F
(m , _) $f x = m $ₘ x

-- An element of the poset is like a finite observation whereas an element of the
-- frame of downward closed posets is like a general observation.

-- The set of downward-closed subsets of a poset forms a frame.
downward-subset-poset : (P : Poset ℓ₀ ℓ₁) → Poset (suc ℓ₀ ⊔ ℓ₁) ℓ₀
downward-subset-poset {ℓ₀ = ℓ₀} {ℓ₁ = ℓ₁} (A , P) =
  𝔻 , (_<<_ , DownwardClosedSubset-set (A , P)) , <<-refl , <<-trans , <<-antisym
  where
    𝔻 = DownwardClosedSubset (A , P)

    _<<_ : 𝔻 → 𝔻 → hProp ℓ₀
    _<<_ (S , _) (T , _) = S ⊆ T

    open AlgebraicProperties (DownwardClosedSubset-set (A , P)) _<<_
       renaming ( IsReflexive  to <<-IsReflexive
                ; IsTransitive to <<-IsTransitive
                ; IsAntisym    to <<-IsAntisym)

    <<-refl : <<-IsReflexive is-true
    <<-refl (U , U-down) x xεU = xεU

    <<-trans : <<-IsTransitive is-true
    <<-trans _ _ _ S<<T T<<U x xεS = T<<U x (S<<T x xεS)

    <<-antisym : <<-IsAntisym is-true
    <<-antisym X Y S⊆T T⊆S =
      to-subtype-≡ X Y (is-true-prop ∘ IsDownwardClosed (A , P)) (⊆-antisym S⊆T T⊆S)

-- The set of downward-closed subsets of a poset forms a frame.
downward-subset-frame : (P : Poset ℓ₀ ℓ₁) → Frame (suc ℓ₀ ⊔ ℓ₁) ℓ₀ ℓ₀
downward-subset-frame {ℓ₀ = ℓ₀} {ℓ₁ = ℓ₁} (X , P) =
    𝔻
  , (strₚ 𝔻ₚ , 𝟏 , (_⊓_ , ⊔_))
  , 𝟏-top , ⊓-lower₀ , ⊓-lower₁ , ⊓-greatest , ⊔-upper , ⊔-least , distr
  where
    𝔻ₚ = downward-subset-poset (X , P)
    𝔻  = ∣ 𝔻ₚ ∣ₚ

    ∣_∣𝔻 : 𝔻 → 𝒫 X
    ∣ S , _ ∣𝔻 = S

    𝟏 = (λ _ → N₁ , N₁-prop) , λ _ _ _ _ → tt

    ∩-down : (S T : 𝒫 X)
           → IsDownwardClosed (X , P) S is-true
           → IsDownwardClosed (X , P) T is-true
           → IsDownwardClosed (X , P) (S ∩ T) is-true
    ∩-down S T S↓ T↓ x y x∈S∩T y⊑x = S↓ x y (π₀ x∈S∩T) y⊑x , T↓ x y (π₁ x∈S∩T) y⊑x

    _⊓_ : 𝔻 → 𝔻 → 𝔻
    (S , S-dc) ⊓ (T , T-dc) = (S ∩ T) , ∩-down S T S-dc T-dc

    𝟏-top : (D : 𝔻) → (D ⊑[ 𝔻ₚ ] 𝟏) is-true
    𝟏-top D _ _ = tt

    -- Given a family ℱ over 𝔻 and some x : X, `in-some-set ℱ x` holds iff there is some
    -- set S among ℱ such that x ∈ S.
    in-some-set-of : (ℱ : Sub ℓ₀ 𝔻) → X → Set ℓ₀
    in-some-set-of ℱ x = Σ (index ℱ) (λ i → ∣ ℱ € i ∣𝔻 x is-true)

    ⊔_ : Sub ℓ₀ 𝔻 → 𝔻
    ⊔ ℱ = (λ x → ∥ in-some-set-of ℱ x ∥ , ∥∥-prop _) , ⊔ℱ↓
      where
        ind : (x y : X)
            → y ⊑[ (X , P) ] x is-true → in-some-set-of ℱ x → ∥ in-some-set-of ℱ y ∥
        ind x y y⊑x (i , x∈ℱᵢ) = ∣ i , π₁ (ℱ € i) x y x∈ℱᵢ y⊑x ∣

        ⊔ℱ↓ : IsDownwardClosed (X , P) (λ x → ∥ in-some-set-of ℱ x ∥ , ∥∥-prop _) is-true
        ⊔ℱ↓ x y ∣p∣ y⊑x = ∥∥-rec (∥∥-prop _) (ind x y y⊑x) ∣p∣

    ⊔-upper : (ℱ : Sub ℓ₀ 𝔻) (D : 𝔻) → D ε ℱ → D ⊑[ 𝔻ₚ ] (⊔ ℱ) is-true
    ⊔-upper ℱ D DεS@(i , p) x x∈D = ∣ i , subst (λ V → ∣ V ∣𝔻 x is-true) (sym p) x∈D ∣

    ⊔-least : (ℱ : Sub ℓ₀ 𝔻) (z : 𝔻)
            → ((o : 𝔻) → o ε ℱ → (o ⊑[ 𝔻ₚ ] z) is-true)
            → (⊔ ℱ) ⊑[ 𝔻ₚ ] z is-true
    ⊔-least ℱ D φ x x∈⊔S = ∥∥-rec (π₁ (∣ D ∣𝔻 x)) ind x∈⊔S
      where
        ind : in-some-set-of ℱ x → ∣ D ∣𝔻 x is-true
        ind (i , x∈ℱᵢ) = φ (ℱ € i) (i , refl) x x∈ℱᵢ

    ⊓-lower₀ : (D E : 𝔻) → (D ⊓ E) ⊑[ 𝔻ₚ ] D is-true
    ⊓-lower₀ D E x (x∈D , _) = x∈D

    ⊓-lower₁ : (D E : 𝔻) → (D ⊓ E) ⊑[ 𝔻ₚ ] E is-true
    ⊓-lower₁ D E x (_ , x∈F) = x∈F

    ⊓-greatest : (D E F : 𝔻)
               → F ⊑[ 𝔻ₚ ] D is-true → F ⊑[ 𝔻ₚ ] E is-true → F ⊑[ 𝔻ₚ ] (D ⊓ E) is-true
    ⊓-greatest D E F F<<D F<<E x x∈F = (F<<D x x∈F) , (F<<E x x∈F)

    distr : (D : 𝔻) (ℱ : Sub ℓ₀ 𝔻) → D ⊓ (⊔ ℱ) ≡ ⊔ (index ℱ , λ i → D ⊓ (ℱ € i))
    distr D ℱ = ⊑[ 𝔻ₚ ]-antisym (D ⊓ (⊔ ℱ)) (⊔ (index ℱ , λ i → D ⊓ (ℱ € i))) down up
      where
        𝒜 = ∣ D ⊓ (⊔ ℱ) ∣𝔻
        ℬ = ∣ ⊔ (index ℱ , (λ i → D ⊓ (ℱ € i))) ∣𝔻

        down : (x : X) → 𝒜 x is-true → ℬ x is-true
        down x x∈𝒜@(x∈D , x∈⊔ℱ) = ∥∥-rec (∥∥-prop _) ind x∈⊔ℱ
          where
            ind : in-some-set-of ℱ x → ∥ in-some-set-of (index ℱ , λ i → D ⊓ (ℱ € i)) x ∥
            ind (i , x∈ℱᵢ) = ∣ i , x∈D , x∈ℱᵢ ∣

        up : (x : X) → ℬ x is-true → 𝒜 x is-true
        up x x∈ℬ =
          ∥∥-rec (isOfHLevelΣ 1 (is-true-prop (∣ D ∣𝔻 x)) λ _ →
          is-true-prop (∣ ⊔ ℱ ∣𝔻 x)) φ x∈ℬ
          where
            φ : in-some-set-of (index ℱ , λ j → D ⊓ (ℱ € j)) x
              → (∣ D ∣𝔻 x is-true) × ∣ ⊔ ℱ ∣𝔻 x is-true
            φ (i , x∈D , x∈ℱᵢ) = x∈D , ∣ i , x∈ℱᵢ ∣

-- Frames form an SNS.

RF-iso : (ℓ₁ ℓ₂ : Level) (M N : Σ (Type ℓ₀) (RawFrameStr ℓ₁ ℓ₂))
       → π₀ M ≃ π₀ N → Type (ℓ₀ ⊔ ℓ₁ ⊔ suc ℓ₂)
RF-iso {ℓ₀ = ℓ₀} ℓ₁ ℓ₂ (A , (P , _) , 𝟏₀ , _⊓₀_ , ⋃₀) (B , (Q , _), 𝟏₁ , _⊓₁_ , ⋃₁) i =
    order-iso (A , P) (B , Q) i
  × f 𝟏₀ ≡ 𝟏₁
  × ((x y : A) → f (x ⊓₀ y) ≡ (f x) ⊓₁ (f y))
  × ((ℱ : Sub ℓ₂ A) → f (⋃₀ ℱ) ≡ ⋃₁ (f ⊚ ℱ))
  where
    f = equivFun i

pos-of : Σ (Type ℓ₀) (RawFrameStr ℓ₁ ℓ₂) → Σ (Type ℓ₀) (Order ℓ₁)
pos-of (A , ((RPS , _) , _)) = (A , RPS)

top-of : (F : Σ (Type ℓ₀) (RawFrameStr ℓ₁ ℓ₂)) → π₀ F
top-of (_ , _ , 𝟏 , _) = 𝟏

RF-is-SNS : SNS {ℓ = ℓ} (RawFrameStr ℓ₁ ℓ₂) (RF-iso ℓ₁ ℓ₂)
RF-is-SNS {ℓ₁ = ℓ₁} {ℓ₂ = ℓ₂} {X = A} F@(P , 𝟏₀ , _⊓₀_ , ⋃₀) G@(Q , 𝟏₁ , _⊓₁_ , ⋃₁) =
  invEquiv (f , f-equiv)
  where
    C = RawFrameStr ℓ₁ ℓ₂ A

    _⊑₀_ : A → A → hProp ℓ₁
    x ⊑₀ y = x ⊑[ (A , P) ] y

    _⊑₁_ : A → A → hProp ℓ₁
    x ⊑₁ y = x ⊑[ (A , Q) ] y

    A-set₀ = carrier-is-set (A , P)

    PS-A = π₀ P
    PS-B = π₀ Q

    f : RF-iso ℓ₁ ℓ₂ (A , F) (A , G) (idEquiv A) → F ≡ G
    f (iₚ , eq-𝟏 , ⊓-xeq , ⋃-xeq) =
      P , 𝟏₀ , _⊓₀_ , ⋃₀   ≡⟨ cong (λ - → (P , - , _⊓₀_ , ⋃₀))              eq-𝟏 ⟩
      P , 𝟏₁ , _⊓₀_ , ⋃₀   ≡⟨ cong {B = λ _ → C} (λ - → P , 𝟏₁ , - , ⋃₀)    ⊓-eq ⟩
      P , 𝟏₁ , _⊓₁_ , ⋃₀   ≡⟨ cong {B = λ _ → C} (λ - → P , 𝟏₁ , _⊓₁_ , -)  ⋃-eq ⟩
      P , 𝟏₁ , _⊓₁_ , ⋃₁   ≡⟨ cong {B = λ _ → C} (λ - → - , 𝟏₁ , _⊓₁_ , ⋃₁) eq   ⟩
      Q , 𝟏₁ , _⊓₁_ , ⋃₁   ∎
      where
        eq : P ≡ Q
        eq = ΣProp≡ (poset-axioms-props A)
             (ΣProp≡ (λ _ → isPropIsSet)
                     (fn-ext _⊑₀_ _⊑₁_ λ x → fn-ext (_⊑₀_ x) (_⊑₁_ x) λ y →
                      ⇔toPath (proj₁ (iₚ x y)) (proj₂ (iₚ x y))))

        ⊓-eq : _⊓₀_ ≡ _⊓₁_
        ⊓-eq = fn-ext _⊓₀_ _⊓₁_ (λ x → fn-ext (_⊓₀_ x) (_⊓₁_ x) λ y → ⊓-xeq x y)

        ⋃-eq : ⋃₀ ≡ ⋃₁
        ⋃-eq = fn-ext ⋃₀ ⋃₁ λ ℱ → ⋃-xeq ℱ

    f-equiv : isEquiv f
    f-equiv = record { equiv-proof = λ eq → (g eq , ret eq) , h eq }
      where
        g : (eq : F ≡ G) → RF-iso ℓ₁ ℓ₂ (A , F) (A , G) (idEquiv A)
        g eq = φ , ψ , ϑ , ξ
          where
            𝒻  = equivFun (idEquiv A)

            φ : order-iso (A , _⊑₀_ , A-set₀) (A , _⊑₁_ , A-set₀) (idEquiv A)
            φ x y =
                (subst (λ { (((_⊑⋆_ , _) , _) , _) → (x ⊑⋆ y) is-true }) eq)
              , subst (λ { (((_⊑⋆_ , _) , _) , _) → (x ⊑⋆ y) is-true }) (sym eq)

            ψ : equivFun (idEquiv A) 𝟏₀ ≡ 𝟏₁
            ψ = subst (λ { (_ , - , _ , _) → 𝒻 - ≡ 𝟏₁ }) (sym eq) refl

            ϑ : (x y : A) → 𝒻 (x ⊓₀ y) ≡ (𝒻 x) ⊓₁ (𝒻 y)
            ϑ x y =
              subst (λ { (_ , _ , _-_ , _) → 𝒻 (x - y) ≡ (𝒻 x) ⊓₁ (𝒻 y) }) (sym eq) refl

            ξ : (ℱ : Sub ℓ₂ A) → 𝒻 (⋃₀ ℱ) ≡ ⋃₁ (index ℱ , λ i → 𝒻 (ℱ € i))
            ξ ℱ = subst (λ { (_ , _ , _ , -) → 𝒻 (- ℱ) ≡ ⋃₁ (𝒻 ⊚ ℱ) }) (sym eq) refl

        str-set : IsSet (RawFrameStr ℓ₁ ℓ₂ A)
        str-set =
          Σ-set (isOfHLevelΣ 2 OrderStr-set (prop⇒set ∘ poset-axioms-props A)) λ _ →
          isOfHLevelΣ 2 A-set₀ λ _ →
          isOfHLevelΣ 2 (∏-set (λ x → ∏-set λ y → A-set₀)) λ _ → ∏-set λ ℱ → A-set₀

        ret : (eq : F ≡ G) → f (g eq) ≡ eq
        ret eq = str-set F G (f (g eq)) eq

        RF-iso-prop : IsProp (RF-iso ℓ₁ ℓ₂ (A , F) (A , G) (idEquiv A))
        RF-iso-prop =
          isOfHLevelΣ 1 (RP-iso-prop (A , π₀ P) (A , π₀ Q) (idEquiv A)) (λ _ →
          isOfHLevelΣ 1 (λ p q → A-set₀ _ _ p q ) λ _ →
          isOfHLevelΣ 1 (∏-prop λ _ → ∏-prop λ _ → A-set₀ _ _) λ _ →
          ∏-prop λ _ → A-set₀ _ _)

        h : (eq : F ≡ G) → (fib : fiber f eq) → (g eq , ret eq) ≡ fib
        h eq (i , p) =
          ΣProp≡
            (λ x → hLevelSuc 2 (RawFrameStr ℓ₁ ℓ₂ A) str-set F G (f x) eq)
            (RF-iso-prop (g eq) i)

RF-is-SNS' : SNS' {ℓ = ℓ} (RawFrameStr ℓ₁ ℓ₂) (RF-iso ℓ₁ ℓ₂)
RF-is-SNS' {ℓ₁ = ℓ₁} {ℓ₂ = ℓ₂} = SNS→SNS' (RawFrameStr ℓ₁ ℓ₂) (RF-iso ℓ₁ ℓ₂) RF-is-SNS

frame-iso : (M N : Σ (Type ℓ₀) (FrameStr ℓ₁ ℓ₂)) → π₀ M ≃ π₀ N → Type (ℓ₀ ⊔ ℓ₁ ⊔ suc ℓ₂)
frame-iso {ℓ₁ = ℓ₁} {ℓ₂ = ℓ₂} = add-to-iso (RawFrameStr ℓ₁ ℓ₂) (RF-iso ℓ₁ ℓ₂) frame-axioms

frame-iso-prop : (M N : Frame ℓ₀ ℓ₁ ℓ₂) → (i : π₀ M ≃ π₀ N) → IsProp (frame-iso M N i)
frame-iso-prop F G i =
  isOfHLevelΣ 1 (RP-iso-prop RP RQ i) λ _ →
  isOfHLevelΣ 1 (carrier-is-set (pos G) _ _) λ _ →
  isOfHLevelΣ 1 (∏-prop λ x → ∏-prop λ y → carrier-is-set (pos G) _ _) λ _ →
                ∏-prop λ _ → carrier-is-set (pos G) _ _
  where
    RP = ∣ F ∣F , π₀ (strₚ (pos F))
    RQ = ∣ G ∣F , π₀ (strₚ (pos G))

frame-iso-Ω : (M N : Frame ℓ₀ ℓ₁ ℓ₂) → π₀ M ≃ π₀ N → hProp (ℓ₀ ⊔ ℓ₁ ⊔ suc ℓ₂)
frame-iso-Ω M N i = frame-iso M N i , frame-iso-prop M N i

frame-axioms-props : (A : Type ℓ₀) (F : RawFrameStr ℓ₁ ℓ₂ A) → IsProp (frame-axioms A F)
frame-axioms-props A (((_⊑_ , A-set) , _) , 𝟏 , _⊓_ , ⋃_) =
  isOfHLevelΣ 1 (∏-prop λ x → is-true-prop (x ⊑ 𝟏)) λ _ →
  isOfHLevelΣ 1 (∏-prop λ o → ∏-prop λ p → is-true-prop ((o ⊓ p) ⊑ o)) λ _ →
  isOfHLevelΣ 1 (∏-prop (λ o → ∏-prop λ p → is-true-prop ((o ⊓ p) ⊑ p))) λ _ →
  isOfHLevelΣ 1 (∏-prop λ o → ∏-prop λ p → ∏-prop λ q →
                 ∏-prop λ _ → ∏-prop λ _ → is-true-prop (q ⊑ (o ⊓ p))) λ _ →
  isOfHLevelΣ 1 (∏-prop λ ℱ → ∏-prop λ o → ∏-prop λ _ → is-true-prop (o ⊑ (⋃ ℱ))) λ _ →
  isOfHLevelΣ 1 (∏-prop λ ℱ → ∏-prop λ z → ∏-prop λ _ → is-true-prop ((⋃ ℱ) ⊑ z)) λ _ →
                 ∏-prop λ o → ∏-prop λ ℱ → A-set _ _

frame-is-SNS' : SNS' {ℓ = ℓ} (FrameStr ℓ₁ ℓ₂) frame-iso
frame-is-SNS' {ℓ₁ = ℓ₁} {ℓ₂ = ℓ₂} = add-axioms-SNS' _ _ _ frame-axioms-props RF-is-SNS'

frame-is-SNS'' : SNS'' {ℓ = ℓ} (FrameStr ℓ₁ ℓ₂) frame-iso
frame-is-SNS'' {ℓ₁ = ℓ₁} {ℓ₂ = ℓ₂} =
  subst id (SNS'≡SNS'' (FrameStr ℓ₁ ℓ₂) frame-iso) frame-is-SNS'

frame-is-SNS''' : SNS''' {ℓ = ℓ} (FrameStr ℓ₁ ℓ₂) frame-iso
frame-is-SNS''' = SNS''→SNS''' frame-is-SNS''

frame-SIP : (F G : Frame ℓ₀ ℓ₁ ℓ₂)
          → (eqv : ∣ F ∣F ≃ ∣ G ∣F)
          → frame-iso F G eqv
          → F ≡ G
frame-SIP {ℓ₁ = ℓ₁} {ℓ₂ = ℓ₂} F G eqv i = foo (eqv , i)
  where
    foo : F ≃[ frame-iso ] G → F ≡ G
    foo = equivFun (SIP (FrameStr ℓ₁ ℓ₂) frame-iso frame-is-SNS''' F G)

frame-iso→frame-iso' : (F G : Frame ℓ₀ ℓ₁ ℓ₂) (eqv : ∣ F ∣F ≃ ∣ G ∣F)
                         → poset-iso (pos F) (pos G) eqv → frame-iso F G eqv
frame-iso→frame-iso' {ℓ₂ = ℓ₂} F G eqv i = i , (𝟏-eq , ⊓-eq , ⋃-eq)
  where
    f = equivFun eqv
    g = equivFun (invEquiv eqv)

    ret : (y : ∣ G ∣F) → f (g y) ≡ y
    ret y = retEq eqv y 

    sec : (x : ∣ F ∣F) → g (f x) ≡ x
    sec = secEq eqv

    foo : (x y : ∣ F ∣F) → (x ⊑[ pos F ] y ⇔ (f x) ⊑[ pos G ] (f y)) is-true
    foo = i

    open PosetReasoning (pos G) using (_⊑⟨_⟩_; _■)
    open PosetReasoning (pos F) using () renaming (_⊑⟨_⟩_ to _⊑₁⟨_⟩_; _■ to _■₁)

    bar : (x y : ∣ G ∣F) → (x ⊑[ pos G ] y ⇔ (g x) ⊑[ pos F ] (g y)) is-true
    bar x y = β , α
      where
        φ : ((g x) ⊑[ pos F ] (g y) ⇔ (f (g x)) ⊑[ pos G ] (f (g y))) is-true
        φ = i (g x) (g y)

        α : ((g x) ⊑[ pos F ] (g y) ⇒ x ⊑[ pos G ] y) is-true
        α p = x       ⊑⟨ ≡⇒⊑ (pos G) (sym (ret x))  ⟩
              f (g x) ⊑⟨ proj₁ φ p                  ⟩
              f (g y) ⊑⟨ ≡⇒⊑ (pos G) (ret y)        ⟩
              y       ■

        β : x ⊑[ pos G ] y ⇒ (g x) ⊑[ pos F ] (g y) is-true
        β p = proj₂ φ eq
          where
            eq : f (g x) ⊑[ pos G ] f (g y) is-true
            eq = f (g x)  ⊑⟨ ≡⇒⊑ (pos G) (ret x)       ⟩
                 x        ⊑⟨ p                         ⟩
                 y        ⊑⟨ ≡⇒⊑ (pos G) (sym (ret y)) ⟩
                 f (g y)  ■


    𝟏-eq : f 𝟏[ F ] ≡ 𝟏[ G ]
    𝟏-eq = top-unique G (f 𝟏[ F ]) NTS
      where
        NTS : (o : ∣ G ∣F) → o ⊑[ pos G ] (f 𝟏[ F ]) is-true
        NTS o = proj₂ (bar o (f 𝟏[ F ])) eq
          where
            eq : g o ⊑[ pos F ] g (f 𝟏[ F ]) is-true
            eq = g o          ⊑₁⟨ 𝟏[ F ]-top (g o) ⟩
                 𝟏[ F ]       ⊑₁⟨ ≡⇒⊑ (pos F) (sym (sec 𝟏[ F ])) ⟩
                 g (f 𝟏[ F ]) ■₁

    ⊓-eq : (x y : ∣ F ∣F) →  f (x ⊓[ F ] y) ≡ (f x) ⊓[ G ] (f y)
    ⊓-eq x y = ⊓-unique G (f x) (f y) (f (x ⊓[ F ] y)) I II III
      where
        I : f (x ⊓[ F ] y) ⊑[ pos G ] f x is-true
        I = proj₂ (bar (f (x ⊓[ F ] y)) (f x)) NTS
          where
            NTS : g (f (x ⊓[ F ] y)) ⊑[ pos F ] g (f x) is-true
            NTS = g (f (x ⊓[ F ] y)) ⊑₁⟨ ≡⇒⊑ (pos F) (sec _)       ⟩
                  x ⊓[ F ] y         ⊑₁⟨ ⊓[ F ]-lower₀ x y         ⟩
                  x                  ⊑₁⟨ ≡⇒⊑ (pos F) (sym (sec x)) ⟩
                  g (f x)            ■₁

        II : f (x ⊓[ F ] y) ⊑[ pos G ] f y is-true
        II = proj₂ (bar (f (x ⊓[ F ] y)) (f y)) NTS
          where
            NTS : g (f (x ⊓[ F ] y)) ⊑[ pos F ] g (f y) is-true
            NTS = g (f (x ⊓[ F ] y)) ⊑₁⟨ ≡⇒⊑ (pos F) (sec _)       ⟩
                  x ⊓[ F ] y         ⊑₁⟨ ⊓[ F ]-lower₁ x y         ⟩
                  y                  ⊑₁⟨ ≡⇒⊑ (pos F) (sym (sec _)) ⟩
                  g (f y)            ■₁

        III : (z′ : ∣ G ∣F)
            → z′ ⊑[ pos G ] (f x) is-true
            → z′ ⊑[ pos G ] (f y) is-true
            → z′ ⊑[ pos G ] f (x ⊓[ F ] y) is-true
        III z′ p q = proj₂ (bar z′ (f (x ⊓[ F ] y))) NTS
          where
            gz′⊑x : g z′ ⊑[ pos F ] x is-true
            gz′⊑x =
              proj₂ (foo (g z′) x) (f (g z′) ⊑⟨ ≡⇒⊑ (pos G) (ret z′) ⟩ z′ ⊑⟨ p ⟩ f x ■)

            gz′⊑y : g z′ ⊑[ pos F ] y is-true
            gz′⊑y =
              proj₂ (foo (g z′) y) (f (g z′) ⊑⟨ ≡⇒⊑ (pos G) (ret z′) ⟩ z′ ⊑⟨ q ⟩ f y ■)

            NTS : g z′ ⊑[ pos F ] g (f (x ⊓[ F ] y)) is-true
            NTS = g z′               ⊑₁⟨ ⊓[ F ]-greatest x y (g z′) gz′⊑x gz′⊑y  ⟩
                  x ⊓[ F ] y         ⊑₁⟨ ≡⇒⊑ (pos F) (sym (sec _))               ⟩
                  g (f (x ⊓[ F ] y)) ■₁

    ⋃-eq : (ℱ : Sub ℓ₂ ∣ F ∣F) →  f (⋃[ F ] ℱ) ≡ ⋃[ G ] (index ℱ , λ i → f (ℱ € i))
    ⋃-eq ℱ = ⋃-unique G (f ⊚ ℱ) (f (⋃[ F ] ℱ)) NTS₀ NTS₁
      where
        NTS₀ : (o : ∣ G ∣F) → o ε (f ⊚ ℱ) → o ⊑[ pos G ] (f (⋃[ F ] ℱ)) is-true
        NTS₀ o (i , p) =
          proj₂
            (bar o (f (⋃[ F ] ℱ)))
            (g o              ⊑₁⟨ ⋃[ F ]-upper ℱ (g o) I ⟩
             ⋃[ F ] ℱ         ⊑₁⟨ ≡⇒⊑ (pos F) (sym (sec _)) ⟩
             g (f (⋃[ F ] ℱ)) ■₁)
          where
            I : g o ε ℱ
            I = i , (ℱ € i ≡⟨ sym (sec _) ⟩ g (f (ℱ € i)) ≡⟨ cong g p ⟩ g o ∎)

        NTS₁ : (z′ : ∣ G ∣F)
             → ((o : ∣ G ∣F) → o ε (f ⊚ ℱ) → rel (pos G) o z′ is-true)
             → f (⋃[ F ] ℱ) ⊑[ pos G ] z′ is-true
        NTS₁ z′ p =
          proj₂
            (bar (f (⋃[ F ] ℱ)) z′)
            (g (f (⋃[ F ] ℱ)) ⊑₁⟨ ≡⇒⊑ (pos F) (sec _)       ⟩
             ⋃[ F ] ℱ         ⊑₁⟨ ⋃[ F ]-least ℱ (g z′) NTS ⟩
             g z′             ■₁)
          where
            NTS : (o : ∣ F ∣F) → o ε ℱ → o ⊑[ pos F ] (g z′) is-true
            NTS o (i , εℱ) =
              proj₂
                (foo o (g z′))
                (f o ⊑⟨ p (f o) foεf⊚ℱ ⟩ z′ ⊑⟨ ≡⇒⊑ (pos G) (sym (ret _)) ⟩ f (g z′) ■)
              where
                foεf⊚ℱ : f o ε (f ⊚ ℱ)
                foεf⊚ℱ = i , (f ⊚ ℱ € i ≡⟨ refl ⟩ f (ℱ € i) ≡⟨ cong f εℱ ⟩ f o ∎)

_≃f_ : Frame ℓ₀ ℓ₁ ℓ₂ → Frame ℓ₀ ℓ₁ ℓ₂ → Type (ℓ₀ ⊔ ℓ₁)
F ≃f G = Σ[ i ∈ (∣ F ∣F ≃ ∣ G ∣F) ] poset-iso (pos F) (pos G) i

-- This is the weak form of univalence.
frame-univ : (F G : Frame ℓ₀ ℓ₁ ℓ₂) → F ≃f G → F ≡ G
frame-univ F G (eqv , iso-f) = frame-SIP F G eqv (frame-iso→frame-iso' F G eqv iso-f)

-- -}
-- -}
-- -}
