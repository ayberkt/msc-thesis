{-# OPTIONS --without-K --cubical --safe #-}

open import Truncation

module Frame where

open import Basis
open import Family
open import Truncation
open import Function                using    (_∘_; id)
open import Data.Product            using    (uncurry)
open import Cubical.Foundations.SIP renaming (SNS-≡ to SNS)
open import Poset
open import Powerset

module JoinSyntax (A : Type ℓ₀) {ℓ₂ : Level} (join : Fam ℓ₂ A → A) where

  join-of : {I : Type ℓ₂} → (I → A) → A
  join-of {I = I} f = join (I , f)

  syntax join-of (λ i → e) = ⋁⟨ i ⟩ e


RawFrameStr : (ℓ₁ ℓ₂ : Level) → Type ℓ₀ → Type (ℓ₀ ⊔ suc ℓ₁ ⊔ suc ℓ₂)
RawFrameStr ℓ₁ ℓ₂ A = PosetStr ℓ₁ A × A × (A → A → A) × (Fam ℓ₂ A → A)

isTop : (P : Poset ℓ₀ ℓ₁) → ∣ P ∣ₚ → hProp (ℓ₀ ⊔ ℓ₁)
isTop P x = ((y : ∣ P ∣ₚ) → [ y ⊑[ P ] x ]) , isPropΠ λ y → is-true-prop (y ⊑[ P ] x)

isGLB : (P : Poset ℓ₀ ℓ₁) → (∣ P ∣ₚ → ∣ P ∣ₚ → ∣ P ∣ₚ) → hProp (ℓ₀ ⊔ ℓ₁)
isGLB P _∧_ = ∧-GLB , ∧-GLB-prop
  where
    ∧-GLB = -- x ∧ y is a lower bound of {x, y}.
        ((x y    : ∣ P ∣ₚ) → [ (x ∧ y) ⊑[ P ] x ⊓ (x ∧ y) ⊑[ P ] y ])
        -- Given any other lower bound z of {x, y}, x ∧ y is _greater_ than that.
      × ((x y z  : ∣ P ∣ₚ) → [ (z ⊑[ P ] x ⊓ z ⊑[ P ] y) ⇒  z ⊑[ P ] (x ∧ y) ])

    ∧-GLB-prop : isProp ∧-GLB
    ∧-GLB-prop =
      isPropΣ
        (isPropΠ2 λ x y → is-true-prop ((x ∧ y) ⊑[ P ] x ⊓ (x ∧ y) ⊑[ P ] y)) λ _ →
        isPropΠ3 λ x y z → is-true-prop (z ⊑[ P ] x ⊓ z ⊑[ P ] y ⇒ z ⊑[ P ] (x ∧ y))

isLUB : (P : Poset ℓ₀ ℓ₁) → (Fam ℓ₂ ∣ P ∣ₚ → ∣ P ∣ₚ) → hProp (ℓ₀ ⊔ ℓ₁ ⊔ suc ℓ₂)
isLUB {ℓ₂ = ℓ₂} P ⋁_ = ⋁-LUB , ⋁-LUB-prop
  where
    ⋁-LUB = ((U : Fam ℓ₂ ∣ P ∣ₚ) → [ ∀[ x ε U ] (x ⊑[ P ] ⋁ U) ])
          × ((U : Fam ℓ₂ ∣ P ∣ₚ) (x : _) → [ (∀[ y ε U ] (y ⊑[ P ] x)) ⇒ ⋁ U ⊑[ P ] x ])

    ⋁-LUB-prop : isProp ⋁-LUB
    ⋁-LUB-prop = isPropΣ
                   (λ ψ ϑ → funExt λ U →
                     is-true-prop (∀[ y ε U ] (y ⊑[ P ] ⋁ U)) (ψ U) (ϑ U)) λ _ →
                   isPropΠ λ U → isPropΠ λ x →
                     is-true-prop (∀[ y ε U ] (y ⊑[ P ] x) ⇒ (⋁ U) ⊑[ P ] x)

isDist : (P : Poset ℓ₀ ℓ₁)
       → (∣ P ∣ₚ → ∣ P ∣ₚ → ∣ P ∣ₚ)
       → (Fam ℓ₂ ∣ P ∣ₚ → ∣ P ∣ₚ)
       → hProp (ℓ₀ ⊔ suc ℓ₂)
isDist {ℓ₂ = ℓ₂} P _⊓_ ⋁_ = ∧-dist-over-⋁ , ∧-dist-over-⋁-prop
  where
    open JoinSyntax ∣ P ∣ₚ ⋁_

    ∧-dist-over-⋁ = (x : ∣ P ∣ₚ) (U : Fam ℓ₂ ∣ P ∣ₚ) → x ⊓ (⋁ U) ≡ ⋁⟨ i ⟩ (x ⊓ (U $ i))

    ∧-dist-over-⋁-prop : isProp ∧-dist-over-⋁
    ∧-dist-over-⋁-prop p q = funExt2 (λ x U → carrier-is-set P _ _ (p x U) (q x U))

FrameAx : {A : Type ℓ₀} → RawFrameStr ℓ₁ ℓ₂ A → hProp (ℓ₀ ⊔ ℓ₁ ⊔ suc ℓ₂)
FrameAx {ℓ₀ = ℓ₀} {ℓ₁ = ℓ₁} {A = A} (s@(_⊑_ , _) , ⊤ , _∧_ , ⋁_) =
  isTop P ⊤ ⊓ isGLB P _∧_ ⊓ isLUB P ⋁_ ⊓ isDist P _∧_ ⋁_
  where
    P : Poset ℓ₀ ℓ₁
    P = A , s

FrameStr : (ℓ₁ ℓ₂ : Level) → Type ℓ₀ → Type (ℓ₀ ⊔ suc ℓ₁ ⊔ suc ℓ₂)
FrameStr ℓ₁ ℓ₂ = add-to-structure (RawFrameStr ℓ₁ ℓ₂) λ _ RF → [ FrameAx RF ]

Frame : (ℓ₀ ℓ₁ ℓ₂ : Level) → Type (suc ℓ₀ ⊔ suc ℓ₁ ⊔ suc ℓ₂)
Frame ℓ₀ ℓ₁ ℓ₂ = Σ (Type ℓ₀) (FrameStr ℓ₁ ℓ₂)

-- Projection for the carrier set of a frame
-- i.e., the carrier set of the underlying poset.
∣_∣F : Frame ℓ₀ ℓ₁ ℓ₂ → Type ℓ₀
∣ A , _ ∣F = A

-- The underlying poset of a frame.
pos : Frame ℓ₀ ℓ₁ ℓ₂ → Poset ℓ₀ ℓ₁
pos (A , (P , _) , _) = A , P

-- Projections for the top element, meet, and join of a frame.

⊤[_] : (F : Frame ℓ₀ ℓ₁ ℓ₂) → ∣ F ∣F
⊤[ _ , (_ , (⊤ , _)) , _ ] = ⊤

glb-of : (F : Frame ℓ₀ ℓ₁ ℓ₂) → ∣ F ∣F → ∣ F ∣F → ∣ F ∣F
glb-of (_ , (_ , _ , _⊓_ , _) , _) = _⊓_

syntax glb-of F x y = x ⊓[ F ] y

⋁[_]_ : (F : Frame ℓ₀ ℓ₁ ℓ₂) → Fam ℓ₂ ∣ F ∣F → ∣ F ∣F
⋁[ (_ , (_ , (_ , _ , ⋁_)) , _) ] U = ⋁ U

-- Projections for frame laws.

module _ (F : Frame ℓ₀ ℓ₁ ℓ₂) where
  private
    P = pos F

    _⊑_ : ∣ F ∣F → ∣ F ∣F → hProp ℓ₁
    x ⊑ y = x ⊑[ P ] y

    open JoinSyntax ∣ F ∣F (λ - → ⋁[ F ] -)

  ⊤[_]-top : (x : ∣ F ∣F) → [ x ⊑ ⊤[ F ] ]
  ⊤[_]-top = let (_ , _ , frame-str) = F in π₀ frame-str

  ⊓[_]-lower₀ : (x y : ∣ F ∣F) → [ (x ⊓[ F ] y) ⊑ x ]
  ⊓[_]-lower₀ = let (_ , _ , str) = F in λ x y → π₀ (π₀ (π₀ (π₁ str)) x y)


  ⊓[_]-lower₁ : (x y : ∣ F ∣F) → [ (x ⊓[ F ] y) ⊑ y ]
  ⊓[_]-lower₁ = let (_ , _ , str) = F in λ x y → π₁ (π₀ (π₀ (π₁ str)) x y)

  ⊓[_]-greatest : (x y z : ∣ F ∣F) → [ z ⊑ x ] → [ z ⊑ y ] → [ z ⊑ (x ⊓[ F ] y) ]
  ⊓[_]-greatest =
    let (_ , _ , str) = F in λ x y z z⊑x z⊑y → π₁ (π₀ (π₁ str)) x y z (z⊑x , z⊑y)

  ⋁[_]-upper : (U : Fam ℓ₂ ∣ F ∣F) (o : ∣ F ∣F) → o ε U → [ o ⊑ (⋁[ F ] U) ]
  ⋁[_]-upper = let (_ , _ , str) = F in π₀ (π₀ (π₁ (π₁ str)))

  ⋁[_]-least : (U : Fam ℓ₂ ∣ F ∣F) (x : ∣ F ∣F)
             → [ ∀[ y ε U ] (y ⊑ x) ] → [ (⋁[ F ] U) ⊑ x ]
  ⋁[_]-least = let (_ , _ , str) = F in π₁ (π₀ (π₁ (π₁ str)))

  dist : (x : ∣ F ∣F) (U : Fam ℓ₂ ∣ F ∣F)
       → x ⊓[ F ] (⋁⟨ i ⟩ (U $ i)) ≡ ⋁⟨ i ⟩ (x ⊓[ F ] (U $ i))
  dist = let (_ , _ , str) = F in π₁ (π₁ (π₁ str))

  top-unique : (y : ∣ F ∣F) → ((x : ∣ F ∣F) → [ x ⊑ y ]) → y ≡ ⊤[ F ]
  top-unique y y-top = ⊑[ pos F ]-antisym y ⊤[ F ] (⊤[_]-top y) (y-top ⊤[ F ])

  ⊓-unique : (x y z : ∣ F ∣F)
           → [ z ⊑ x ] → [ z ⊑ y ] → ((w : ∣ F ∣F) → [ w ⊑ x ] → [ w ⊑ y ] → [ w ⊑ z ])
           → z ≡ x ⊓[ F ] y
  ⊓-unique x y z z⊑x z⊑y greatest =
    ⊑[ P ]-antisym z (x ⊓[ F ] y) (⊓[_]-greatest x y z z⊑x z⊑y) NTS
    where
      NTS : [ (x ⊓[ F ] y) ⊑ z ]
      NTS = greatest (x ⊓[ F ] y) (⊓[_]-lower₀ x y) (⊓[_]-lower₁ x y)

  ⋁-unique : (U : Fam ℓ₂ ∣ F ∣F) (z : ∣ F ∣F)
           → ((x : ∣ F ∣F) → x ε U → [ x ⊑ z ])
           → ((w : ∣ F ∣F) → ((o : ∣ F ∣F) → o ε U → [ o ⊑ w ]) → [ z ⊑ w ])
           → z ≡ ⋁[ F ] U
  ⋁-unique U z upper least =
    ⊑[ P ]-antisym z (⋁[ F ] U) (least (⋁[ F ] U) (⋁[_]-upper U)) NTS
    where
      NTS : [ (⋁[ F ] U) ⊑ z ]
      NTS = ⋁[_]-least U z upper

  comm : (x y : ∣ F ∣F) → x ⊓[ F ] y ≡ y ⊓[ F ] x
  comm x y = ⊓-unique y x _ (⊓[_]-lower₁ x y) (⊓[_]-lower₀ x y) NTS
    where
      NTS = λ w w⊑y w⊑x → ⊓[_]-greatest x y w w⊑x w⊑y

  family-iff : {U V : Fam ℓ₂ ∣ F ∣F}
             → ((x : ∣ F ∣F) → (x ε U → x ε V) × (x ε V → x ε U))
             → ⋁[ F ] U ≡ ⋁[ F ] V
  family-iff {U = U} {V = V} h = ⋁-unique _ _ ub least
    where
      ub : (o : ∣ F ∣F) → o ε V → [ o ⊑ (⋁[ F ] U) ]
      ub o (i , p) =
        subst (λ - → [ - ⊑ _ ]) p (⋁[ _ ]-upper _ (π₁ (h (V $ i)) (i , refl)))

      least : (w : ∣ F ∣F)
            → ((o : ∣ F ∣F) → o ε V → [ o ⊑ w ])
            → [ (⋁[ F ] U) ⊑ w ]
      least w f = ⋁[ _ ]-least _ λ o oεU → f o (π₀ (h o) oεU)

  flatten : (I : Type ℓ₂) (J : I → Type ℓ₂) (f : (i : I) → J i → ∣ F ∣F)
          → ⋁[ F ] (Σ I J , uncurry f) ≡ ⋁[ F ] ⁅ ⋁[ F ] (J i , λ j → f i j) ∣ i ∶ I ⁆
  flatten I J f = ⊑[ pos F ]-antisym _ _ down up
    where
      open PosetReasoning (pos F)

      LHS = ⋁[ F ] (Σ I J , uncurry f)
      RHS = ⋁[ F ] (I , (λ i → ⋁[ F ] (J i , f i)))

      down : [ LHS ⊑ RHS ]
      down = ⋁[_]-least _ _ isUB
        where
          isUB : (x : ∣ F ∣F) → x ε (Σ I J , uncurry f) → [ x ⊑ RHS ]
          isUB x ((i , j) , eq) =
              x                          ⊑⟨ ≡⇒⊑ (pos F) (sym eq)      ⟩
              f i j                      ⊑⟨ ⋁[_]-upper _ _ (j , refl) ⟩
              ⋁[ F ] (J i , λ - → f i -) ⊑⟨ ⋁[_]-upper _ _ (i , refl) ⟩
              RHS                        ■

      up : [ RHS ⊑ LHS ]
      up = ⋁[_]-least _ _ isUB
        where
          isUB : (x : ∣ F ∣F)
               → x ε ⁅ ⋁[ F ] (J i , f i) ∣ i ∶ I ⁆ → [ x ⊑ (⋁[ F ] (Σ I J , uncurry f)) ]
          isUB x (i , p) =
            x                          ⊑⟨ ≡⇒⊑ (pos F) (sym p)  ⟩
            ⋁[ F ] ⁅ f i j ∣ j ∶ J i ⁆ ⊑⟨ ⋁[_]-least _ _ isUB′ ⟩
            ⋁[ F ] (Σ I J , uncurry f) ■
            where
              isUB′ : (z : ∣ F ∣F) → z ε ⁅ f i j ∣ j ∶ J i ⁆ → [ z ⊑ LHS ]
              isUB′ z (j , q) = ⋁[_]-upper _ _ ((i , j) , q)

  sym-distr : (U@(I , _) V@(J , _) : Fam ℓ₂ ∣ F ∣F)
            → (⋁⟨ i ⟩ (U $ i)) ⊓[ F ] (⋁⟨ i ⟩ (V $ i))
            ≡ ⋁[ F ] ⁅ (U $ i) ⊓[ F ] (V $ j) ∣ (i , j) ∶ (I × J) ⁆
  sym-distr U@(I , _) V@(J , _) =
    (⋁[ F ] U) ⊓[ F ] (⋁[ F ] V)
      ≡⟨ dist (⋁[ F ] U) V ⟩
    ⋁[ F ] ((λ - → (⋁[ F ] U) ⊓[ F ] -) ⟨$⟩ V)
      ≡⟨ cong (λ - → ⋁[ F ] (- ⟨$⟩ V)) NTS₀ ⟩
    ⋁[ F ] ((λ x → x ⊓[ F ] (⋁[ F ] U)) ⟨$⟩ V)
      ≡⟨ cong (λ - → ⋁[ F ] (- ⟨$⟩ V)) NTS₁ ⟩
    ⋁[ F ] ((λ x → ⋁[ F ] ((λ y → x ⊓[ F ] y) ⟨$⟩ U)) ⟨$⟩ V)
      ≡⟨ sym (flatten (index V) (λ _ → index U) λ j i →  (V $ j) ⊓[ F ] (U $ i))  ⟩
    ⋁[ F ] ⁅ (V $ j) ⊓[ F ] (U $ i) ∣ (j , i) ∶ (J × I) ⁆
      ≡⟨ family-iff NTS₂  ⟩
    ⋁[ F ] ⁅ (U $ i) ⊓[ F ] (V $ j) ∣ (i , j) ∶ (I × J) ⁆
      ∎
    where
      open PosetReasoning (pos F)

      NTS₀ : (λ - → (⋁[ F ] U) ⊓[ F ] -) ≡ (λ - → - ⊓[ F ] (⋁[ F ] U))
      NTS₀ = funExt λ x → comm (⋁[ F ] U) x

      NTS₁ : (λ - → - ⊓[ F ] (⋁[ F ] U)) ≡ (λ - → ⋁[ F ] ((λ y → - ⊓[ F ] y) ⟨$⟩ U))
      NTS₁ = funExt λ x → dist x U

      NTS₂ : _
      NTS₂ x = down , up
        where
          down : _
          down ((j , i) , eq) =
            subst
              (λ - → x ε (_ , -))
              (funExt (λ { (i′ , j′) → comm (V $ j′) (U $ i′) })) ((i , j) , eq)

          up : _
          up ((i , j) , eq) =
            subst
              (λ - → x ε (_ , -))
              (funExt (λ { (j′ , i′) → comm (U $ i′) (V $ j′) })) ((j , i) , eq)

-- Frame homomorphisms.
isFrameHomomorphism : (F : Frame ℓ₀ ℓ₁ ℓ₂) (G : Frame ℓ₀′ ℓ₁′ ℓ₂)
                    → (pos F ─m→ pos G)
                    → Type (ℓ₀ ⊔ suc ℓ₂ ⊔ ℓ₀′)
isFrameHomomorphism {ℓ₂ = ℓ₂} F G (f , _) = resp-⊤ × resp-⊓ × resp-⋁
  where
    resp-⊤ : Type _
    resp-⊤ = f ⊤[ F ] ≡ ⊤[ G ]

    resp-⊓ : Type _
    resp-⊓ = (x y : ∣ F ∣F) → f (x ⊓[ F ] y) ≡ (f x) ⊓[ G ] (f y)

    resp-⋁ : Type _
    resp-⋁ = (U : Fam ℓ₂ ∣ F ∣F) → f (⋁[ F ] U) ≡ ⋁[ G ] ⁅ f x ∣ x ε U ⁆

isFrameHomomorphism-prop : (F : Frame ℓ₀ ℓ₁ ℓ₂) (G : Frame ℓ₀′ ℓ₁′ ℓ₂)
                         → (f : pos F ─m→ pos G)
                         → isProp (isFrameHomomorphism F G f)
isFrameHomomorphism-prop F G f =
  isPropΣ (carrier-is-set (pos G) _ _) λ _ →
  isPropΣ (isPropΠ2 λ x y → carrier-is-set (pos G) _ _) λ _ →
  isPropΠ λ U → carrier-is-set (pos G) _ _

_─f→_ : Frame ℓ₀ ℓ₁ ℓ₂ → Frame ℓ₀′ ℓ₁′ ℓ₂ → Type (ℓ₀ ⊔ ℓ₁ ⊔ suc ℓ₂ ⊔ ℓ₀′ ⊔ ℓ₁′)
_─f→_ {ℓ₂ = ℓ₂} F G = Σ (pos F ─m→ pos G) (isFrameHomomorphism F G)

_$f_ : {F G : Frame ℓ₀ ℓ₁ ℓ₂} → F ─f→ G → ∣ F ∣F → ∣ G ∣F
(f , _) $f x = f $ₘ x

-- An element of the poset is like a finite observation whereas an element of the
-- frame of downward closed posets is like a general observation.

-- The set of downward-closed subsets of a poset forms a frame.
DCPoset : (P : Poset ℓ₀ ℓ₁) → Poset (suc ℓ₀ ⊔ ℓ₁) ℓ₀
DCPoset {ℓ₀ = ℓ₀} P = 𝔻 , _<<_ , 𝔻-set , <<-refl , <<-trans  , <<-antisym
  where
    𝔻     = DCSubset     P
    𝔻-set = DCSubset-set P

    _<<_ : 𝔻 → 𝔻 → hProp ℓ₀
    _<<_ (S , _) (T , _) = S ⊆ T

    abstract
      <<-refl : [ isReflexive _<<_ ]
      <<-refl (U , U-down) x xεU = xεU

      <<-trans : [ isTransitive _<<_ ]
      <<-trans _ _ _ S<<T T<<U x xεS = T<<U x (S<<T x xεS)

      <<-antisym : [ isAntisym 𝔻-set _<<_ ]
      <<-antisym X Y S⊆T T⊆S =
        ΣProp≡ (is-true-prop ∘ isDownwardsClosed P) (⊆-antisym S⊆T T⊆S)

-- The set of downward-closed subsets of a poset forms a frame.
DCFrame : (P : Poset ℓ₀ ℓ₁) → Frame (suc ℓ₀ ⊔ ℓ₁) ℓ₀ ℓ₀
DCFrame {ℓ₀ = ℓ₀} {ℓ₁ = ℓ₁} (X , P) =
    𝔻
  , (strₚ 𝔻ₚ , ⊤ , (_∧_ , ⋁_))
  , ⊤-top
  , ( (λ x y → ⊓-lower₀ x y , ⊓-lower₁ x y)
    , λ { x y z (z⊑x , z⊑y) → ⊓-greatest x y z z⊑x z⊑y })
  , (⊔-upper , ⊔-least)
  , distr
  where
    𝔻ₚ = DCPoset (X , P)
    𝔻  = ∣ 𝔻ₚ ∣ₚ

    -- Function that forget the downwards-closure information.
    ∣_∣𝔻 : 𝔻 → 𝒫 X
    ∣ S , _ ∣𝔻 = S

    ⊤ = (λ _ → Unit ℓ₀ , Unit-prop) , λ _ _ _ _ → tt

    ∩-down : (S T : 𝒫 X)
           → [ isDownwardsClosed (X , P) S ]
           → [ isDownwardsClosed (X , P) T ]
           → [ isDownwardsClosed (X , P) (S ∩ T) ]
    ∩-down S T S↓ T↓ x y x∈S∩T y⊑x = S↓ x y (π₀ x∈S∩T) y⊑x , T↓ x y (π₁ x∈S∩T) y⊑x

    _∧_ : 𝔻 → 𝔻 → 𝔻
    (S , S-dc) ∧ (T , T-dc) = (S ∩ T) , ∩-down S T S-dc T-dc

    ⊤-top : (D : 𝔻) → [ D ⊑[ 𝔻ₚ ] ⊤ ]
    ⊤-top D _ _ = tt

    -- Given a family U over 𝔻 and some x : X, `in-some-set U x` holds iff there is some
    -- set S among U such that x ∈ S.
    in-some-set-of : (U : Fam ℓ₀ 𝔻) → X → Type ℓ₀
    in-some-set-of U x = Σ[ i ∈ index U ] [ x ∈ ∣ U $ i ∣𝔻 ]

    ⋁_ : Fam ℓ₀ 𝔻 → 𝔻
    ⋁ U = (λ x → ∥ in-some-set-of U x ∥ , ∥∥-prop _) , ⊔U↓
      where
        NTS : (x y : X)
            → [ y ⊑[ (X , P) ] x ] → in-some-set-of U x → ∥ in-some-set-of U y ∥
        NTS x y y⊑x (i , x∈Uᵢ) = ∣ i , π₁ (U $ i) x y x∈Uᵢ y⊑x ∣

        ⊔U↓ : [ isDownwardsClosed (X , P) (λ x → ∥ in-some-set-of U x ∥ , ∥∥-prop _) ]
        ⊔U↓ x y ∣p∣ y⊑x = ∥∥-rec (∥∥-prop _) (NTS x y y⊑x) ∣p∣

    open JoinSyntax 𝔻 ⋁_

    ⊔-upper : (U : Fam ℓ₀ 𝔻) (D : 𝔻) → D ε U → [ D ⊑[ 𝔻ₚ ] (⋁ U) ]
    ⊔-upper U D DεS@(i , p) x x∈D = ∣ i , subst (λ V → [ ∣ V ∣𝔻 x ]) (sym p) x∈D ∣

    ⊔-least : (U : Fam ℓ₀ 𝔻) (z : 𝔻) → [ ∀[ x ε U ] (x ⊑[ 𝔻ₚ ] z) ] → [ (⋁ U) ⊑[ 𝔻ₚ ] z ]
    ⊔-least U D φ x x∈⊔S = ∥∥-rec (∈-prop ∣ D ∣𝔻) NTS x∈⊔S
      where
        NTS : in-some-set-of U x → [ x ∈ ∣ D ∣𝔻 ]
        NTS (i , x∈Uᵢ) = φ (U $ i) (i , refl) x x∈Uᵢ

    ⊓-lower₀ : (U V : 𝔻) → [ (U ∧ V) ⊑[ 𝔻ₚ ] U ]
    ⊓-lower₀ _ _ _ (x∈U , _) = x∈U

    ⊓-lower₁ : (U V : 𝔻) → [ (U ∧ V) ⊑[ 𝔻ₚ ] V ]
    ⊓-lower₁ _ _ _ (_ , x∈V) = x∈V

    ⊓-greatest : (U V W : 𝔻) → [ W ⊑[ 𝔻ₚ ] U ] → [ W ⊑[ 𝔻ₚ ] V ] → [ W ⊑[ 𝔻ₚ ] (U ∧ V) ]
    ⊓-greatest U V W W<<U W<<V x x∈W = (W<<U x x∈W) , (W<<V x x∈W)

    distr : (U : 𝔻) (V : Fam ℓ₀ 𝔻) → U ∧ (⋁ V) ≡ ⋁⟨ i ⟩ (U ∧ (V $ i))
    distr U V@(I , _) = ⊑[ 𝔻ₚ ]-antisym _ _ down up
      where
        LHS = ∣ U ∧ (⋁ V) ∣𝔻
        RHS = ∣ ⋁⟨ i ⟩ (U ∧ (V $ i)) ∣𝔻

        down : [ LHS ⊆ RHS ]
        down x (x∈D , x∈⊔U) =
          ∥∥-rec (∥∥-prop _) (λ { (i , x∈Uᵢ) → ∣ i , x∈D , x∈Uᵢ ∣ }) x∈⊔U

        up : [ RHS ⊆ LHS ]
        up x = ∥∥-rec (is-true-prop (x ∈ LHS)) φ
          where
            φ : in-some-set-of ⁅ U ∧ (V $ i) ∣ i ∶ I ⁆ x → [ ∣ U ∣𝔻 x ] × [ ∣ ⋁ V ∣𝔻 x ]
            φ (i , x∈D , x∈Uᵢ) = x∈D , ∣ i , x∈Uᵢ ∣

-- Frames form an SNS.

RF-iso : {ℓ₁ ℓ₂ : Level} (M N : Σ (Type ℓ₀) (RawFrameStr ℓ₁ ℓ₂))
       → π₀ M ≃ π₀ N → Type (ℓ₀ ⊔ ℓ₁ ⊔ suc ℓ₂)
RF-iso {ℓ₂ = ℓ₂} (A , (P , _) , ⊤₀ , _⊓₀_ , ⋁₀) (B , (Q , _), ⊤₁ , _⊓₁_ , ⋁₁) i =
    (order-iso (A , P) (B , Q) i)
  × (f ⊤₀ ≡ ⊤₁)
  × ((x y : A) → f (x ⊓₀ y) ≡ (f x) ⊓₁ (f y))
  × ((U : Fam ℓ₂ A) → f (⋁₀ U) ≡ ⋁₁ (f ⟨$⟩ U))
  where
    f = equivFun i

pos-of : Σ (Type ℓ₀) (RawFrameStr ℓ₁ ℓ₂) → Σ (Type ℓ₀) (Order ℓ₁)
pos-of (A , ((RPS , _) , _)) = (A , RPS)

top-of : (F : Σ (Type ℓ₀) (RawFrameStr ℓ₁ ℓ₂)) → π₀ F
top-of (_ , _ , ⊤ , _) = ⊤

RF-is-SNS : SNS {ℓ₀} (RawFrameStr ℓ₁ ℓ₂) RF-iso
RF-is-SNS {ℓ₁ = ℓ₁} {ℓ₂ = ℓ₂} {X = A} F@(P , ⊤₀ , _⊓₀_ , ⋁₀) G@(Q , ⊤₁ , _⊓₁_ , ⋁₁) =
  f , f-equiv
  where
    C = RawFrameStr ℓ₁ ℓ₂ A

    _⊑₀_ : A → A → hProp ℓ₁
    x ⊑₀ y = x ⊑[ (A , P) ] y

    _⊑₁_ : A → A → hProp ℓ₁
    x ⊑₁ y = x ⊑[ (A , Q) ] y

    A-set₀ = carrier-is-set (A , P)

    PS-A = π₀ P
    PS-B = π₀ Q

    f : RF-iso (A , F) (A , G) (idEquiv A) → F ≡ G
    f (iₚ , eq-⊤ , ⊓-xeq , ⋁-xeq) =
      P , ⊤₀ , _⊓₀_ , ⋁₀   ≡⟨ cong (λ - → (P , - , _⊓₀_ , ⋁₀))              eq-⊤ ⟩
      P , ⊤₁ , _⊓₀_ , ⋁₀   ≡⟨ cong {B = λ _ → C} (λ - → P , ⊤₁ , - , ⋁₀)    ⊓-eq ⟩
      P , ⊤₁ , _⊓₁_ , ⋁₀   ≡⟨ cong {B = λ _ → C} (λ - → P , ⊤₁ , _⊓₁_ , -)  ⋁-eq ⟩
      P , ⊤₁ , _⊓₁_ , ⋁₁   ≡⟨ cong {B = λ _ → C} (λ - → - , ⊤₁ , _⊓₁_ , ⋁₁) eq   ⟩
      Q , ⊤₁ , _⊓₁_ , ⋁₁   ∎
      where
        eq : P ≡ Q
        eq = ΣProp≡
               (poset-axioms-props A)
               (funExt λ x → funExt λ y → ⇔toPath (π₀ (iₚ x y)) (π₁ (iₚ x y)))

        ⊓-eq : _⊓₀_ ≡ _⊓₁_
        ⊓-eq = funExt (λ x → funExt λ y → ⊓-xeq x y)

        ⋁-eq : ⋁₀ ≡ ⋁₁
        ⋁-eq = funExt λ U → ⋁-xeq U

    f-equiv : isEquiv f
    f-equiv = record { equiv-proof = λ eq → (g eq , ret eq) , h eq }
      where
        g : (eq : F ≡ G) → RF-iso (A , F) (A , G) (idEquiv A)
        g eq = φ , ψ , ϑ , ξ
          where
            𝒻  = equivFun (idEquiv A)

            φ : order-iso (A , _⊑₀_) (A , _⊑₁_) (idEquiv A)
            φ x y =
                (subst (λ { ((_⊑⋆_ , _) , _) → [ x ⊑⋆ y ] }) eq)
              , subst (λ { ((_⊑⋆_ , _) , _) → [ x ⊑⋆ y ] }) (sym eq)

            ψ : equivFun (idEquiv A) ⊤₀ ≡ ⊤₁
            ψ = subst (λ { (_ , - , _ , _) → 𝒻 - ≡ ⊤₁ }) (sym eq) refl

            ϑ : (x y : A) → 𝒻 (x ⊓₀ y) ≡ (𝒻 x) ⊓₁ (𝒻 y)
            ϑ x y =
              subst (λ { (_ , _ , _-_ , _) → 𝒻 (x - y) ≡ (𝒻 x) ⊓₁ (𝒻 y) }) (sym eq) refl

            ξ : (U : Fam ℓ₂ A) → 𝒻 (⋁₀ U) ≡ ⋁₁ (index U , λ i → 𝒻 (U $ i))
            ξ U = subst (λ { (_ , _ , _ , -) → 𝒻 (- U) ≡ ⋁₁ (𝒻 ⟨$⟩ U) }) (sym eq) refl

        str-set : isSet (RawFrameStr ℓ₁ ℓ₂ A)
        str-set = isSetΣ (PosetStr-set ℓ₁ A) λ _ →
                  isSetΣ A-set₀ λ _ →
                  isSetΣ (isSetΠ λ _ → isSetΠ λ _ → A-set₀) λ _ → isSetΠ λ _ → A-set₀

        ret : (eq : F ≡ G) → f (g eq) ≡ eq
        ret eq = str-set F G (f (g eq)) eq

        RF-iso-prop : isProp (RF-iso (A , F) (A , G) (idEquiv A))
        RF-iso-prop =
          isPropΣ (RP-iso-prop (A , π₀ P) (A , π₀ Q) (idEquiv A)) (λ _ →
          isPropΣ (λ p q → A-set₀ _ _ p q ) λ _ →
          isPropΣ (isPropΠ λ _ → isPropΠ λ _ → A-set₀ _ _) λ _ →
          isPropΠ λ _ → A-set₀ _ _)

        h : (eq : F ≡ G) → (fib : fiber f eq) → (g eq , ret eq) ≡ fib
        h eq (i , p) =
          ΣProp≡ (λ x → isOfHLevelSuc 2 str-set F G (f x) eq) (RF-iso-prop (g eq) i)


frame-iso : (M N : Σ (Type ℓ₀) (FrameStr ℓ₁ ℓ₂)) → π₀ M ≃ π₀ N → Type (ℓ₀ ⊔ ℓ₁ ⊔ suc ℓ₂)
frame-iso {ℓ₁ = ℓ₁} {ℓ₂ = ℓ₂} =
  add-to-iso RF-iso λ A RF → [ FrameAx RF ]

frame-iso-prop : (M N : Frame ℓ₀ ℓ₁ ℓ₂) → (i : π₀ M ≃ π₀ N) → isProp (frame-iso M N i)
frame-iso-prop F G i =
  isPropΣ (RP-iso-prop RP RQ i) λ _ →
  isPropΣ (carrier-is-set (pos G) _ _) λ _ →
  isPropΣ (isPropΠ λ x → isPropΠ λ y → carrier-is-set (pos G) _ _) λ _ →
                isPropΠ λ _ → carrier-is-set (pos G) _ _
  where
    RP = ∣ F ∣F , π₀ (strₚ (pos F))
    RQ = ∣ G ∣F , π₀ (strₚ (pos G))

frame-iso-Ω : (M N : Frame ℓ₀ ℓ₁ ℓ₂) → π₀ M ≃ π₀ N → hProp (ℓ₀ ⊔ ℓ₁ ⊔ suc ℓ₂)
frame-iso-Ω M N i = frame-iso M N i , frame-iso-prop M N i

FrameAx-props : (A : Type ℓ₀) (str : RawFrameStr ℓ₁ ℓ₂ A)
                   → isProp [ FrameAx str ]
FrameAx-props A str = is-true-prop (FrameAx str)

frame-is-SNS : SNS {ℓ₀} (FrameStr ℓ₁ ℓ₂) frame-iso
frame-is-SNS {ℓ₁ = ℓ₁} {ℓ₂ = ℓ₂} =
  SNS-PathP→SNS-≡
    (FrameStr ℓ₁ ℓ₂)
    frame-iso
    (add-axioms-SNS _ FrameAx-props (SNS-≡→SNS-PathP RF-iso RF-is-SNS))

frame-is-SNS-PathP : SNS-PathP {ℓ₀} (FrameStr ℓ₁ ℓ₂) frame-iso
frame-is-SNS-PathP = SNS-≡→SNS-PathP frame-iso frame-is-SNS

frame-SIP : (F G : Frame ℓ₀ ℓ₁ ℓ₂) → (eqv : ∣ F ∣F ≃ ∣ G ∣F) → frame-iso F G eqv → F ≡ G
frame-SIP {ℓ₁ = ℓ₁} {ℓ₂ = ℓ₂} F G eqv i = NTS (eqv , i)
  where
    NTS : F ≃[ frame-iso ] G → F ≡ G
    NTS = equivFun (SIP frame-is-SNS-PathP F G)

frame-iso→frame-iso' : (F G : Frame ℓ₀ ℓ₁ ℓ₂) (eqv : ∣ F ∣F ≃ ∣ G ∣F)
                     → poset-iso (pos F) (pos G) eqv → frame-iso F G eqv
frame-iso→frame-iso' {ℓ₂ = ℓ₂} F G eqv i = i , (⊤-eq , ⊓-eq , ⋁-eq)
  where
    f = equivFun eqv
    g = equivFun (invEquiv eqv)

    ret : (y : ∣ G ∣F) → f (g y) ≡ y
    ret y = retEq eqv y

    sec : (x : ∣ F ∣F) → g (f x) ≡ x
    sec = secEq eqv

    open PosetReasoning (pos G)
    open PosetReasoning (pos F) using () renaming (_⊑⟨_⟩_ to _⊑₁⟨_⟩_; _■ to _■₁)

    bar : (x y : ∣ G ∣F) → [ x ⊑[ pos G ] y ⇔ (g x) ⊑[ pos F ] (g y) ]
    bar x y = β , α
      where
        φ : [ (g x) ⊑[ pos F ] (g y) ⇔ (f (g x)) ⊑[ pos G ] (f (g y)) ]
        φ = i (g x) (g y)

        α : [ (g x) ⊑[ pos F ] (g y) ⇒ x ⊑[ pos G ] y ]
        α p = x       ⊑⟨ ≡⇒⊑ (pos G) (sym (ret x))  ⟩
              f (g x) ⊑⟨ π₀ φ p                     ⟩
              f (g y) ⊑⟨ ≡⇒⊑ (pos G) (ret y)        ⟩
              y       ■

        β : [ x ⊑[ pos G ] y ⇒ (g x) ⊑[ pos F ] (g y) ]
        β p = π₁ φ eq
          where
            eq : [ f (g x) ⊑[ pos G ] f (g y) ]
            eq = f (g x)  ⊑⟨ ≡⇒⊑ (pos G) (ret x)       ⟩
                 x        ⊑⟨ p                         ⟩
                 y        ⊑⟨ ≡⇒⊑ (pos G) (sym (ret y)) ⟩
                 f (g y)  ■


    ⊤-eq : f ⊤[ F ] ≡ ⊤[ G ]
    ⊤-eq = top-unique G (f ⊤[ F ]) NTS
      where
        NTS : (o : ∣ G ∣F) → [ o ⊑[ pos G ] (f ⊤[ F ]) ]
        NTS o = π₁ (bar o (f ⊤[ F ])) eq
          where
            eq : [ g o ⊑[ pos F ] g (f ⊤[ F ]) ]
            eq = g o          ⊑₁⟨ ⊤[ F ]-top (g o) ⟩
                 ⊤[ F ]       ⊑₁⟨ ≡⇒⊑ (pos F) (sym (sec ⊤[ F ])) ⟩
                 g (f ⊤[ F ]) ■₁

    ⊓-eq : (x y : ∣ F ∣F) →  f (x ⊓[ F ] y) ≡ (f x) ⊓[ G ] (f y)
    ⊓-eq x y = ⊓-unique G (f x) (f y) (f (x ⊓[ F ] y)) I II III
      where
        I : [ f (x ⊓[ F ] y) ⊑[ pos G ] f x ]
        I = π₁ (bar (f (x ⊓[ F ] y)) (f x)) NTS
          where
            NTS : [ g (f (x ⊓[ F ] y)) ⊑[ pos F ] g (f x) ]
            NTS = g (f (x ⊓[ F ] y)) ⊑₁⟨ ≡⇒⊑ (pos F) (sec _)       ⟩
                  x ⊓[ F ] y         ⊑₁⟨ ⊓[ F ]-lower₀ x y         ⟩
                  x                  ⊑₁⟨ ≡⇒⊑ (pos F) (sym (sec x)) ⟩
                  g (f x)            ■₁

        II : [ f (x ⊓[ F ] y) ⊑[ pos G ] f y ]
        II = π₁ (bar (f (x ⊓[ F ] y)) (f y)) NTS
          where
            NTS : [ g (f (x ⊓[ F ] y)) ⊑[ pos F ] g (f y) ]
            NTS = g (f (x ⊓[ F ] y)) ⊑₁⟨ ≡⇒⊑ (pos F) (sec _)       ⟩
                  x ⊓[ F ] y         ⊑₁⟨ ⊓[ F ]-lower₁ x y         ⟩
                  y                  ⊑₁⟨ ≡⇒⊑ (pos F) (sym (sec _)) ⟩
                  g (f y)            ■₁

        III : (z′ : ∣ G ∣F)
            → [ z′ ⊑[ pos G ] (f x) ]
            → [ z′ ⊑[ pos G ] (f y) ]
            → [ z′ ⊑[ pos G ] f (x ⊓[ F ] y) ]
        III z′ p q = π₁ (bar z′ (f (x ⊓[ F ] y))) NTS
          where
            gz′⊑x : [ g z′ ⊑[ pos F ] x ]
            gz′⊑x =
              π₁ (i (g z′) x) (f (g z′) ⊑⟨ ≡⇒⊑ (pos G) (ret z′) ⟩ z′ ⊑⟨ p ⟩ f x ■)

            gz′⊑y : [ g z′ ⊑[ pos F ] y ]
            gz′⊑y =
              π₁ (i (g z′) y) (f (g z′) ⊑⟨ ≡⇒⊑ (pos G) (ret z′) ⟩ z′ ⊑⟨ q ⟩ f y ■)

            NTS : [ g z′ ⊑[ pos F ] g (f (x ⊓[ F ] y)) ]
            NTS = g z′               ⊑₁⟨ ⊓[ F ]-greatest x y (g z′) gz′⊑x gz′⊑y  ⟩
                  x ⊓[ F ] y         ⊑₁⟨ ≡⇒⊑ (pos F) (sym (sec _))               ⟩
                  g (f (x ⊓[ F ] y)) ■₁

    ⋁-eq : (U : Fam ℓ₂ ∣ F ∣F) →  f (⋁[ F ] U) ≡ ⋁[ G ] (index U , λ i → f (U $ i))
    ⋁-eq U = ⋁-unique G (f ⟨$⟩ U) (f (⋁[ F ] U)) NTS₀ NTS₁
      where
        NTS₀ : (o : ∣ G ∣F) → o ε (f ⟨$⟩ U) → [ o ⊑[ pos G ] (f (⋁[ F ] U)) ]
        NTS₀ o (i , p) =
          π₁
            (bar o (f (⋁[ F ] U)))
            (g o              ⊑₁⟨ ⋁[ F ]-upper U (g o) I ⟩
             ⋁[ F ] U         ⊑₁⟨ ≡⇒⊑ (pos F) (sym (sec _)) ⟩
             g (f (⋁[ F ] U)) ■₁)
          where
            I : g o ε U
            I = i , (U $ i ≡⟨ sym (sec _) ⟩ g (f (U $ i)) ≡⟨ cong g p ⟩ g o ∎)

        NTS₁ : (z′ : ∣ G ∣F)
             → ((o : ∣ G ∣F) → o ε (f ⟨$⟩ U) → [ o ⊑[ pos G ] z′ ])
             → [ f (⋁[ F ] U) ⊑[ pos G ] z′ ]
        NTS₁ z′ p =
          π₁
            (bar (f (⋁[ F ] U)) z′)
            (g (f (⋁[ F ] U)) ⊑₁⟨ ≡⇒⊑ (pos F) (sec _)       ⟩
             ⋁[ F ] U         ⊑₁⟨ ⋁[ F ]-least U (g z′) NTS ⟩
             g z′             ■₁)
          where
            NTS : (o : ∣ F ∣F) → o ε U → [ o ⊑[ pos F ] (g z′) ]
            NTS o (j , εU) =
              π₁
                (i o (g z′))
                (f o ⊑⟨ p (f o) foεf⟨$⟩U ⟩ z′ ⊑⟨ ≡⇒⊑ (pos G) (sym (ret _)) ⟩ f (g z′) ■)
              where
                foεf⟨$⟩U : f o ε (f ⟨$⟩ U)
                foεf⟨$⟩U = j , (f ⟨$⟩ U $ j ≡⟨ refl ⟩ f (U $ j) ≡⟨ cong f εU ⟩ f o ∎)

_≃f_ : Frame ℓ₀ ℓ₁ ℓ₂ → Frame ℓ₀ ℓ₁ ℓ₂ → Type (ℓ₀ ⊔ ℓ₁)
F ≃f G = Σ[ i ∈ (∣ F ∣F ≃ ∣ G ∣F) ] poset-iso (pos F) (pos G) i

-- This is the weak form of univalence.
≃f→≡ : (F G : Frame ℓ₀ ℓ₁ ℓ₂) → F ≃f G → F ≡ G
≃f→≡ F G (eqv , iso-f) = frame-SIP F G eqv (frame-iso→frame-iso' F G eqv iso-f)

-- -}
-- -}
-- -}
