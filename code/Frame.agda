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

record Frame (ℓ₀ ℓ₁ ℓ₂ : Level) : Set (suc (ℓ₀ ⊔ ℓ₁ ⊔ ℓ₂)) where
  constructor frame

  field
    P   : Poset ℓ₀ ℓ₁

  O   = ∣ P ∣ₚ
  _⊑_ = PosetStr._⊑_ (strₚ P)

  field
    𝟏   : O
    _⊓_ : O → O → O
    ⊔_  : Sub ℓ₂ O → O

  field

    -- Greatest lower bound.
    -- Consider merging the following three requirements and prove that equivalent to
    -- this. Thanks to univalence, one can alternate between the two styles if one happens
    -- to be more preferable than the other in certain cases.
    top         : (o     : O) → o ⊑ 𝟏 is-true
    ⊓-lower₀    : (o p   : O) → (o ⊓ p) ⊑ o is-true
    ⊓-lower₁    : (o p   : O) → (o ⊓ p) ⊑ p is-true
    ⊓-greatest  : (o p q : O) → q ⊑ o is-true → q ⊑ p is-true → q ⊑ (o ⊓ p) is-true

    -- Least upper bound.
    ⊔-upper : (ℱ : Sub ℓ₂ O) → (o : O) → o ε ℱ → o ⊑ (⊔ ℱ) is-true
    ⊔-least : (ℱ : Sub ℓ₂ O) → (p : O) → ((o : O) → o ε ℱ → o ⊑ p is-true) → (⊔ ℱ) ⊑ p is-true

    -- Binary meety distribute over arbitrary joins.
    dist : (o : O) (ℱ : Sub ℓ₂ O) → o ⊓ (⊔ ℱ) ≡ ⊔ (index ℱ , λ i → o ⊓ (ℱ € i))

-- Projection for the carrier set of a frame i.e., the carrier set of the underlying poset.
∣_∣F : Frame ℓ₀ ℓ₁ ℓ₂ → Set ℓ₀
∣ frame P _ _ _ _ _ _ _ _ _ _ ∣F = ∣ P ∣ₚ

-- The underlying frame of a poset.
pos : Frame ℓ₀ ℓ₁ ℓ₂ → Poset ℓ₀ ℓ₁
pos F = Frame.P F

top-unique : (F : Frame ℓ₀ ℓ₁ ℓ₂)
           → (z : ∣ F ∣F)
           → ((o : ∣ F ∣F) → o ⊑[ pos F ] z is-true)
           → z ≡ Frame.𝟏 F
top-unique F z z-top = ⊑-antisym z 𝟏 (top z) (z-top 𝟏)
  where
    open Frame    F              using (𝟏; top)
    open PosetStr (strₚ (pos F)) using (⊑-antisym)

record _─f→_ {ℓ ℓ′ ℓ₂ : Level} (F₀ F₁ : Frame ℓ ℓ′ ℓ₂) : Set (ℓ ⊔ ℓ′ ⊔ suc ℓ₂) where
  constructor frame-homo
  open Frame F₀ using () renaming (P to P₀; _⊓_ to _⊓₀_; ⊔_ to ⊔₀_; 𝟏 to 𝟏₀)
  open Frame F₁ using () renaming (P to P₁; _⊓_ to _⊓₁_; ⊔_ to ⊔₁_; 𝟏 to 𝟏₁)

  field
    m : P₀ ─m→ P₁

  field
     resp-id : m $ₘ 𝟏₀ ≡ 𝟏₁
     resp-⊓  : (x y : ∣ P₀ ∣ₚ) → m $ₘ (x ⊓₀ y) ≡ (m $ₘ x) ⊓₁ (m $ₘ y)
     resp-⊔  : (ℱ : Sub ℓ₂ ∣ P₀ ∣ₚ) → m $ₘ (⊔₀ ℱ) ≡ (⊔₁ (index ℱ , λ i → m $ₘ (ℱ € i)))

-- Convenient notation for frame homomorphism application.
_$f_ : {F₀ : Frame ℓ₀ ℓ₁ ℓ₂} {F₁ : Frame ℓ₀ ℓ₁ ℓ₂}
     → (F₀ ─f→ F₁) → ∣ Frame.P F₀ ∣ₚ → ∣ Frame.P F₁ ∣ₚ
(frame-homo m _ _ _) $f k = m $ₘ k

-- An element of the poset is like a finite observation whereas an element of the
-- frame of downward closed posets is like a general observation.

-- The set of downward-closed subsets of a poset forms a frame.
downward-subset-poset : (P : Poset ℓ₀ ℓ₁) → Poset (suc ℓ₀ ⊔ ℓ₁) ℓ₀
downward-subset-poset {ℓ₀ = ℓ₀} {ℓ₁} (A , P) =
  𝔻 , posetstr _<<_ (DownwardClosedSubset-set (A , P)) <<-refl <<-trans <<-antisym
  where
    open PosetStr P using (_⊑_; ⊑-refl; ⊑-trans; ⊑-antisym)

    𝔻 = DownwardClosedSubset (A , P)

    _<<_ : 𝔻 → 𝔻 → Ω ℓ₀
    _<<_ (S , _) (T , _) = S ⊆ T

    open AlgebraicProperties (DownwardClosedSubset-set (A , P)) _<<_
       renaming ( IsReflexive  to <<-IsReflexive
                ; IsTransitive to <<-IsTransitive
                ; IsAntisym    to <<-IsAntisym)

    <<-refl : <<-IsReflexive is-true
    <<-refl (U , U-down) x xεU = xεU

    <<-trans : <<-IsTransitive is-true
    <<-trans (S , _) (T , _) (U , _) S<<T T<<U x xεS = T<<U x (S<<T x xεS)

    <<-antisym : <<-IsAntisym is-true
    <<-antisym X Y S⊆T T⊆S =
      to-subtype-≡ X Y (is-true-prop ∘ IsDownwardClosed (A , P)) (⊆-antisym S⊆T T⊆S)

-- The set of downward-closed subsets of a poset forms a frame.
downward-subset-frame : (P : Poset ℓ₀ ℓ₁) → Frame (suc ℓ₀ ⊔ ℓ₁) ℓ₀ ℓ₀
downward-subset-frame {ℓ₀ = ℓ} {ℓ′} (X , P) =
  record
    { P           =  𝔻ₚ
    ; 𝟏           =  𝟏
    ; _⊓_         =  _⊓_
    ; ⊔_          =  ⊔_
    ; top         =  𝟏-top
    ; ⊓-lower₀    =  ⊓-lower₀
    ; ⊓-lower₁    =  ⊓-lower₁
    ; ⊓-greatest  =  ⊓-greatest
    ; ⊔-upper     =  ⊔-upper
    ; ⊔-least     =  ⊔-least
    ; dist        =  dist
    }
  where
    𝔻ₚ = downward-subset-poset (X , P)
    𝔻  = ∣ 𝔻ₚ ∣ₚ

    ∣_∣𝔻 : 𝔻 → 𝒫 X
    ∣ S , _ ∣𝔻 = S

    open PosetStr (strₚ 𝔻ₚ) using    ()
                            renaming ( _⊑_       to  _<<_
                                     ; ⊑-refl    to  <<-refl
                                     ; ⊑-antisym to  <<-antisym)
    open PosetStr P          using   (_⊑_)

    𝟏 = (λ _ → N₁ , N₁-prop) , λ _ _ _ _ → tt

    ∩-down : (S T : 𝒫 X)
           → IsDownwardClosed (X , P) S is-true
           → IsDownwardClosed (X , P) T is-true
           → IsDownwardClosed (X , P) (S ∩ T) is-true
    ∩-down S T S↓ T↓ x y x∈S∩T y⊑x = S↓ x y (π₀ x∈S∩T) y⊑x , T↓ x y (π₁ x∈S∩T) y⊑x

    _⊓_ : 𝔻 → 𝔻 → 𝔻
    (S , S-dc) ⊓ (T , T-dc) = (S ∩ T) , ∩-down S T S-dc T-dc

    𝟏-top : (D : 𝔻) → (D << 𝟏) is-true
    𝟏-top D _ _ = tt

    -- Given a family ℱ over 𝔻 and some x : X, `in-some-set ℱ x` holds iff there is some
    -- set S among ℱ such that x ∈ S.
    in-some-set-of : (ℱ : Sub ℓ 𝔻) → X → Set ℓ
    in-some-set-of ℱ x = Σ (index ℱ) (λ i → ∣ ℱ € i ∣𝔻 x is-true)

    ⊔_ : Sub ℓ 𝔻 → 𝔻
    ⊔ ℱ = (λ x → ∥ in-some-set-of ℱ x ∥ , ∥∥-prop _) , ⊔ℱ↓
      where
        ind : (x y : X) → y ⊑ x is-true → in-some-set-of ℱ x → ∥ in-some-set-of ℱ y ∥
        ind x y y⊑x (i , x∈ℱᵢ) = ∣ i , π₁ (ℱ € i) x y x∈ℱᵢ y⊑x ∣

        ⊔ℱ↓ : IsDownwardClosed (X , P) (λ x → ∥ in-some-set-of ℱ x ∥ , ∥∥-prop _) is-true
        ⊔ℱ↓ x y ∣p∣ y⊑x = ∥∥-rec (∥∥-prop _) (ind x y y⊑x) ∣p∣

    ⊔-upper : (ℱ : Sub ℓ 𝔻) (D : 𝔻) → D ε ℱ → D << (⊔ ℱ) is-true
    ⊔-upper ℱ D DεS@(i , p) x x∈D = ∣ i , subst (λ V → ∣ V ∣𝔻 x is-true) (sym p) x∈D ∣

    ⊔-least : (ℱ : Sub ℓ 𝔻) (z : 𝔻) → ((o : 𝔻) → o ε ℱ → (o << z) is-true) → (⊔ ℱ) << z is-true
    ⊔-least ℱ D φ x x∈⊔S = ∥∥-rec (π₁ (∣ D ∣𝔻 x)) ind x∈⊔S
      where
        ind : in-some-set-of ℱ x → ∣ D ∣𝔻 x is-true
        ind (i , x∈ℱᵢ) = φ (ℱ € i) (i , refl) x x∈ℱᵢ

    ⊓-lower₀ : (D E : 𝔻) → (D ⊓ E) << D is-true
    ⊓-lower₀ D E x (x∈D , _) = x∈D

    ⊓-lower₁ : (D E : 𝔻) → (D ⊓ E) << E is-true
    ⊓-lower₁ D E x (_ , x∈F) = x∈F

    ⊓-greatest : (D E F : 𝔻) → (F << D) is-true → (F << E) is-true → F << (D ⊓ E) is-true
    ⊓-greatest D E F F<<D F<<E x x∈F = (F<<D x x∈F) , (F<<E x x∈F)

    dist : (D : 𝔻) (ℱ : Sub ℓ 𝔻) → D ⊓ (⊔ ℱ) ≡ ⊔ (index ℱ , λ i → D ⊓ (ℱ € i))
    dist D ℱ = <<-antisym (D ⊓ (⊔ ℱ)) (⊔ (index ℱ , λ i → D ⊓ (ℱ € i))) down up
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
          ∥∥-rec (isOfHLevelΣ 1 (is-true-prop (∣ D ∣𝔻 x)) (λ _ → is-true-prop (∣ ⊔ ℱ ∣𝔻 x))) φ x∈ℬ
          where
            φ : in-some-set-of (index ℱ , λ j → D ⊓ (ℱ € j)) x
              → (∣ D ∣𝔻 x is-true) × ∣ ⊔ ℱ ∣𝔻 x is-true
            φ (i , x∈D , x∈ℱᵢ) = x∈D , ∣ i , x∈ℱᵢ ∣

-- Frames form an SNS.

RFS : Type ℓ → Type (suc ℓ)
RFS {ℓ = ℓ} A = PS A × A × (A → A → A) × (Sub ℓ A → A)

RF-iso : (M N : Σ (Type ℓ) RFS) → π₀ M ≃ π₀ N → Type (suc ℓ)
RF-iso {ℓ = ℓ} (A , (RPS-A , _) , 𝟏₀ , _⊓₀_ , ⋃₀) (B , (RPS-B , _), 𝟏₁ , _⊓₁_ , ⋃₁) i =
    RP-iso (A , RPS-A) (B , RPS-B) i
  × f 𝟏₀ ≡ 𝟏₁
  × ((x y : A) → f (x ⊓₀ y) ≡ (f x) ⊓₁ (f y))
  × ((ℱ : Sub ℓ A) → f (⋃₀ ℱ) ≡ (⋃₁ (index ℱ , λ i → f (ℱ € i))))
  where
    f = equivFun i

pos-of : Σ (Type ℓ) RFS → Σ (Type ℓ) RPS
pos-of (A , ((RPS , _) , _)) = (A , RPS)

top-of : (F : Σ (Type ℓ) RFS) → π₀ F
top-of (_ , _ , 𝟏 , _) = 𝟏

RF-is-SNS : SNS {ℓ = ℓ} RFS RF-iso
RF-is-SNS {ℓ = ℓ} {X = A} F@(PS-A@(RPS₀@(_⊑₀_ , A-set₀) , ax₀) , 𝟏₀ , _⊓₀_ , ⋃₀) G@(PS-B@(RPS₁@(_⊑₁_ , A-set₁) , ax₁) , 𝟏₁ , _⊓₁_ , ⋃₁) =
  invEquiv (f , f-equiv)
  where
    f : RF-iso (A , F) (A , G) (idEquiv A) → _≡_ {A = RFS A} F G
    f (iₚ , eq-𝟏 , ⊓-xeq , ⋃-xeq) =
      PS-A , 𝟏₀ , _⊓₀_ , ⋃₀   ≡⟨ cong (λ - → (PS-A , - , _⊓₀_ , ⋃₀)) eq-𝟏               ⟩
      PS-A , 𝟏₁ , _⊓₀_ , ⋃₀   ≡⟨ cong {B = λ _ → RFS A} (λ - → PS-A , 𝟏₁ , - , ⋃₀) ⊓-eq ⟩
      PS-A , 𝟏₁ , _⊓₁_ , ⋃₀   ≡⟨ cong {B = λ _ → RFS A} (λ - → PS-A , 𝟏₁ , _⊓₁_ , -)  ⋃-eq ⟩
      PS-A , 𝟏₁ , _⊓₁_ , ⋃₁   ≡⟨ cong {B = λ _ → RFS A} (λ - → - , 𝟏₁ , _⊓₁_ , ⋃₁) eq ⟩
      PS-B , 𝟏₁ , _⊓₁_ , ⋃₁   ∎
      where
        eq : PS-A ≡ PS-B
        eq = ΣProp≡ (poset-axioms-props A)
             (ΣProp≡ (λ _ → isPropIsSet)
                     (fn-ext _⊑₀_ _⊑₁_ λ x →
                      fn-ext (_⊑₀_ x) (_⊑₁_ x) λ y → ⇔toPath (proj₁ (iₚ x y)) (proj₂ (iₚ x y))))

        ⊓-eq : _⊓₀_ ≡ _⊓₁_
        ⊓-eq = fn-ext _⊓₀_ _⊓₁_ (λ x → fn-ext (_⊓₀_ x) (_⊓₁_ x) λ y → ⊓-xeq x y)

        ⋃-eq : ⋃₀ ≡ ⋃₁
        ⋃-eq = fn-ext ⋃₀ ⋃₁ λ ℱ → ⋃-xeq ℱ

    f-equiv : isEquiv f
    f-equiv = record { equiv-proof = λ eq → (g eq , ret eq) , h eq }
      where
        g : (eq : F ≡ G) → RF-iso (A , F) (A , G) (idEquiv A)
        g eq = φ , ψ , ϑ , ξ
          where
            𝒻  = equivFun (idEquiv A)

            φ : RP-iso (A , _⊑₀_ , A-set₀) (A , _⊑₁_ , A-set₁) (idEquiv A)
            φ x y = (λ x⊑₁y → subst (λ { (((_⊑⋆_ , _) , _) , _) → (x ⊑⋆ y) is-true }) eq x⊑₁y)
                  , λ x⊑₁y → subst (λ { (((_⊑⋆_ , _) , _) , _) → (x ⊑⋆ y) is-true }) (sym eq) x⊑₁y

            ψ : equivFun (idEquiv A) 𝟏₀ ≡ 𝟏₁
            ψ = subst (λ { (_ , - , _ , _) → 𝒻 - ≡ 𝟏₁ }) (sym eq) refl

            ϑ : (x y : A) → 𝒻 (x ⊓₀ y) ≡ (𝒻 x) ⊓₁ (𝒻 y)
            ϑ x y = subst (λ { (_ , _ , _-_ , _) → 𝒻 (x - y) ≡ (𝒻 x) ⊓₁ (𝒻 y) }) (sym eq) refl

            ξ : (ℱ : Sub ℓ A) → 𝒻 (⋃₀ ℱ) ≡ ⋃₁ (index ℱ , λ i → 𝒻 (ℱ € i))
            ξ ℱ = subst (λ { (_ , _ , _ , -) → 𝒻 (- ℱ) ≡ (⋃₁ (index ℱ , λ i → 𝒻 (ℱ € i)))}) (sym eq) refl

        str-set : IsSet (RFS A)
        str-set = Σ-set (isOfHLevelΣ 2 RPS-prop (λ FS → prop⇒set (poset-axioms-props A FS))) λ _ → isOfHLevelΣ 2 A-set₀ λ _ →
                  isOfHLevelΣ 2 (∏-set (λ x → ∏-set λ y → A-set₀)) λ _ → ∏-set λ ℱ → A-set₀

        ret : (eq : F ≡ G) → f (g eq) ≡ eq
        ret eq = str-set F G (f (g eq)) eq

        RF-iso-prop : IsProp (RF-iso (A , F) (A , G) (idEquiv A))
        RF-iso-prop i₀ i₁ = isOfHLevelΣ 1 (RP-iso-prop (A , RPS₀) (A , RPS₁) (idEquiv A)) (λ _ → isOfHLevelΣ 1 (λ p q → A-set₀ _ _ p q ) λ _ →
                            isOfHLevelΣ 1 (∏-prop λ x → ∏-prop λ y → A-set₀ _ _) λ _ → ∏-prop λ _ → A-set₀ _ _) i₀ i₁

        h : (eq : F ≡ G) → (fib : fiber f eq) → (g eq , ret eq) ≡ fib
        h eq (i , p) = ΣProp≡ (λ x → hLevelSuc 2 (RFS A) str-set F G (f x) eq) (RF-iso-prop (g eq) i)

RF-is-SNS' : SNS' {ℓ = ℓ} RFS RF-iso
RF-is-SNS' = SNS→SNS' RFS RF-iso RF-is-SNS

frame-axioms : (A : Type ℓ) → RFS A → Type (suc ℓ)
frame-axioms {ℓ = ℓ} O (((_⊑_ , _) , _) , 𝟏 , _⊓_ , ⋃_) =
    ((o : O)       → o ⊑ 𝟏 is-true)
  × ((o p : O)     → (o ⊓ p) ⊑ o is-true)
  × ((o p : O)     → (o ⊓ p) ⊑ p is-true)
  × ((o p q : O)   → q ⊑ o is-true → q ⊑ p is-true → q ⊑ (o ⊓ p) is-true)
  × ((ℱ : Sub ℓ O) → (o : O) → o ε ℱ → o ⊑ (⋃ ℱ) is-true)
  × ((ℱ : Sub ℓ O) → (p : O) → ((o : O) → o ε ℱ → o ⊑ p is-true) → (⋃ ℱ) ⊑ p is-true)

FS : Type ℓ → Type (suc ℓ)
FS = add-to-structure RFS frame-axioms

frame-iso : (M N : Σ (Type ℓ) FS) → π₀ M ≃ π₀ N → Type (suc ℓ)
frame-iso = add-to-iso RFS RF-iso frame-axioms

frame-iso-prop : (M N : Σ (Type ℓ) FS) → (i : π₀ M ≃ π₀ N) → IsProp (frame-iso M N i)
frame-iso-prop M@(A , (P@(RP@(_⊑₀_ , A-set) , _) , _) , _) N@(B , (Q@(RQ@(_⊑₁_ , B-set) , _) , _) , _) i =
  isOfHLevelΣ 1 (RP-iso-prop (A , RP) (B , RQ) i) λ _ →
  isOfHLevelΣ 1 (B-set _ _) λ _ →
  isOfHLevelΣ 1 (∏-prop λ x → ∏-prop λ y → B-set _ _) λ _ →
                ∏-prop λ _ → B-set _ _

frame-iso-Ω : (M N : Σ (Type ℓ) FS) → π₀ M ≃ π₀ N → hProp (suc ℓ)
frame-iso-Ω M N i = (frame-iso M N i) , frame-iso-prop M N i

frame-axioms-props : (A : Type ℓ) (F : RFS A) → IsProp (frame-axioms A F)
frame-axioms-props A (((_⊑_ , _) , _) , 𝟏 , _⊓_ , ⋃_) =
  isOfHLevelΣ 1 (∏-prop λ x → is-true-prop (x ⊑ 𝟏)) λ _ →
  isOfHLevelΣ 1 (∏-prop λ o → ∏-prop λ p → is-true-prop ((o ⊓ p) ⊑ o)) λ _ →
  isOfHLevelΣ 1 (∏-prop (λ o → ∏-prop λ p → is-true-prop ((o ⊓ p) ⊑ p))) λ _ →
  isOfHLevelΣ 1 (∏-prop λ o → ∏-prop λ p → ∏-prop λ q → ∏-prop λ _ → ∏-prop λ _ → is-true-prop (q ⊑ (o ⊓ p))) λ _ →
  isOfHLevelΣ 1 (∏-prop λ ℱ → ∏-prop λ o → ∏-prop λ _ → is-true-prop (o ⊑ (⋃ ℱ))) λ _ →
  ∏-prop λ ℱ → ∏-prop λ z → ∏-prop λ _ → is-true-prop ((⋃ ℱ) ⊑ z)

frame-is-SNS' : SNS' {ℓ = ℓ} FS frame-iso
frame-is-SNS' = add-axioms-SNS' RFS RF-iso frame-axioms frame-axioms-props RF-is-SNS'

frame-is-SNS''' : SNS''' {ℓ = ℓ} FS frame-iso
frame-is-SNS''' = SNS''→SNS''' FS frame-iso frame-is-SNS'

frame-SIP : (A : Type ℓ) → (F G : FS A)
          → frame-iso (A , F) (A , G) (idEquiv A)
          → (A , F) ≡ (A , G)
frame-SIP A F G i = foo (idEquiv A , i)
  where
    foo : (A , F) ≃[ frame-iso ] (A , G) → (A , F) ≡ (A , G)
    foo = equivFun (SIP FS frame-iso frame-is-SNS''' (A , F) (A , G))

frame-iso' : (M N : Σ (Type ℓ) FS) → π₀ M ≃ π₀ N → hProp ℓ
frame-iso' (A , (P@((_⊑₀_ , _) , _) , _) , _) (B , (Q@((_⊑₁_ , _) , _) , _) , _) i =
  poset-iso (A , P) (B , Q) i , RP-iso-prop (A , π₀ P) (B , π₀ Q) i


frame-iso'→frame-iso : (M N : Σ (Type ℓ) FS)
                     → (i : π₀ M ≃ π₀ N)
                     → frame-iso M N i → frame-iso' M N i is-true
frame-iso'→frame-iso M N i (rp-iso , _)= rp-iso

frame-iso→frame-iso' : (A : Type ℓ)
                     → (F G : FS A)
                     → frame-iso' (A , F) (A , G) (idEquiv A) is-true
                     → frame-iso (A , F) (A , G) (idEquiv A)
frame-iso→frame-iso' A M@((P@((_⊑₀_ , _) , ax₀) , 𝟏₀ , _⊓₀_ , _) , fax₀) N@((Q@((_⊑₁_ , _) , ax₁) , 𝟏₁ , _⊓₁_ , _) , fax₁) rp-iso =
  rp-iso , (𝟏-eq , ⊓-eq , {!!})
  where
    ⊑₁-antisym = π₁ (π₁ ax₁)
    𝟏₀-top     = π₀ fax₀
    𝟏₁-top     = π₀ fax₁
    ⊓₀-lower₀   = π₀ (π₁ fax₀)
    ⊓₁-lower₀   = π₀ (π₁ fax₁)
    ⊓₁-lower₁   = π₀ (π₁ (π₁ fax₁))
    ⊓₀-lower₁   = π₀ (π₁ (π₁ fax₀))
    ⊓-greatest = π₀ (π₁ (π₁ (π₁ fax₀)))
    ⊓₀-greatest = π₀ (π₁ (π₁ (π₁ fax₀)))
    ⊓₁-greatest = π₀ (π₁ (π₁ (π₁ fax₁)))

    𝟏-eq : 𝟏₀ ≡ 𝟏₁
    𝟏-eq = ⊑₁-antisym 𝟏₀ 𝟏₁ (𝟏₁-top 𝟏₀) (proj₁ (rp-iso 𝟏₁ 𝟏₀) (𝟏₀-top 𝟏₁))

    ⊓-eq : (x y : A) → (x ⊓₀ y) ≡ (x ⊓₁ y)
    ⊓-eq x y = ⊑₁-antisym (x ⊓₀ y) (x ⊓₁ y) down up
      where
        x⊓₁y⊑₀x : (x ⊓₁ y) ⊑₀ x is-true
        x⊓₁y⊑₀x = proj₂ (rp-iso (x ⊓₁ y) x) (⊓₁-lower₀ x y)

        x⊓₁y⊑₀y : (x ⊓₁ y) ⊑₀ y is-true
        x⊓₁y⊑₀y = proj₂ (rp-iso (x ⊓₁ y) y) (⊓₁-lower₁ x y)

        x⊓₀y⊑₁y : (x ⊓₀ y) ⊑₁ y is-true
        x⊓₀y⊑₁y = proj₁ (rp-iso (x ⊓₀ y) y) (⊓₀-lower₁ x y)

        x⊓₀y⊑₁x : ((x ⊓₀ y) ⊑₁ x) is-true
        x⊓₀y⊑₁x = proj₁ (rp-iso (x ⊓₀ y) x) (⊓₀-lower₀ x y)

        down : (x ⊓₀ y) ⊑₁ (x ⊓₁ y) is-true
        down = ⊓₁-greatest x y (x ⊓₀ y) x⊓₀y⊑₁x x⊓₀y⊑₁y

        up : (x ⊓₁ y) ⊑₁ (x ⊓₀ y) is-true
        up = proj₁ (rp-iso (x ⊓₁ y) (x ⊓₀ y)) (⊓₀-greatest x y (x ⊓₁ y) x⊓₁y⊑₀x x⊓₁y⊑₀y)

-- -}
-- -}
-- -}
