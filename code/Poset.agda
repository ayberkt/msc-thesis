module Poset where

open import Relation.Binary.PropositionalEquality using (_≡_; sym)
            renaming (cong to ap; subst to transport; trans to _·_)
open import Data.Product using (Σ; Σ-syntax; proj₁; proj₂; _,_; _×_)
open import Function     using (id; _∘_)
open import Level
open import Homotopy

_$_ : {ℓ ℓ′ : Level} {A : Set ℓ} {B : A → Set ℓ′} → Σ A B → A
_$_ = proj₁

record PosetStr {ℓ : Level} (A : Set ℓ) : Set (suc ℓ) where
  constructor posetstr

  -- Data.
  field
    _⊑_  : A → A → Set ℓ

  -- Laws.
  field
    refl  : (x     : A) → x ⊑ x
    trans : (x y z : A) → x ⊑ y → y ⊑ z → x ⊑ z
    sym⁻¹ : (x y   : A) → x ⊑ y → y ⊑ x → x ≡ y

  -- Homotopy structure.
  field
    ⊑-set : (x y : A) → isprop (x ⊑ y)

Poset : {ℓ : Level} → Set (suc ℓ)
Poset {ℓ} = Σ[ A ∈ Set ℓ ] (PosetStr A)

-- Monotonic functions.
_─m→_ : {ℓ : Level} {A B : Set ℓ} → PosetStr A → PosetStr B → Set ℓ
_─m→_ {_} {A} {B} P₁ P₂ =
  let
     open PosetStr P₁ using () renaming (_⊑_ to _⊑₁_)
     open PosetStr P₂ using () renaming (_⊑_ to _⊑₂_)
   in
     Σ[ f ∈ (A → B) ] ((x y : A) → x ⊑₁ y → (f x) ⊑₂ (f y))

-- Monotonic function composition.
_∘m_ : {A B C : Set} {P₁ : PosetStr A} {P₂ : PosetStr B} {P₃ : PosetStr C}
      → (P₂ ─m→ P₃)
      → (P₁ ─m→ P₂)
      → (P₁ ─m→ P₃)
(g , pg) ∘m (f , pf) = g ∘ f , λ x y p → pg (f x) (f y) (pf x y p)

𝟏m : {A : Set} → (P : PosetStr A) → P ─m→ P
𝟏m {A} P = id , (λ x y → id)

_≃m≃_ : {A B : Set} → PosetStr A → PosetStr B → Set
_≃m≃_ {A} {B} P₁ P₂ =
  Σ[ m₁ ∈ (P₁ ─m→ P₂) ]
  Σ[ m₂ ∈ (P₂ ─m→ P₁) ] ((proj₁ m₁ ∘ proj₁ m₂) ~ id) × ((proj₁ m₂ ∘ proj₁ m₁) ~ id)

eqp : {A B : Set} (P₀ : PosetStr A) (P₁ : PosetStr B)
    → P₀ ≃m≃ P₁
    → A ≡ B
eqp {A} {B} P₀ P₁ (m₀ , m₁ , p , q) =
  proj₁ (proj₁ (ua {_} {A} {B})) (proj₁ m₀ , (proj₁ m₁ , q) , (proj₁ m₁) , p)

posetext : {A : Set} (P₀ P₁ : PosetStr A)
         → PosetStr._⊑_ P₀ ≡ PosetStr._⊑_ P₁
         → P₀ ≡ P₁
posetext (posetstr _⊑₀_ refl₀ trans₀ sym⁻¹₀ ⊑₀-set) (posetstr _⊑₁_ refl₁ trans₁ sym⁻¹₁ ⊑₁-set) p rewrite p =
    ap (λ k → posetstr _ k _ _ _) foo · (ap _ bar · (ap _ baz · ap _ quux))
  where
    foo : refl₀ ≡ refl₁
    foo = funext refl₀ refl₁ (λ x → ⊑₁-set x x (refl₀ x) (refl₁ x))
    bar : trans₀ ≡ trans₁
    bar = {!!}
    baz : sym⁻¹₀ ≡ sym⁻¹₁
    baz = {!!}
    quux : ⊑₀-set ≡ ⊑₁-set
    quux = {!!}

eqp′ : {A B : Set} (P₀ : PosetStr A) (P₁ : PosetStr B)
     → (iso : P₀ ≃m≃ P₁)
     → transport PosetStr (eqp P₀ P₁ iso) P₀ ≡ P₁
eqp′ {A} {B} P₀ P₁ iso =
    posetext (transport PosetStr (eqp P₀ P₁ iso) P₀) P₁ φ
  where
    open PosetStr (transport PosetStr (eqp P₀ P₁ iso) P₀) using () renaming (_⊑_ to _⊑₀_)
    open PosetStr P₁ using () renaming (_⊑_ to _⊑₁_)
    AtoB = proj₁ (idtoeqv {_} {A} {B}(eqp P₀ P₁ iso))
    BtoA = proj₁ (proj₁ (proj₂ (idtoeqv {_} {A} {B}(eqp P₀ P₁ iso))))
    m₁   = proj₁ iso
    m₂   = proj₁ (proj₂ iso)
    f₁ : B → B
    f₁ = transport (λ k → k → B) (eqp P₀ P₁ iso) (proj₁ m₁)
    br : (x : B) → f₁ x ≡ x
    br x = {!!}
    baz₀ : (x y : B) → x ⊑₀ y → x ⊑₁ y
    baz₀ x y p = {!!}
    baz₁ : (x y : B) → x ⊑₁ y → x ⊑₀ y
    baz₁ x y p = {!!}
    baz : (x y : B) → (x ⊑₀ y) ≃ (x ⊑₁ y)
    baz x y = (baz₀ x y) , (baz₁ x y , {!!}) , (baz₁ x y) , λ x₁ → {!!}
    bar : (x y : B) → x ⊑₀ y ≡ x ⊑₁ y
    bar x y = proj₁ (proj₁ (ua {_} {x ⊑₀ y} {x ⊑₁ y})) (baz x y)
    φ : _⊑₀_ ≡ _⊑₁_
    φ = funext _ _ (λ x → funext _ _ (λ y → bar x y))

↓ : {ℓ : Level} (P : Poset {ℓ}) → proj₁ P → Set ℓ
↓ P x = Σ[ y ∈ (proj₁ P) ] (x ⊑ y)
  where
    open PosetStr (proj₂ P) using (_⊑_)
