module PosetIsomorphism where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl) renaming (cong to ap; trans to _·_; subst to transport)

open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Homotopy

open import Poset

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
