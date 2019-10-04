{-# OPTIONS --without-K #-}

module PosetIsomorphism where

open import Common
open import Homotopy
open import SIP
open import SIPWithAxioms

variable
  ℓ ℓ′ ℓ₀ ℓ₁ ℓ₂ : Level

IsPartial : {X : Set ℓ} → IsSet X → (X → X → Ω ℓ′) → Ω (ℓ ⊔ ℓ′)
IsPartial {ℓ = ℓ} {ℓ′} {X = X} X-set _⊑_ = φ , φ-prop
  where
    φ : Set (ℓ ⊔ ℓ′)
    φ = IsReflexive holds × (IsTransitive holds × IsAntisym holds)
     where
       open import AlgebraicProperties X-set _⊑_
    φ-prop : IsProp φ
    φ-prop = ×-resp-prop _ _ (proj₂ IsReflexive )
             (×-resp-prop _ _ (proj₂ IsTransitive) (proj₂ IsAntisym))
      where
        open import AlgebraicProperties X-set _⊑_

PosetStr : Set → Set₁
PosetStr X = X → X → Ω zero

PosetAxioms′ : (X : Set) → IsSet X → (X → X → Ω zero) → Ω zero
PosetAxioms′ X X-set _⊑_ = IsPartial X-set _⊑_

PosetAxioms : (X : Set) → (X → X → Ω zero) → Ω zero
PosetAxioms X _⊑_ = (Σ[ X-set ∈ (IsSet X) ] PosetAxioms′ X X-set _⊑_ holds) , prop
  where
    prop : IsProp (Σ[ X-set ∈ (IsSet X) ] PosetAxioms′ X X-set _⊑_ holds)
    prop = Σ-resp-prop IsSet-prop λ X-set → proj₂ (PosetAxioms′ X X-set _⊑_)

sns-data : SNS PosetStr (suc zero)
sns-data = ι , ρ , θ
  where
    ι : (A B : Σ _ PosetStr) → ∣ A ∣ ≃ ∣ B ∣ → Set₁
    ι (X , d) (Y , e) (f , _) = d ≡ λ x x′ → e (f x) (f x′)

    ρ : (A : Σ _ PosetStr) → ι A A (id-≃ ∣ A ∣)
    ρ (X , d) = refl

    h : {X : Set} {d e : PosetStr X} → canonical-map ι ρ d e ~ id
    h refl = refl

    θ : {X : Set} (d e : PosetStr X) → isequiv (canonical-map ι ρ d e)
    θ d e = {!!}

Poset : Set₁
Poset = Σ[ X ∈ Set ] Σ[ _⊑_ ∈ (PosetStr X) ] (PosetAxioms X _⊑_ holds)

carrier : (P : Poset) → Set
carrier (X , _) = X

rel : (P : Poset)→ ∣ P ∣ → ∣ P ∣ → Ω zero
rel (_ , _⊑_ , _) = _⊑_

setlike : (P : Poset) → IsSet ∣ P ∣
setlike (_ , _ , X-set , _) = X-set

axioms : (P : Poset) → PosetAxioms ∣ P ∣ (rel P) holds
axioms (_ , _ , axioms) = axioms

_≅_ : Poset → Poset → Set₁
(X , _⊑₀_ , _) ≅ (Y , _⊑₁_ , _) =
  Σ[ f ∈ (X → Y) ] (isequiv f × (_⊑₀_ ≡ λ x x′ → (f x) ⊑₁ (f x′)))

eq≃iso : (P₀ P₁ : Poset) → (P₀ ≡ P₁) ≃ (P₀ ≅ P₁)
eq≃iso P₀ P₁ =
  characterisation-of-≡-with-axioms
    sns-data
    foo
    (λ X _⊑_ → proj₂ (PosetAxioms X _⊑_))
    (proj₁ P₀ , rel P₀ , axioms P₀) (proj₁ P₁ , (rel P₁ , axioms P₁))
  where
    foo : (X : Set) → PosetStr X → Set
    foo X _⊑_ = (PosetAxioms X _⊑_) holds

eq≡iso : (P₀ P₁ : Poset) → (P₀ ≡ P₁) ≡ (P₀ ≅ P₁)
eq≡iso P₀ P₁ = equivtoid (eq≃iso P₀ P₁)

-- -}
-- -}
-- -}
