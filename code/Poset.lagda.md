```
{-# OPTIONS --without-K --cubical --safe #-}

module Poset where

open import Basis
open import Powerset
import AlgebraicProperties
```

```
RawPosetStr : (ℓ₁ : Level) → Type ℓ → Type (ℓ ⊔ suc ℓ₁)
RawPosetStr {ℓ = ℓ} ℓ₁ A = (A → A → Ω ℓ₁) × IsSet A

SatisfiesPosetAxioms : (ℓ₁ : Level) (A : Type ℓ) → RawPosetStr ℓ₁ A → Ω (ℓ ⊔ ℓ₁)
SatisfiesPosetAxioms _ A (_⊑_ , A-set) = IsReflexive ∧ IsTransitive ∧ IsAntisym
  where
    open AlgebraicProperties A-set _⊑_

PosetStr : (ℓ₁ : Level) → Type ℓ → Type (ℓ ⊔ suc ℓ₁)
PosetStr ℓ₁ = add-to-structure (RawPosetStr ℓ₁) (λ A RP → SatisfiesPosetAxioms ℓ₁ A RP is-true)


Poset : (ℓ₀ ℓ₁ : Level) → Type (suc ℓ₀ ⊔ suc ℓ₁)
Poset ℓ₀ ℓ₁ = Σ (Type ℓ₀) (PosetStr ℓ₁)


∣_∣ₚ : Poset ℓ₀ ℓ₁ → Type ℓ₀
∣ X , _ ∣ₚ = X

strₚ : (P : Poset ℓ₀ ℓ₁) → PosetStr ℓ₁ ∣ P ∣ₚ
strₚ (_ , s) = s

```

```
rel : (P : Poset ℓ₀ ℓ₁) → ∣ P ∣ₚ → ∣ P ∣ₚ → Ω ℓ₁
rel (_ , (_⊑_ , _) , _) = _⊑_

syntax rel P x y = x ⊑[ P ] y
```

```
⊑[_]-refl : (P : Poset ℓ₀ ℓ₁) → (x : ∣ P ∣ₚ) → x ⊑[ P ] x is-true
⊑[_]-refl (_ , _ , (⊑-refl , _)) = ⊑-refl

⊑[_]-trans : (P : Poset ℓ₀ ℓ₁) (x y z : ∣ P ∣ₚ)
           → x ⊑[ P ] y is-true → y ⊑[ P ] z is-true → x ⊑[ P ] z is-true
⊑[_]-trans (_ , _ , (_ , ⊑-trans , _)) = ⊑-trans

⊑[_]-antisym : (P : Poset ℓ₀ ℓ₁) (x y : ∣ P ∣ₚ)
             → x ⊑[ P ] y is-true → y ⊑[ P ] x is-true → x ≡ y
⊑[_]-antisym (_ , _ , (_ , _ , ⊑-antisym)) = ⊑-antisym
```

```
module PosetReasoning (P : Poset ℓ₀ ℓ₁) where

  _⊑⟨_⟩_ : (x : ∣ P ∣ₚ) {y z : ∣ P ∣ₚ}
         → x ⊑[ P ] y is-true → y ⊑[ P ] z is-true → x ⊑[ P ] z is-true
  _ ⊑⟨ p ⟩ q = ⊑[ P ]-trans _ _ _ p q

  _■ : (x : ∣ P ∣ₚ) → x ⊑[ P ] x is-true
  _■ = ⊑[ P ]-refl

  infixr 0 _⊑⟨_⟩_
  infix  1 _■
```

```
≡⇒⊑ : (P : Poset ℓ₀ ℓ₁) → {x y : ∣ P ∣ₚ} → x ≡ y → rel P x y is-true
≡⇒⊑ P {x = x} p = subst (λ z → x ⊑[ P ] z is-true) p (⊑[ P ]-refl x)

IsMonotonic : (P : Poset ℓ₀ ℓ₁) (Q : Poset ℓ₂ ℓ₃) → (∣ P ∣ₚ → ∣ Q ∣ₚ) → Set (ℓ₀ ⊔ ℓ₁ ⊔ ℓ₃)
IsMonotonic P Q f =
  (x y : ∣ P ∣ₚ) → x ⊑[ P ] y is-true → (f x) ⊑[ Q ] (f y) is-true
```

## Monotonic functions

```
_─m→_ : Poset ℓ₀ ℓ₁ → Poset ℓ₀′ ℓ₁′ → Set (ℓ₀ ⊔ ℓ₁ ⊔ ℓ₀′ ⊔ ℓ₁′)
_─m→_ P Q = Σ (∣ P ∣ₚ → ∣ Q ∣ₚ) (IsMonotonic P Q)
```

Projection for the underlying function of a monotonic map.

```
_$ₘ_ = π₀
```

Monotonic function composition.

```
_∘m_ : {P Q R : Poset ℓ₀ ℓ₁} → (Q ─m→ R) → (P ─m→ Q) → (P ─m→ R)
(g , pg) ∘m (f , pf) = g ∘ f , λ x y p → pg (f x) (f y) (pf x y p)

𝟏m : (P : Poset ℓ₀ ℓ₁) → P ─m→ P
𝟏m P = id , (λ x y x⊑y → x⊑y)

↓[_]_ : (P : Poset ℓ₀ ℓ₁) → ∣ P ∣ₚ → Set (ℓ₀ ⊔ ℓ₁)
↓[ P ] a = Σ ∣ P ∣ₚ (λ b → b ⊑[ P ] a is-true)

IsDownwardClosed : (P : Poset ℓ₀ ℓ₁) → (𝒫 ∣ P ∣ₚ) → Ω (ℓ₀ ⊔ ℓ₁)
IsDownwardClosed P@(X , _) D =
  ((x y : X) → D x is-true → y ⊑[ P ] x is-true → D y is-true) , prop
  where
    prop : IsProp ((x y : X) → D x is-true → y ⊑[ P ] x is-true → D y is-true)
    prop = ∏-prop λ _ → ∏-prop λ x → ∏-prop λ _ → ∏-prop λ _ → is-true-prop (D x)

DownwardClosedSubset : (P : Poset ℓ₀ ℓ₁) → Set (suc ℓ₀ ⊔ ℓ₁)
DownwardClosedSubset P = Σ (𝒫 ∣ P ∣ₚ) (λ S → IsDownwardClosed P S is-true)

DownwardClosedSubset-set : (P : Poset ℓ₀ ℓ₁) → IsSet (DownwardClosedSubset P)
DownwardClosedSubset-set P =
  Σ-set (𝒫-set ∣ P ∣ₚ) λ x → prop⇒set (is-true-prop (IsDownwardClosed P x))
```

```
RPS-prop : IsSet (RawPosetStr ℓ₁ A)
RPS-prop = isOfHLevelΣ 2 (∏-set (λ x → ∏-set λ y → isSetHProp)) λ _ → prop⇒set isPropIsSet

RP-iso : (M N : Σ (Type ℓ₀) (RawPosetStr ℓ₁)) → π₀ M ≃ π₀ N → Type (ℓ₀ ⊔ ℓ₁)
RP-iso (A , (_⊑₀_ , _)) (B , (_⊑₁_ , _)) eq =
  (x y : A) → (x ⊑₀ y ⇔ f x ⊑₁ f y) is-true
  where
    f = equivFun eq

RP-iso-prop : (M N : Σ (Type ℓ₀) (RawPosetStr ℓ₁)) → (i : π₀ M ≃ π₀ N) → IsProp (RP-iso M N i)
RP-iso-prop (A , (_⊑₀_ , _)) (B , (_⊑₁_ , _)) i =
  ∏-prop λ x → ∏-prop λ y → is-true-prop (x ⊑₀ y ⇔ f x ⊑₁ f y)
  where
    f = equivFun i

××=× : (A B : Type ℓ) → (A × B) ≡ A ×× B
××=× A B = isoToPath {A = A × B} {B = A ×× B} (iso f g sec ret)
  where
    f : A × B → A ×× B
    f = λ { (x , y ) → (x , y) }

    g : A ×× B → A × B
    g = λ { (x , y ) → (x , y) }

    sec : section f g
    sec (x , y) = refl

    ret : retract f g
    ret (x , y) = refl

raw-poset-is-SNS : SNS {ℓ = ℓ} (RawPosetStr ℓ₁) RP-iso
raw-poset-is-SNS {X = X} P@(_⊑₀_ , A-set) Q@(_⊑₁_ , B-set) = invEquiv (f , f-equiv)
  where
    f : RP-iso (X , (_⊑₀_ , A-set)) (X , (_⊑₁_ , B-set)) (idEquiv X)
      → (_⊑₀_ , A-set) ≡ (_⊑₁_ , B-set)
    f i = ΣProp≡ (λ _ → ∏-prop λ _ → ∏-prop λ _ → IsProp-prop) (fn-ext _⊑₀_ _⊑₁_ (λ x → fn-ext (_⊑₀_ x) (_⊑₁_ x) (λ y → ⇔toPath (proj₁ (i x y)) (proj₂ (i x y)))))


    f-equiv : isEquiv f
    f-equiv = record { equiv-proof = λ eq → (g eq , right-inv eq) , h eq }
      where
        g : (eq : (_⊑₀_ , A-set) ≡ (_⊑₁_ , B-set))
          → (x y : X)
          → (x ⊑₀ y is-true → x ⊑₁ y is-true)
            ×× (x ⊑₁ y is-true → x ⊑₀ y is-true)
        g eq x y = (λ x⊑₀y → subst (λ { (_⊑⋆_ , _) → x ⊑⋆ y is-true }) eq x⊑₀y)
                 , λ x⊑₁y → subst (λ { (_⊑⋆_ , _) → (x ⊑⋆ y) is-true }) (sym eq) x⊑₁y

        rel-set : IsSet ((X → X → Ω ℓ) × IsSet X)
        rel-set = Σ-set (∏-set (λ _ → ∏-set λ _ → isSetHProp)) λ _ → prop⇒set isPropIsSet

        something-prop : IsProp ((x y : X) → ((x ⊑₀ y) is-true
                       → (x ⊑₁ y) is-true) ×× ((x ⊑₁ y) is-true → (x ⊑₀ y) is-true))
        something-prop =
          ∏-prop (λ x → ∏-prop λ y →
            subst IsProp (××=× (x ⊑₀ y is-true → x ⊑₁ y is-true)
                               (x ⊑₁ y is-true → x ⊑₀ y is-true))
                           (isOfHLevelΣ 1 (∏-prop (λ z → is-true-prop (x ⊑₁ y))) λ p → ∏-prop (λ q → is-true-prop (x ⊑₀ y))))

        right-inv : (eq : (_⊑₀_ , A-set) ≡ (_⊑₁_ , B-set)) → f (g eq) ≡ eq
        right-inv eq = rel-set (_⊑₀_ , A-set) (_⊑₁_ , B-set) (f (g eq)) eq

        h : (eq : (_⊑₀_ , A-set) ≡ (_⊑₁_ , B-set)) → (fib : fiber f eq) → (g eq , right-inv eq) ≡ fib
        h eq (i , snd) =
          ΣProp≡ (λ x → hLevelSuc 2 ((X → X → Ω _) × IsSet X) rel-set P Q (f x) eq)
                 (something-prop (g eq) i)

raw-poset-is-SNS' : SNS' {ℓ = ℓ} (RawPosetStr ℓ₁) RP-iso
raw-poset-is-SNS' {ℓ₁ = ℓ₁} = SNS→SNS' (RawPosetStr ℓ₁) RP-iso raw-poset-is-SNS

poset-iso : (P Q : Poset ℓ₀ ℓ₁) → ∣ P ∣ₚ ≃ ∣ Q ∣ₚ → Type (ℓ₀ ⊔ ℓ₁)
poset-iso {ℓ₁ = ℓ₁} =
  add-to-iso (RawPosetStr ℓ₁) RP-iso λ A str → SatisfiesPosetAxioms ℓ₁ A str is-true

poset-axioms-props : (A : Type ℓ₀) (str : RawPosetStr ℓ₁ A) → IsProp (SatisfiesPosetAxioms ℓ₁ A str is-true)
poset-axioms-props {ℓ₁ = ℓ₁} A str = is-true-prop (SatisfiesPosetAxioms ℓ₁ A str) 

poset-is-SNS' : SNS' {ℓ = ℓ} (PosetStr ℓ₁) poset-iso
poset-is-SNS' {ℓ₁ = ℓ₁} =
  add-axioms-SNS' (RawPosetStr ℓ₁) RP-iso (λ A str → SatisfiesPosetAxioms ℓ₁ A str is-true) poset-axioms-props raw-poset-is-SNS'

poset-is-SNS''' : SNS''' {ℓ = ℓ} (PosetStr ℓ₁) poset-iso
poset-is-SNS''' {ℓ₁ = ℓ₁} = SNS''→SNS''' (PosetStr ℓ₁) poset-iso poset-is-SNS'

poset-SIP : (A : Type ℓ₀) (B : Type ℓ₀) (eqv : A ≃ B) (P : PosetStr ℓ₁ A) (Q : PosetStr ℓ₁ B)
          → poset-iso (A , P) (B , Q) eqv
          → (A , P) ≡ (B , Q)
poset-SIP {ℓ₁ = ℓ₁} A B eqv P Q i = foo (eqv , i)
  where
    foo : (A , P) ≃[ poset-iso ] (B , Q) → (A , P) ≡ (B , Q)
    foo = equivFun (SIP (PosetStr ℓ₁) poset-iso poset-is-SNS''' (A , P) (B , Q))

_≃ₚ_ : Poset ℓ₀ ℓ₁ → Poset ℓ₀ ℓ₁ → Type (ℓ₀ ⊔ ℓ₁)
_≃ₚ_ P Q = Σ[ i ∈ (∣ P ∣ₚ ≃ ∣ Q ∣ₚ) ] poset-iso P Q i

pos-iso-to-eq : (P Q : Poset ℓ₀ ℓ₁) → P ≃ₚ Q → P ≡ Q
pos-iso-to-eq (A , A-pos) (B , B-pos) (eqv , i) = poset-SIP A B eqv A-pos B-pos i

-- --}
-- --}
-- --}
```
