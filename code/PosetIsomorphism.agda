module PosetIsomorphism where

open import Common
open import Homotopy
open import Poset
open import AlgebraicProperties

variable
  ℓ ℓ′ ℓ₀ ℓ₁ ℓ₂ : Level

IsPartial : {X : Set ℓ} → (X → X → Set ℓ) → Set ℓ
IsPartial _⊑_ = IsReflexive _⊑_ × IsTransitive _⊑_ × IsAntisym _⊑_

PosetStr′ : Set ℓ → Set (suc ℓ)
PosetStr′ {ℓ} X =
  IsSet X × Σ[ _⊑_ ∈ (X → X → Set ℓ) ] (((x y : X) → IsProp (x ⊑ y)) × IsPartial _⊑_)

Poset′ : (ℓ : Level) → Set (suc ℓ)
Poset′ ℓ = Σ (Set ℓ) PosetStr′

∣_∣ : (P : Poset′ ℓ) → Set ℓ
∣ X , _ ∣ = X

rel : (P : Poset′ ℓ)→ ∣ P ∣ → ∣ P ∣ → Set ℓ
rel (_ , _ , _⊑_ , _) = _⊑_

setlike : (P : Poset′ ℓ) → IsSet ∣ P ∣
setlike (_ , ∣P∣-set , _ , _) = ∣P∣-set

⊑-prop : (P : Poset′ ℓ) → (x y : ∣ P ∣) → IsProp (rel P x y)
⊑-prop (_ , _ , _ , ⊑-prop , _) = ⊑-prop

IsMonotonic : (P₀ P₁ : Poset′ ℓ) → (∣ P₀ ∣ → ∣ P₁ ∣) → Set ℓ
IsMonotonic P₀ P₁ f = (x y : ∣ P₀ ∣) → (rel P₀ x y) → rel P₁ (f x) (f y)

id-monotonic : (P : Poset′ ℓ) → IsMonotonic P P (id {A = ∣ P ∣})
id-monotonic P x y x⊑y = x⊑y

IsIsomorphism : (P₀ P₁ : Poset′ ℓ) → (∣ P₀ ∣ → ∣ P₁ ∣) → Set ℓ
IsIsomorphism P₀ P₁ f = (IsMonotonic P₀ P₁ f) × Σ (∣ P₁ ∣ → ∣ P₀ ∣) λ g →
  IsMonotonic P₁ P₀ g × ((g ∘ f) ~ id × ((f ∘ g) ~ id))

-- The type of poset isomorphisms.
_≅ₚ_ : Poset′ ℓ → Poset′ ℓ → Set ℓ
P₀ ≅ₚ P₁ = Σ (∣ P₀ ∣ → ∣ P₁ ∣) (λ f → IsIsomorphism P₀ P₁ f)

-- Expresses that a given f : ∣P₀∣ → ∣P₁∣ is an equivalence that is monotonic.
IsMonoEquiv : (P₀ P₁ : Poset′ ℓ) → (∣ P₀ ∣ → ∣ P₁ ∣) → Set ℓ
IsMonoEquiv P₀ P₁ f = isequiv f × IsMonotonic P₀ P₁ f

-- The type of *monotonic equivalences*.
_≃ₚ_ : Poset′ ℓ → Poset′ ℓ → Set ℓ
P₀ ≃ₚ P₁ = Σ (∣ P₀ ∣ → ∣ P₁ ∣) λ f → IsMonoEquiv P₀ P₁ f

PosetStr′≃PosetStr : (X : Set ℓ) → PosetStr X ≃ PosetStr′ X
PosetStr′≃PosetStr X = to-Σ , λ P → (from-Σ P , cancellation P) , foo P
  where
    to-Σ : PosetStr X → PosetStr′ X
    to-Σ (posetstr _⊑_ ⊑-prop A-set rlx trans antisym) =
      A-set , (_⊑_ , ⊑-prop , rlx , (trans , antisym))
    from-Σ : PosetStr′ X → PosetStr X
    from-Σ (X-set , _⊑_ , ⊑-prop , rfl , trans , antisym) =
      posetstr _⊑_ ⊑-prop X-set rfl trans antisym
    cancellation : (P : PosetStr′ X) → to-Σ (from-Σ P) ≡ P
    cancellation _ = refl
    foo : (P : PosetStr′ X) (x : fiber to-Σ P) → (from-Σ P , refl) ≡ x
    foo  _ (_ , refl) = refl

PosetStr′≡PosetStr : (X : Set ℓ) → PosetStr X ≡ PosetStr′ X
PosetStr′≡PosetStr = equivtoid ∘ PosetStr′≃PosetStr

⌜_⌝ : {P₀ P₁ : Poset′ ℓ} → P₀ ≡ P₁ → ∣ P₀ ∣ → ∣ P₁ ∣
⌜ p ⌝ = transport ∣_∣ p

eq⇒iso : {P₀ P₁ : Poset′ ℓ} → P₀ ≡ P₁ → P₀ ≅ₚ P₁
eq⇒iso refl = id , ((λ _ _ p → p) , (id , ((λ _ _ p → p) , (λ _ → refl) , λ _ → refl)))

iso⇒equiv : {P₀ P₁ : Poset′ ℓ}
          → (f : ∣ P₀ ∣ → ∣ P₁ ∣) → IsIsomorphism P₀ P₁ f → IsMonoEquiv P₀ P₁ f
iso⇒equiv {P₁ = P₁} f (mono , (g , (g-mono , li , ri))) = f-equiv , mono
  where
    bar : (y : ∣ P₁ ∣) (f : fiber f y) → (g y , ri y) ≡ f
    bar y (x , refl) = to-subtype-≡ (λ x′ → setlike P₁ (f x′) (f x)) (li x)
    f-equiv : isequiv f
    f-equiv x = (g x , ri x) , bar x

-- Being monotonic is a propositional type.
Mono-prop : (P₀ P₁ : Poset′ ℓ) → (f : ∣ P₀ ∣ → ∣ P₁ ∣) → IsProp (IsMonotonic P₀ P₁ f)
Mono-prop P₀ P₁ f =
  ∏-resp-prop λ x → ∏-resp-prop λ y → ∏-resp-prop λ p → ⊑-prop P₁ (f x) (f y)

MonoEquiv-prop : {P₀ P₁ : Poset′ ℓ} → (f : ∣ P₀ ∣ → ∣ P₁ ∣) → IsProp (IsMonoEquiv P₀ P₁ f)
MonoEquiv-prop {P₀ = P₀} {P₁} f =
  ×-resp-prop (isequiv f) (IsMonotonic P₀ P₁ f) (equiv-prop f) (Mono-prop P₀ P₁ f)
