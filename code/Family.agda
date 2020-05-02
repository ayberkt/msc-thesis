{-# OPTIONS --without-K --cubical --safe #-}

module Family where

open import Basis

Sub : (ℓ₀ : Level) → Type ℓ₁ → Type (suc ℓ₀ ⊔ ℓ₁)
Sub ℓ A = Σ (Set ℓ) (λ I → I → A)

index : Sub ℓ₁ A → Type ℓ₁
index (I , _) = I

-- Application of a family over X to an index.
_$_ : (ℱ : Sub ℓ₀ A) → index ℱ → A
_$_ (_ , f) = f

infixr 7 _$_

-- Membership for families.
_ε_ : A → Sub ℓ₁ A → Type _
x ε (_ , f) = fiber f x

-- Composition of a family with a function.
_⟨$⟩_ : {X : Type ℓ₀} {Y : Type ℓ₁} → (g : X → Y) → (ℱ : Sub ℓ₂ X) → Sub ℓ₂ Y
g ⟨$⟩ ℱ = (index ℱ) , g ∘ (_$_ ℱ)

fmap : {X : Type ℓ₀} {Y : Type ℓ₁} → (g : X → Y) → (ℱ : Sub ℓ₂ X) → Sub ℓ₂ Y
fmap = _⟨$⟩_

syntax fmap (λ x → e) ℱ = ⁅ e ∣ x ε ℱ ⁆

fmap′ : {X : Type ℓ₀} → (I : Type ℓ₂) → (I → X) → Sub ℓ₂ X
fmap′ I f = (I , f)

syntax fmap′ I (λ i → e) = ⁅ e ∣ i ∶ I ⁆

-- Forall quantification for families.
fam-forall : {X : Type ℓ₀} (ℱ : Sub ℓ₂ X) → (X → hProp ℓ₁) → hProp (ℓ₀ ⊔ ℓ₁ ⊔ ℓ₂)
fam-forall {X = X} ℱ P = ((x : X) → x ε ℱ → [ P x ]) , prop
  where
    prop : isProp ((x : X) → x ε ℱ → [ P x ])
    prop = isPropΠ λ x → isPropΠ λ _ → is-true-prop (P x)

syntax fam-forall ℱ (λ x → P) = ∀[ x ε ℱ ] P

-- Familification of a given powerset.
⟪_⟫ : {A : Type ℓ₀} → (A → hProp ℓ₁) → Sub (ℓ₀ ⊔ ℓ₁) A
⟪_⟫ {A = A} U = (Σ[ x ∈ A ] [ U x ]) , π₀
