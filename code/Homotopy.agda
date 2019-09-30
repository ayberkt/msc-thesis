module Homotopy where

open import Common

UIP : {ℓ : Level} {A : Set ℓ} {x y : A} → (p q : x ≡ y) → p ≡ q
UIP refl refl = refl

_~_ : {ℓ : Level} {A B : Set ℓ} → (A → B) → (A → B) → Set ℓ
_~_ {_} {A} {B} f g = (x : A) → f x ≡ g x

isequiv : {ℓ ℓ′ : Level} {A : Set ℓ} {B : Set ℓ′} → (f : A → B) → Set (ℓ ⊔ ℓ′)
isequiv {_} {_} {A} {B} f = (Σ[ g ∈ (B → A) ] (g ∘ f) ~ id) × (Σ[ h ∈ (B → A) ] (f ∘ h) ~ id)

_≃_ : {ℓ ℓ′ : Level} → Set ℓ → Set ℓ′ → Set (ℓ ⊔ ℓ′)
A ≃ B = Σ[ f ∈ (A → B) ] (isequiv f)

idtoeqv : {ℓ : Level} → {A B : Set ℓ} → A ≡ B → A ≃ B
idtoeqv refl = id , ((λ x → x) , (λ x → refl)) , (λ x → x) , (λ x → refl)

postulate
  funext : {ℓ ℓ′ : Level} {A : Set ℓ} {B : A → Set ℓ′}
         → (f g : (x : A) → B x)
         → ((x : A) → (f x) ≡ (g x))
         → f ≡ g
  ua : {ℓ : Level} {A B : Set ℓ} → isequiv {_} {_} {A ≡ B} {A ≃ B} idtoeqv

IsSet : {ℓ : Level} → Set ℓ → Set ℓ
IsSet A = (x y : A) → (p q : x ≡ y) → p ≡ q

IsProp : {ℓ : Level} → Set ℓ → Set ℓ
IsProp A = (x y : A) → x ≡ y

Proposition : (ℓ : Level) → Set (suc ℓ)
Proposition ℓ = Σ[ A ∈ (Set ℓ) ] (IsProp A)

-- The product of two propositions is a proposition.
_×p_ : {ℓ : Level} → Proposition ℓ → Proposition ℓ → Proposition ℓ
(A , A-prop) ×p (B , B-prop) = (A × B) , A×B-prop
  where
    A×B-prop : (x y : A × B) → x ≡ y
    A×B-prop (x₀ , y₀) (x₁ , y₁) =
      begin
        (x₀ , y₀) ≡⟨ cong (λ k → (k , y₀)) (A-prop x₀ x₁) ⟩
        (x₁ , y₀) ≡⟨ cong (λ k → (x₁ , k)) (B-prop y₀ y₁) ⟩
        (x₁ , y₁)
      ∎
