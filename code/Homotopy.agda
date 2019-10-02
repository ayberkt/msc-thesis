{-# OPTIONS --without-K #-}

module Homotopy where

open import Common

_~_ : {ℓ : Level} {A B : Set ℓ} → (A → B) → (A → B) → Set ℓ
_~_ {_} {A} {B} f g = (x : A) → f x ≡ g x

fiber : {ℓ ℓ′ : Level} {X : Set ℓ} {Y : Set ℓ′} → (f : X → Y) → Y → Set (ℓ ⊔ ℓ′)
fiber {X = X} f y = Σ X (λ x → f x ≡ y)

IsContractible : {ℓ : Level} → Set ℓ → Set ℓ
IsContractible X = Σ X (λ c → (x : X) → c ≡ x)

IsProp : {ℓ : Level} → Set ℓ → Set ℓ
IsProp A = (x y : A) → x ≡ y

isequiv : {ℓ ℓ′ : Level} {A : Set ℓ} {B : Set ℓ′} → (f : A → B) → Set (ℓ ⊔ ℓ′)
isequiv {_} {_} {A} {B} f = (y : B) → IsContractible (fiber f y)

center : {ℓ : Level} → (X : Set ℓ) → IsContractible X → X
center _ (c , _) = c

centrality : {ℓ : Level} → (X : Set ℓ) → (i : IsContractible X) → (x : X) → center X i ≡ x
centrality X (c , φ) = φ

fiber-point : {ℓ ℓ′ : Level} {X : Set ℓ} {Y : Set ℓ′} {f : X → Y} {y : Y}
            → fiber f y → X
fiber-point (x , p) = x

fiber-identification : {ℓ ℓ′ : Level} {X : Set ℓ} {Y : Set ℓ′} {f : X → Y} {y : Y}
                     → (w : fiber f y) → f (fiber-point w) ≡ y
fiber-identification (x , p) = p

inverse : {ℓ ℓ′ : Level} {X : Set ℓ} {Y : Set ℓ′} → (f : X → Y) → isequiv f → Y → X
inverse {X = X} {Y} f e y = fiber-point (center (fiber f y) (e y))

rcancel : {ℓ ℓ′ : Level} {X : Set ℓ} {Y : Set ℓ′}
        → (f : X → Y) → (e : isequiv f) → (f ∘ inverse f e) ~ id
rcancel f e y = fiber-identification (center (fiber f y) (e y))

inverse-centrality : {ℓ ℓ′ : Level} {X : Set ℓ} {Y : Set ℓ′}
                   → (f : X → Y) (e : isequiv f) (y : Y) (t : fiber f y)
                   → (inverse f e y , rcancel f e y) ≡ t
inverse-centrality f e y = centrality (fiber f y) (e y)

lcancel : {ℓ ℓ′ : Level} {X : Set ℓ} {Y : Set ℓ′}
        → (f : X → Y) → (e : isequiv f) → (inverse f e ∘ f) ~ id
lcancel f e x = cong fiber-point (inverse-centrality f e (f x) (x , refl))

_≃_ : {ℓ ℓ′ : Level} → Set ℓ → Set ℓ′ → Set (ℓ ⊔ ℓ′)
A ≃ B = Σ[ f ∈ (A → B) ] (isequiv f)

id-≃ : {ℓ : Level} → (X : Set ℓ) → X ≃ X
id-≃ X = id , φ
  where
    φ : (x : X) → IsContractible (fiber id x)
    φ x = (x , refl) , λ { (y , refl) → refl }

idtoeqv : {ℓ : Level} → {A B : Set ℓ} → A ≡ B → A ≃ B
idtoeqv {A = A} refl = id , φ
  where
    φ : (y : A) → IsContractible (fiber (λ x → x) y)
    φ x = (x , refl) , λ { (y , refl) → refl }

postulate
  funext : {ℓ ℓ′ : Level} {A : Set ℓ} {B : A → Set ℓ′}
         → (f g : (x : A) → B x)
         → ((x : A) → (f x) ≡ (g x))
         → f ≡ g
  ua : {ℓ : Level} {A B : Set ℓ} → isequiv {_} {_} {A ≡ B} {A ≃ B} idtoeqv

equivtoid : {ℓ : Level} {A B : Set ℓ} → A ≃ B → A ≡ B
equivtoid {A = A} {B} (f , e) = proj₁ (proj₁ (ua {_} {A} {B} (f , e)))

IsSet : {ℓ : Level} → Set ℓ → Set ℓ
IsSet A = (x y : A) → (p q : x ≡ y) → p ≡ q

Proposition : (ℓ : Level) → Set (suc ℓ)
Proposition ℓ = Σ[ A ∈ (Set ℓ) ] (IsProp A)

-- The product of two propositions is a proposition.
×-resp-prop : {ℓ : Level} → (A B : Set ℓ) → IsProp A → IsProp B → IsProp (A × B)
×-resp-prop A B A-prop B-prop (a₀ , b₀) (a₁ , b₁) =
  begin
    (a₀ , b₀) ≡⟨ cong (λ k → (k , b₀)) (A-prop a₀ a₁) ⟩
    (a₁ , b₀) ≡⟨ cong (λ k → (a₁ , k)) (B-prop b₀ b₁) ⟩
    (a₁ , b₁)
  ∎

_×p_ : {ℓ : Level} → Proposition ℓ → Proposition ℓ → Proposition ℓ
(A , A-prop) ×p (B , B-prop) = (A × B) , ×-resp-prop A B A-prop B-prop

-- Dependent functions respect propositionality.
∏-resp-prop : {ℓ ℓ′ : Level} {X : Set ℓ} {A : X → Set ℓ′}
            → ((x : X) → IsProp (A x))
            → IsProp ((x : X) → A x)
∏-resp-prop i f g = funext _ _ λ x → i x (f x) (g x)

to-subtype-≡ : {ℓ ℓ′ : Level} {X : Set ℓ} {A : X → Set ℓ′}
               {x y : X} {a : A x} {b : A y}
             → ((x : X) → IsProp (A x))
             → x ≡ y
             → (x , a) ≡ (y , b)
to-subtype-≡ {x = x} {y} {a} {b} p refl = cong (λ k → (x , k)) (p x a b)

wconstant : {ℓ ℓ′ : Level} {X : Set ℓ} {Y : Set ℓ′} → (X → Y) → Set (ℓ ⊔ ℓ′)
wconstant {X = X} f = (x x′ : X) → f x ≡ f x′

wconstant-endomap : {ℓ : Level} → Set ℓ → Set ℓ
wconstant-endomap X = Σ (X → X) wconstant

wcmap : {ℓ : Level} (X : Set ℓ) → wconstant-endomap X → X → X
wcmap X (f , _) = f

wcmap-constancy : {ℓ : Level} (X : Set ℓ) → (c : wconstant-endomap X) → wconstant (wcmap X c)
wcmap-constancy X (_ , w) = w

wconstant-≡-endomaps : {ℓ : Level} → Set ℓ → Set ℓ
wconstant-≡-endomaps X = (x y : X) → wconstant-endomap (x ≡ y)

sets-have-wconstant-≡-endomaps : {ℓ : Level} (X : Set ℓ) → IsSet X → wconstant-≡-endomaps X
sets-have-wconstant-≡-endomaps X s x y = id , s x y

props-have-wconstant-≡-endomaps : {ℓ : Level} (X : Set ℓ) → IsProp X → wconstant-≡-endomaps X
props-have-wconstant-≡-endomaps X X-prop x y = (λ _ → X-prop x y) , λ _ _ → refl

-- A type is a set iff its identity types all have designated wconstant endomaps.
postulate
  Hedberg : {ℓ : Level} {X : Set ℓ} (x : X)
          → ((y : X) → wconstant-endomap (x ≡ y))
          → (y : X) → IsProp (x ≡ y)

types-with-wconstant-≡-endomaps-are-sets : {ℓ : Level} (X : Set ℓ)
                                         → wconstant-≡-endomaps X → IsSet X
types-with-wconstant-≡-endomaps-are-sets X c x =
  Hedberg x (λ y → wcmap (x ≡ y) (c x y) , wcmap-constancy (x ≡ y) (c x y))

contra⇒prop : {ℓ : Level} {A : Set ℓ} → IsContractible A → IsProp A
contra⇒prop (c , φ) x y = begin x ≡⟨ sym (φ x) ⟩ c ≡⟨ φ y ⟩ y ∎

prop⇒set : {ℓ : Level} {A : Set ℓ} → IsProp A → IsSet A
prop⇒set {A = A} A-prop =
  types-with-wconstant-≡-endomaps-are-sets A (props-have-wconstant-≡-endomaps A A-prop)

IsContractible-prop : {ℓ : Level} {A : Set ℓ} → IsProp (IsContractible A)
IsContractible-prop {A = A} c@(a₀ , c₀) (a₁ , c₁) = to-subtype-≡ foo (c₀ a₁)
  where
    bar : IsSet A
    bar = prop⇒set (contra⇒prop c)
    foo : (x : A) → IsProp ((y : A) → x ≡ y)
    foo x = λ f g → funext _ _ λ y → bar x y (f y) (g y)

-- Being equivalence is a proposition.
equiv-prop : {ℓ ℓ′ : Level} {X : Set ℓ} {Y : Set ℓ′} → (f : X → Y) → IsProp (isequiv f)
equiv-prop {X = X} f = ∏-resp-prop (λ _ → IsContractible-prop)

-- Logically equivant propositions are equivalent.
P↔Q⇒P≃Q : {ℓ : Level} {X Y : Set ℓ} → IsProp X → IsProp Y → (X → Y) → (Y → X) → X ≃ Y
P↔Q⇒P≃Q {X = X} {Y} p q f g = f , λ y → ((g y) , (q (f (g y)) y)) , bar y
  where
    postulate bar : (y : Y) (fib : fiber f y) → (g y , q (f (g y)) y) ≡ fib
