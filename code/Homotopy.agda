{-# OPTIONS --without-K #-}

module Homotopy where

open import Common

private
  variable
    ℓ ℓ′ : Level

------------------------------------------------------------------------------------------
-- BASICS
------------------------------------------------------------------------------------------

-- Contractibility.
IsContractible : Set ℓ → Set ℓ
IsContractible X = Σ X (λ c → (x : X) → c ≡ x)

-- Propositionality.
IsProp : Set ℓ → Set ℓ
IsProp A = (x y : A) → x ≡ y

-- Homotopy.
_~_ : {A B : Set ℓ} → (A → B) → (A → B) → Set ℓ
_~_ {_} {A} {B} f g = (x : A) → f x ≡ g x

fiber : {X : Set ℓ} {Y : Set ℓ′} → (f : X → Y) → Y → Set (ℓ ⊔ ℓ′)
fiber {X = X} f y = Σ X (λ x → f x ≡ y)

isequiv : {A : Set ℓ} {B : Set ℓ′} → (f : A → B) → Set (ℓ ⊔ ℓ′)
isequiv {_} {_} {A} {B} f = (y : B) → IsContractible (fiber f y)

center : (X : Set ℓ) → IsContractible X → X
center _ (c , _) = c

centrality : (X : Set ℓ) → (i : IsContractible X) → (x : X) → center X i ≡ x
centrality X (c , φ) = φ

fiber-point : {X : Set ℓ} {Y : Set ℓ′} {f : X → Y} {y : Y}
            → fiber f y → X
fiber-point (x , p) = x

fiber-identification : {X : Set ℓ} {Y : Set ℓ′} {f : X → Y} {y : Y}
                     → (w : fiber f y) → f (fiber-point w) ≡ y
fiber-identification (x , p) = p

inverse : {X : Set ℓ} {Y : Set ℓ′} → (f : X → Y) → isequiv f → Y → X
inverse {X = X} {Y} f e y = fiber-point (center (fiber f y) (e y))

rcancel : {X : Set ℓ} {Y : Set ℓ′}
        → (f : X → Y) → (e : isequiv f) → (f ∘ inverse f e) ~ id
rcancel f e y = fiber-identification (center (fiber f y) (e y))

inverse-centrality : {X : Set ℓ} {Y : Set ℓ′}
                   → (f : X → Y) (e : isequiv f) (y : Y) (t : fiber f y)
                   → (inverse f e y , rcancel f e y) ≡ t
inverse-centrality f e y = centrality (fiber f y) (e y)

lcancel : {X : Set ℓ} {Y : Set ℓ′}
        → (f : X → Y) → (e : isequiv f) → (inverse f e ∘ f) ~ id
lcancel f e x = cong fiber-point (inverse-centrality f e (f x) (x , refl))

_≃_ : Set ℓ → Set ℓ′ → Set (ℓ ⊔ ℓ′)
A ≃ B = Σ[ f ∈ (A → B) ] (isequiv f)

id-≃ : (X : Set ℓ) → X ≃ X
id-≃ X = id , φ
  where
    φ : (x : X) → IsContractible (fiber id x)
    φ x = (x , refl) , λ { (y , refl) → refl }

idtoeqv : {A B : Set ℓ} → A ≡ B → A ≃ B
idtoeqv {A = A} refl = id , φ
  where
    φ : (y : A) → IsContractible (fiber (λ x → x) y)
    φ x = (x , refl) , λ { (y , refl) → refl }

postulate
  funext : {A : Set ℓ} {B : A → Set ℓ′}
         → (f g : (x : A) → B x)
         → ((x : A) → (f x) ≡ (g x))
         → f ≡ g
  ua : {A B : Set ℓ} → isequiv {_} {_} {A ≡ B} {A ≃ B} idtoeqv

equivtoid : {A B : Set ℓ} → A ≃ B → A ≡ B
equivtoid {A = A} {B} (f , e) = proj₁ (proj₁ (ua {_} {A} {B} (f , e)))

IsSet : Set ℓ → Set ℓ
IsSet A = (x y : A) → (p q : x ≡ y) → p ≡ q

to-subtype-≡ : {X : Set ℓ} {A : X → Set ℓ′}
               {x y : X} {a : A x} {b : A y}
             → ((x : X) → IsProp (A x))
             → x ≡ y
             → (x , a) ≡ (y , b)
to-subtype-≡ {x = x} {y} {a} {b} p refl = cong (λ k → (x , k)) (p x a b)

Σ-resp-prop : {X : Set ℓ} {Y : X → Set ℓ′}
            → IsProp X → ((x : X) → IsProp (Y x)) → IsProp (Σ X Y)
Σ-resp-prop X-prop Y-prop (x₀ , _) (x₁ , _) = to-subtype-≡ Y-prop (X-prop x₀ x₁)

wconst : {X : Set ℓ} {Y : Set ℓ′} → (X → Y) → Set (ℓ ⊔ ℓ′)
wconst {X = X} f = (x x′ : X) → f x ≡ f x′

wconst-endomap : Set ℓ → Set ℓ
wconst-endomap X = Σ (X → X) wconst

wcmap : (X : Set ℓ) → wconst-endomap X → X → X
wcmap X (f , _) = f

wcmap-constancy : (X : Set ℓ) → (c : wconst-endomap X) → wconst (wcmap X c)
wcmap-constancy X (_ , w) = w

wconst-≡-endomaps : Set ℓ → Set ℓ
wconst-≡-endomaps X = (x y : X) → wconst-endomap (x ≡ y)

-- Hedberg's theorem: if the identity type of some type has all wildly constant endomaps
-- then the identity type is a proposition.
Hedberg : {X : Set ℓ}
        → ((x y : X)→ wconst-endomap (x ≡ y))
        → (x y : X) → IsProp (x ≡ y)
Hedberg {ℓ} {X} φ x y p q =
  begin
    p                           ≡⟨ a y p ⟩
    (sym (f x refl) >>> f y p)  ≡⟨ cong (_>>>_ (sym (f x refl))) (κ y p q) ⟩
    (sym (f x refl) >>> f y q)  ≡⟨ sym (a y q) ⟩
    q                           ∎
  where
    f : (y : X) → x ≡ y → x ≡ y
    f = proj₁ ∘ φ x
    κ : (y : X) (p q : x ≡ y) → f y p ≡ f y q
    κ = proj₂ ∘ φ x
    lemma : (a b : X) (p : a ≡ b) → (sym p) >>> p ≡ refl
    lemma _ _ refl = refl
    a : (y : X) (p : x ≡ y) → p ≡ (sym (f x refl)) >>> f y p
    a y refl = sym (lemma y x (f x refl))

-- (Generalised) Hedberg's *theorem*.
wconst-≡-endomap⇒set : (X : Set ℓ) → wconst-≡-endomaps X → IsSet X
wconst-≡-endomap⇒set X wconst = Hedberg wconst

-- Converse of Hedberg's theorem which is trivial.
set⇒wconst-≡-endomap : (X : Set ℓ) → IsSet X → wconst-≡-endomaps X
set⇒wconst-≡-endomap X X-set x y = id , X-set x y

contra⇒prop : {A : Set ℓ} → IsContractible A → IsProp A
contra⇒prop (c , φ) x y = begin x ≡⟨ sym (φ x) ⟩ c ≡⟨ φ y ⟩ y ∎

prop⇒set : {A : Set ℓ} → IsProp A → IsSet A
prop⇒set {A = A} A-prop x y = wconst-≡-endomap⇒set _ f x y
  where
    f : wconst-≡-endomaps A
    f x y = (λ _ → A-prop x y) , λ _ _ → refl

------------------------------------------------------------------------------------------
-- PROPOSITIONS
------------------------------------------------------------------------------------------

-- The type of propositions.
Ω : (ℓ : Level) → Set (suc ℓ)
Ω ℓ = Σ[ p ∈ (Set ℓ) ] (IsProp p)

_holds : Ω ℓ → Set ℓ
(P , _) holds = P

holds-prop : (p : Ω ℓ) → IsProp (p holds)
holds-prop (P , i) = i

-- Some things that are propositions

-- The product of two propositions is a proposition.
×-resp-prop : (A : Set ℓ) → (B : Set ℓ′) → IsProp A → IsProp B → IsProp (A × B)
×-resp-prop A B A-prop B-prop (a₀ , b₀) (a₁ , b₁) =
  begin
    (a₀ , b₀) ≡⟨ cong (λ k → (k , b₀)) (A-prop a₀ a₁) ⟩
    (a₁ , b₀) ≡⟨ cong (λ k → (a₁ , k)) (B-prop b₀ b₁) ⟩
    (a₁ , b₁)
  ∎

-- Dependent functions respect propositionality.
∏-resp-prop : {X : Set ℓ} {A : X → Set ℓ′}
            → ((x : X) → IsProp (A x)) → IsProp ((x : X) → A x)
∏-resp-prop i f g = funext _ _ λ x → i x (f x) (g x)

_×p_ : Ω ℓ → Ω ℓ → Ω ℓ
(A , A-prop) ×p (B , B-prop) = (A × B) , ×-resp-prop A B A-prop B-prop

-- Being contractible is a proposition.
IsContractible-prop : {A : Set ℓ} → IsProp (IsContractible A)
IsContractible-prop {A = A} c@(a₀ , c₀) (a₁ , c₁) = to-subtype-≡ foo (c₀ a₁)
  where
    bar : IsSet A
    bar = prop⇒set (contra⇒prop c)
    foo : (x : A) → IsProp ((y : A) → x ≡ y)
    foo x = λ f g → funext _ _ λ y → bar x y (f y) (g y)

-- Being a proposition is a proposition.
IsProp-prop : {X : Set ℓ} → IsProp (IsProp X)
IsProp-prop {X = X} X-prop₀ X-prop₁ = funext _ _ exteq′
  where
    X-set : IsSet X
    X-set = prop⇒set X-prop₀
    exteq : (x y : X) → X-prop₀ x y ≡ X-prop₁ x y
    exteq x y = X-set x y (X-prop₀ x y) (X-prop₁ x y)
    exteq′ : (x : X) → X-prop₀ x ≡ X-prop₁ x
    exteq′ x = funext _ _ λ y → exteq x y

IsSet-prop : {X : Set ℓ} → IsProp (IsSet X)
IsSet-prop = ∏-resp-prop λ x → ∏-resp-prop λ y → IsProp-prop

-- Being equivalence is a proposition.
equiv-prop : {X : Set ℓ} {Y : Set ℓ′} → (f : X → Y) → IsProp (isequiv f)
equiv-prop {X = X} f = ∏-resp-prop (λ _ → IsContractible-prop)

-- Logically equivant propositions are equivalent.
P↔Q⇒P≃Q : {X Y : Set ℓ} → IsProp X → IsProp Y → (X → Y) → (Y → X) → X ≃ Y
P↔Q⇒P≃Q {X = X} {Y} p q f g = f , λ y → ((g y) , (q (f (g y)) y)) , bar y
  where
    postulate bar : (y : Y) (fib : fiber f y) → (g y , q (f (g y)) y) ≡ fib

postulate
  Ω-ext : {ℓ : Level} {p q : Ω ℓ} → (p holds → q holds) → (q holds → p holds) → p ≡ q

------------------------------------------------------------------------------------------
-- SETS
------------------------------------------------------------------------------------------

------------------------------------------------------------------------------------------
-- SET CLOSURE
------------------------------------------------------------------------------------------

postulate ∏-set : {X : Set ℓ} {Y : X → Set ℓ′}
                → ((x : X) → IsSet (Y x)) → IsSet ((x : X) → Y x)

_=×=_ : {A : Set ℓ} {B : Set ℓ′} → (x y : A × B) → Set (ℓ ⊔ ℓ′)
_=×=_ {B = B} (a₀ , b₀) (a₁ , b₁) = (a₀ ≡ a₁) × (b₀ ≡ b₁)

ap-pr₁ : {A : Set ℓ} {B : A → Set ℓ′} {x y : Σ A B} → x ≡ y → proj₁ x ≡ proj₁ y
ap-pr₁ refl = refl

ap-pr₂ : {A : Set ℓ} {B : Set ℓ′} {x y : A × B} → x ≡ y → (proj₂ x) ≡ proj₂ y
ap-pr₂ refl = refl

pair⁼ : {A : Set ℓ} {B : Set ℓ′} {x y : A × B} → x =×= y → x ≡ y
pair⁼ {x = (x₀ , y₀)} {x₁ , y₁} (refl , refl) = refl

×-set : {A : Set ℓ} {B : Set ℓ′} → IsSet A → IsSet B → IsSet (A × B)
×-set {A = A} {B} A-set B-set (x₀ , y₀) (x₁ , y₁) p q =
  p                             ≡⟨ φ                             ⟩
  pair⁼ (ap-pr₁ p , ap-pr₂ p)   ≡⟨ cong (λ k → pair⁼ (k , _)) I  ⟩
  pair⁼ (ap-pr₁ q , ap-pr₂ p)   ≡⟨ cong (λ k → pair⁼ (_ , k)) II ⟩
  pair⁼ (ap-pr₁ q , ap-pr₂ q)   ≡⟨ ψ                             ⟩
  q                             ∎
  where
    -- TODO: do this without using `rewrite`.
    φ : p ≡ pair⁼ (ap-pr₁ p , ap-pr₂ p)
    φ rewrite p = refl
    -- TODO: do this without using `rewrite`.
    ψ : pair⁼ (ap-pr₁ q , ap-pr₂ q) ≡ q
    ψ rewrite q = refl
    I : ap-pr₁ p ≡ ap-pr₁ q
    I = A-set x₀ x₁ (ap-pr₁ p) (ap-pr₁ q)
    II : ap-pr₂ p ≡ ap-pr₂ q
    II = B-set y₀ y₁ (ap-pr₂ p) (ap-pr₂ q)

-- TODO: generalise ×-set to Σ-types.
postulate
  Σ-set : {A : Set ℓ} {B : A → Set ℓ′} → IsSet A → ((x : A) → IsSet (B x)) → IsSet (Σ A B)

------------------------------------------------------------------------------------------
-- POWERSETS
------------------------------------------------------------------------------------------

Ω-set : IsSet (Ω ℓ)
Ω-set {ℓ} = wconst-≡-endomap⇒set (Ω ℓ) c
  where
    _↔_ : (p q : Ω ℓ) → Set ℓ
    p ↔ q = (p holds → q holds) × (q holds → p holds)
    ↔-set : (p q : Ω ℓ) → IsProp (p ↔ q)
    ↔-set p q =
      ×-resp-prop _ _ (∏-resp-prop λ _ → holds-prop q) (∏-resp-prop λ _ → holds-prop p)
    g : (p q : Ω ℓ) → p ≡ q → p ↔ q
    g p q refl = id , id
    h : (p q : Ω ℓ) → p ↔ q → p ≡ q
    h p q p↔q = Ω-ext (proj₁ p↔q) (proj₂ p↔q)
    f : (P Q : Ω ℓ) → P ≡ Q → P ≡ Q
    f P Q = h P Q ∘ g P Q
    f-const : (P Q : Ω ℓ) (d e : P ≡ Q) → f P Q d ≡ f P Q e
    f-const P Q d e = cong (h P Q) (↔-set P Q (g P Q d) (g P Q e))
    c : (p q : Ω ℓ) → Σ[ f ∈ (p ≡ q → p ≡ q) ] (wconst f)
    c P Q = f P Q , f-const P Q

𝒫 : Set ℓ → Set (suc ℓ)
𝒫 {ℓ} X = X → Ω ℓ

𝒫-set : {X : Set ℓ} → IsSet (𝒫 X)
𝒫-set = ∏-set (λ _ → Ω-set)

_∈_ : {X : Set ℓ} → X → 𝒫 X → Set ℓ
x ∈ A = A x holds

_⊆_ : {X : Set ℓ} → 𝒫 X → 𝒫 X → Set ℓ
_⊆_ {X = X} S T = (x : X) → x ∈ S → x ∈ T

subsetext : {X : Set ℓ} {A B : 𝒫 X} → A ⊆ B → B ⊆ A → A ≡ B
subsetext {X = X} {A} {B} A⊆B B⊆A = funext _ _ φ
  where
    φ : (x : X) → A x ≡ B x
    φ x = to-subtype-≡ (λ _ → IsProp-prop) (equivtoid foo)
      where
        foo : (A x holds) ≃ (B x holds)
        foo = P↔Q⇒P≃Q (proj₂ (A x)) (proj₂ (B x)) (A⊆B x) (B⊆A x)

-- --}
-- --}
-- --}
