{-# OPTIONS --without-K #-}

module Homotopy where

open import Common
open import Unit
open import Data.Bool using (Bool)
open import Data.List using (List; _∷_; [])
open import HLevels public

private
  variable
    ℓ ℓ′ ℓ₀ ℓ₁ ℓ₂ : Level

------------------------------------------------------------------------------------------
-- BASICS
------------------------------------------------------------------------------------------

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

IsInvertible : {X : Set ℓ₀} {Y : Set ℓ₁} → (X → Y) → Set (ℓ₀ ⊔ ℓ₁)
IsInvertible {X = X} {Y} f = Σ[ g ∈ (Y → X) ] (g ∘ f) ~ id × (f ∘ g) ~ id

postulate
  invertible⇒equiv : {X : Set ℓ₀} {Y : Set ℓ₁} → (f : X → Y) → IsInvertible f → isequiv f

invertibility→≃ : {X : Set ℓ₀} {Y : Set ℓ₁} (f : X → Y) → IsInvertible f → X ≃ Y
invertibility→≃ f inv = f , (invertible⇒equiv f inv)

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

funext-conv : {X : Set ℓ} {Y : X → Set ℓ′}
            → (f g : (x : X) → Y x) → f ≡ g → ((x : X) → f x ≡ g x)
funext-conv f g refl x = refl

equivtoid : {A B : Set ℓ} → A ≃ B → A ≡ B
equivtoid {A = A} {B} (f , e) = proj₁ (proj₁ (ua {_} {A} {B} (f , e)))

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

⊥-prop : IsProp ⊥
⊥-prop () ()

-- The type of propositions.
Ω : (ℓ : Level) → Set (suc ℓ)
Ω ℓ = Σ[ p ∈ (Set ℓ) ] (IsProp p)

_holds : Ω ℓ → Set ℓ
(P , _) holds = P

infix 5 _holds

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

Ω-ext : {ℓ : Level} {P Q : Ω ℓ} → (P holds → Q holds) → (Q holds → P holds) → P ≡ Q
Ω-ext {P = (A , A-prop)} {B , B-prop} P⇒Q Q⇒P =
  to-subtype-≡ (λ _ → IsProp-prop) (equivtoid (P↔Q⇒P≃Q A-prop B-prop P⇒Q Q⇒P))

------------------------------------------------------------------------------------------
-- SETS
------------------------------------------------------------------------------------------

Bool-set : IsSet Bool
Bool-set = wconst-≡-endomap⇒set Bool foo
  where
    foo : (x y : Bool) → wconst-endomap (x ≡ y)
    foo Bool.false Bool.false = (λ x → refl) , (λ x x₁ → refl)
    foo Bool.false Bool.true = (λ x → x) , (λ x ())
    foo Bool.true Bool.false = (λ x → x) , (λ x ())
    foo Bool.true Bool.true = (λ x → refl) , (λ x x₁ → refl)

------------------------------------------------------------------------------------------
-- SET CLOSURE
------------------------------------------------------------------------------------------

∏-set : {X : Set ℓ} {Y : X → Set ℓ′}
      → ((x : X) → IsSet (Y x)) → IsSet ((x : X) → Y x)
∏-set {X = X} {Y} Y-set = wconst-≡-endomap⇒set _ φ
  where
    𝔎 : (x : X) → (y y′ : Y x) → y ≡ y′ → y ≡ y′
    𝔎 x y y′ = proj₁ (set⇒wconst-≡-endomap (Y x) (Y-set x) y y′)
    𝔎-wconst : (x : X) → (y y′ : Y x) → wconst (𝔎 x y y′)
    𝔎-wconst x y y′ = proj₂ (set⇒wconst-≡-endomap (Y x) (Y-set x) y y′)
    φ : wconst-≡-endomaps ((x : X) → Y x)
    φ f g = 𝔏 , 𝔏-wconst
      where
        𝔏 : f ≡ g → f ≡ g
        𝔏 p = funext _ _ λ x → 𝔎 x (f x) (g x) (funext-conv f g p x)
        exteq : f ≡ g → (x : X) → f x ≡ g x
        exteq = funext-conv f g
        𝔏-wconst : wconst 𝔏
        𝔏-wconst p q = cong (funext f g) (funext _ _ λ x → 𝔎-wconst x (f x) (g x) (exteq p x) (exteq q x))

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

IsDecidable : (A : Set ℓ) → Set ℓ
IsDecidable A = A ⊎ (A → ⊥)

HasDecidableEquality : (A : Set ℓ) → Set ℓ
HasDecidableEquality A = (x y : A) → IsDecidable (x ≡ y)

decidable-≡⇒wconst-≡ : (A : Set ℓ) → HasDecidableEquality A → wconst-≡-endomaps A
decidable-≡⇒wconst-≡ A _=A=_ x y with x =A= y
decidable-≡⇒wconst-≡ A _=A=_ x y | inj₁ p = (λ _ → p) , λ _ _ → refl
decidable-≡⇒wconst-≡ A _=A=_ x y | inj₂ p = id , (λ x=y _ → explode (p x=y))

hedberg-theorem : (A : Set ℓ) → HasDecidableEquality A → IsSet A
hedberg-theorem A _=A=_ = wconst-≡-endomap⇒set A (decidable-≡⇒wconst-≡ A _=A=_)

List-set : {A : Set ℓ} → IsSet A → IsSet (List A)
List-set {A = A} A-set = wconst-≡-endomap⇒set (List A) NTS
  where
    A-const-≡-endomap : wconst-≡-endomaps A
    A-const-≡-endomap = set⇒wconst-≡-endomap A A-set

    split₀ : {x y : A} {xs ys : List A} → (x ∷ xs) ≡ (y ∷ ys) → x ≡ y
    split₀ refl = refl

    split₁ : {x y : A} {xs ys : List A} → (x ∷ xs) ≡ (y ∷ ys) → xs ≡ ys
    split₁ refl = refl

    merge : {x y : A} {xs ys : List A} → x ≡ y → xs ≡ ys → (x ∷ xs) ≡ (y ∷ ys)
    merge refl refl = refl

    NTS : wconst-≡-endomaps (List A)
    NTS []       []       = (λ x → refl) , (λ x x₁ → refl)
    NTS []       (_ ∷ _)  = (λ x → x) , (λ x ())
    NTS (x ∷ xs) []       = (λ x → x) , (λ x ())
    NTS (x ∷ xs) (y ∷ ys) =
      (λ eq → merge (proj₁ (A-const-≡-endomap x y) (split₀ eq) ) (proj₁ (NTS xs ys) (split₁ eq))) , φ
      where
        φ : (p q : x ∷ xs ≡ y ∷ ys) → merge (split₀ p) (proj₁ (NTS xs ys) (split₁ p))
                                    ≡ merge (split₀ q) (proj₁ (NTS xs ys) (split₁ q))
        φ p q rewrite proj₂ (A-const-≡-endomap x y) (split₀ p) (split₀ q)
                    | proj₂ (NTS xs ys) (split₁ p) (split₁ q) = refl

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

_∈_ : {X : Set ℓ} → X → 𝒫 X → Ω ℓ
x ∈ A = A x

infix 20 _∈_

_⊆_ : {X : Set ℓ} → 𝒫 X → 𝒫 X → Set ℓ
_⊆_ {X = X} S T = (x : X) → (x ∈ S) holds → (x ∈ T) holds

entirety : {X : Set ℓ} → 𝒫 X
entirety x = ⊤ , ⊤-prop

_∩_ : {X : Set ℓ} → 𝒫 X → 𝒫 X → 𝒫 X
_∩_ {X = X} S T x =
    (x ∈ S holds × x ∈ T holds)
  , ×-resp-prop (x ∈ S holds) (x ∈ T holds) (holds-prop (S x)) (holds-prop (T x))

⊆-refl : {X : Set ℓ} → (S : 𝒫 X) → S ⊆ S
⊆-refl S x x∈S = x∈S

⊆-prop : {X : Set ℓ} → (S : 𝒫 X) → (T : 𝒫 X) → IsProp (S ⊆ T)
⊆-prop S T = ∏-resp-prop λ x → ∏-resp-prop (λ x∈S → holds-prop (T x))

⊆-trans : {X : Set ℓ} → (S T U : 𝒫 X) → S ⊆ T → T ⊆ U → S ⊆ U
⊆-trans S T U S⊆T T⊆U x x∈S = T⊆U x (S⊆T x x∈S)

subsetext : {X : Set ℓ} {A B : 𝒫 X} → A ⊆ B → B ⊆ A → A ≡ B
subsetext {X = X} {A} {B} A⊆B B⊆A = funext _ _ φ
  where
    φ : (x : X) → A x ≡ B x
    φ x = to-subtype-≡ (λ _ → IsProp-prop) (equivtoid foo)
      where
        foo : (A x holds) ≃ (B x holds)
        foo = P↔Q⇒P≃Q (proj₂ (A x)) (proj₂ (B x)) (A⊆B x) (B⊆A x)

⊆-antisym : {X : Set ℓ} → {S T : 𝒫 X} → S ⊆ T → T ⊆ S → S ≡ T
⊆-antisym = subsetext

-- --}
-- --}
-- --}
