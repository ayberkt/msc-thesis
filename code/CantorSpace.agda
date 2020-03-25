{-# OPTIONS --cubical --safe #-}

module CantorSpace where

open import Basis
open import Cubical.Core.Everything
open import Cubical.Relation.Nullary using (Discrete; yes; no; Dec; ¬_)
open import Cubical.Relation.Nullary.DecidableEq using (Discrete→isSet)
open import Cubical.Data.Empty.Base  using (⊥; ⊥-elim)
open import Cubical.Data.Unit.Base   using (Unit; tt)
open import Cubical.Data.Bool.Base
open import Truncation
open import Poset
open import FormalTopology

data 𝔹 : Type₀ where
  true false : 𝔹

case𝔹 : {A : Type ℓ} → 𝔹 → A → A → A
case𝔹 true  x _ = x
case𝔹 false _ y = y

𝔹-discrete : Discrete 𝔹
𝔹-discrete true  true  = yes refl
𝔹-discrete true  false = no (λ p → subst (λ b → case𝔹 b 𝔹 ⊥) p false)
𝔹-discrete false true  = no (λ p → subst (λ b → case𝔹 b ⊥ 𝔹) p true)
𝔹-discrete false false = yes refl

data ℂ : Type₀ where
  []  : ℂ
  _⌢_ : ℂ → 𝔹 → ℂ

caseℂ : {A : Type ℓ} → ℂ → A → (𝔹 → ℂ → A) → A
caseℂ []       e c = e
caseℂ (xs ⌢ x) e c = c x xs

lemma : (xs ys : ℂ) (x y : 𝔹) → xs ⌢ x ≡ ys ⌢ y → xs ≡ ys
lemma xs ys x y p = subst NTS (sym p) refl
  where
    NTS : ℂ → Type ℓ-zero
    NTS []        = []  ≡ ys
    NTS (xs′ ⌢ x) = xs′ ≡ ys

lemma′ : (xs ys : ℂ) (x y : 𝔹) → xs ⌢ x ≡ ys ⌢ y → x ≡ y
lemma′ xs ys x y p with 𝔹-discrete x y
lemma′ xs ys x y p | yes q = q
lemma′ xs ys x y p | no ¬q =  sym (subst {x = xs ⌢ x} {y = ys ⌢ y} NTS p refl)
  where
    NTS : ℂ → Type ℓ-zero
    NTS []       = ⊥
    NTS (zs ⌢ z) = z ≡ x

lemma2 : (xs : ℂ) (x : 𝔹) → ¬ ((xs ⌢ x) ≡ [])
lemma2 xs x p = subst NTS p p
  where
    NTS : ℂ → Type ℓ-zero
    NTS []       = ⊥
    NTS (ys ⌢ y) = (ys ⌢ y) ≡ []

ℂ-discrete : Discrete ℂ
ℂ-discrete [] [] = yes refl
ℂ-discrete [] (ys ⌢ y) = no λ p → lemma2 ys y (sym p)
ℂ-discrete (xs ⌢ x) [] = no λ p → lemma2 xs x p
ℂ-discrete (xs ⌢ x) (ys ⌢ y) with 𝔹-discrete x y
ℂ-discrete (xs ⌢ x) (ys ⌢ y) | yes p with ℂ-discrete xs ys
ℂ-discrete (xs ⌢ x) (ys ⌢ y) | yes p | yes q = subst (λ xs′ → Dec (xs′ ⌢ x ≡ ys ⌢ y)) (sym q) (subst (λ x′ → Dec (ys ⌢ x′ ≡ ys ⌢ y)) (sym p) (yes refl))
ℂ-discrete (xs ⌢ x) (ys ⌢ y) | yes p | no ¬q = no λ q → ¬q (lemma xs ys x y q)
ℂ-discrete (xs ⌢ x) (ys ⌢ y) | no ¬p = no (λ p → ¬p (lemma′ xs ys x y p))

ℂ-set : IsSet ℂ
ℂ-set = Discrete→isSet ℂ-discrete

infixl 5 _⌢_

_++_ : ℂ → ℂ → ℂ
xs ++ []       = xs
xs ++ (ys ⌢ y) = (xs ++ ys) ⌢ y

++-left-id : (xs : ℂ) → [] ++ xs ≡ xs
++-left-id [] = refl
++-left-id (xs ⌢ x) = cong (λ - → - ⌢ x) (++-left-id xs)

snoc-lemma : (xs ys : ℂ) (x : 𝔹) → (xs ⌢ x) ++ ys ≡ xs ++ (([] ⌢ x) ++ ys)
snoc-lemma xs [] x = refl
snoc-lemma xs (ys ⌢ y) x = cong (λ - → - ⌢ y) (snoc-lemma xs ys x)

lemma3 : (xs : ℂ) (ys : ℂ) (y : 𝔹)  → ¬ (xs ≡ xs ++ (ys ⌢ y))
lemma3 [] ys y p = ⊥-elim (lemma2 ys y (ys ⌢ y ≡⟨ sym (cong (λ - → - ⌢ y) (++-left-id ys)) ⟩ ([] ++ ys) ⌢ y ≡⟨ sym p ⟩ [] ∎))
lemma3 (xs ⌢ x) [] y p = ⊥-elim (lemma3 xs [] x (lemma xs (xs ⌢ x) x y p))
lemma3 (xs ⌢ x) (ys ⌢ y) y′ p = ⊥-elim (lemma3 xs (([] ⌢ x) ++ ys) y bar)
  where
    foo : xs ≡ ((xs ⌢ x) ++ ys) ⌢ y
    foo = lemma xs ((xs ⌢ x) ++ (ys ⌢ y)) x y′ p
    bar : xs ≡ (xs ++ (([] ⌢ x) ++ ys)) ⌢ y
    bar = xs ≡⟨ foo ⟩ ((xs ⌢ x) ++ ys) ⌢ y ≡⟨ snoc-lemma xs (ys ⌢ y) x ⟩ (xs ++ (([] ⌢ x) ++ ys)) ⌢ y ∎

some-other-lemma : (xs : ℂ) (y : 𝔹) → ¬ (xs ≡ (xs ⌢ y))
some-other-lemma [] y p = subst NTS p tt
  where
    NTS : ℂ → Type ℓ-zero
    NTS []       = Unit
    NTS (x ⌢ xs) = ⊥
some-other-lemma (xs ⌢ x) y p = ⊥-elim (some-other-lemma xs x (lemma xs (xs ⌢ x) x y p))

lemma3′ : (xs ys : ℂ) (y : 𝔹) → ¬ (xs ≡ (xs ⌢ y) ++ ys)
lemma3′ [] [] y p = subst NTS p tt
  where
    NTS : ℂ → Type ℓ-zero
    NTS []       = Unit
    NTS (xs ⌢ x) = ⊥
lemma3′ [] (ys ⌢ _) y p = subst NTS p tt
  where
    NTS : ℂ → Type ℓ-zero
    NTS []       = Unit
    NTS (xs ⌢ x) = ⊥
lemma3′ (xs ⌢ x) [] y p = ⊥-elim (some-other-lemma xs x (lemma xs (xs ⌢ x) x y p))
lemma3′ (xs ⌢ x) (ys ⌢ y) y′ p = ⊥-elim (lemma3′ xs (([] ⌢ y′) ++ ys) x bar)
  where
    foo : xs ≡ (((xs ⌢ x) ++ ([] ⌢ y′)) ++ ys)
    foo = lemma xs ((xs ⌢ x ⌢ y′) ++ ys) x y p
    bar : xs ≡ (xs ⌢ x) ++ (([] ⌢ y′) ++ ys)
    bar = xs ≡⟨ foo ⟩ ((((xs ⌢ x) ++ ([] ⌢ y′)) ++ ys)) ≡⟨ snoc-lemma ((xs ⌢ x) ++ []) ys y′ ⟩ ((xs ⌢ x) ++ (([] ⌢ y′) ++ ys)) ∎

[]-left-id : (xs : ℂ) → [] ++ xs ≡ xs
[]-left-id []       = refl
[]-left-id (xs ⌢ x) = cong (λ - → - ⌢ x) ([]-left-id xs)

assoc : (xs ys zs : ℂ) → xs ++ (ys ++ zs) ≡ (xs ++ ys) ++ zs
assoc xs ys []       = refl
assoc xs ys (zs ⌢ z) = cong (λ - → - ⌢ z) (assoc xs ys zs)

++-lemma : (xs ys zs₀ zs₁ : ℂ) → xs ≡ ys ++ zs₀ → xs ≡ ys ++ zs₁ → zs₀ ≡ zs₁
++-lemma [] [] zs₀ zs₁ p q = zs₀ ≡⟨ sym (++-left-id zs₀) ⟩ [] ++ zs₀ ≡⟨ sym p ⟩ [] ≡⟨ q ⟩ [] ++ zs₁ ≡⟨ ++-left-id zs₁ ⟩ zs₁ ∎
++-lemma [] (ys ⌢ y) [] [] p q = refl
++-lemma [] (ys ⌢ y) [] (zs₁ ⌢ x) p q = ⊥-elim (lemma2 ys y (sym p))
++-lemma [] (ys ⌢ y) (zs₀ ⌢ x) [] p q = ⊥-elim (lemma2 ys y (sym q))
++-lemma [] (ys ⌢ y) (zs₀ ⌢ x) (zs₁ ⌢ x₁) p q = ⊥-elim (lemma2 ((ys ⌢ y) ++ zs₀) x (sym p))
++-lemma (xs ⌢ x) [] [] zs₁ p q = ⊥-elim (lemma2 xs x p)
++-lemma (xs ⌢ x) [] (zs₀ ⌢ z₀) [] p q = ⊥-elim (lemma2 xs x q)
++-lemma (xs ⌢ x) [] (zs₀ ⌢ z₀) (zs₁ ⌢ z₁) p q =
  zs₀ ⌢ z₀         ≡⟨ cong (λ - → - ⌢ z₀) (sym (++-left-id zs₀)) ⟩
  ([] ++ zs₀) ⌢ z₀ ≡⟨ sym p ⟩
  xs ⌢ x           ≡⟨ q ⟩
  ([] ++ zs₁) ⌢ z₁ ≡⟨ cong (λ - → - ⌢ z₁) (++-left-id zs₁) ⟩
  zs₁ ⌢ z₁         ∎
++-lemma (xs ⌢ x) (ys ⌢ y) [] [] p q = refl
++-lemma (xs ⌢ x) (ys ⌢ y) [] (zs₁ ⌢ z₁) p q = ⊥-elim (lemma3′ ys zs₁ y (lemma ys ((ys ⌢ y) ++ zs₁) y z₁ NTS))
  where
    NTS : ys ⌢ y ≡ ((ys ⌢ y) ++ zs₁) ⌢ z₁
    NTS = ys ⌢ y ≡⟨ sym p ⟩ xs ⌢ x ≡⟨ q ⟩ ((ys ⌢ y) ++ zs₁) ⌢ z₁ ∎
++-lemma (xs ⌢ x) (ys ⌢ y) (zs₀ ⌢ z₀) [] p q = ⊥-elim (lemma3′ ys zs₀ y (lemma ys ((ys ⌢ y) ++ zs₀) y z₀ NTS))
  where
    NTS : ys ⌢ y ≡ ((ys ⌢ y) ++ zs₀) ⌢ z₀
    NTS = ys ⌢ y ≡⟨ sym q ⟩ xs ⌢ x ≡⟨ p ⟩ ((ys ⌢ y) ++ (zs₀ ⌢ z₀)) ∎
++-lemma (xs ⌢ x) (ys ⌢ y) (zs₀ ⌢ z₀) (zs₁ ⌢ z₁) p q with 𝔹-discrete z₀ z₁
++-lemma (xs ⌢ x) (ys ⌢ y) (zs₀ ⌢ z₀) (zs₁ ⌢ z₁) p q | yes z₀=z₁ = zs₀ ⌢ z₀ ≡⟨ cong (λ - → - ⌢ z₀) IH ⟩ zs₁ ⌢ z₀ ≡⟨ cong (_⌢_ zs₁) z₀=z₁ ⟩ zs₁ ⌢ z₁ ∎
  where
    foo : xs ≡ (ys ⌢ y) ++ zs₁
    foo = lemma xs ((ys ⌢ y) ++ zs₁) x z₁ q
    bar : xs ≡ (ys ⌢ y) ++ zs₀
    bar = lemma xs ((ys ⌢ y) ++ zs₀) x z₀ p
    IH : zs₀ ≡ zs₁
    IH = ++-lemma xs (ys ⌢ y) zs₀ zs₁ bar foo
++-lemma (xs ⌢ x) (ys ⌢ y) (zs₀ ⌢ z₀) (zs₁ ⌢ z₁) p q | no ¬p = ⊥-elim (¬p (lemma′ ((ys ⌢ y) ++ zs₀) ((ys ⌢ y) ++ zs₁) z₀ z₁ (((ys ⌢ y) ++ zs₀) ⌢ z₀ ≡⟨ sym p ⟩ xs ⌢ x ≡⟨ q ⟩ ((ys ⌢ y) ++ zs₁) ⌢ z₁ ∎)))

_≤_ : ℂ → ℂ → hProp ℓ-zero
xs ≤ ys = (Σ[ zs ∈ ℂ ] xs ≡ ys ++ zs) , prop
  where
    prop : IsProp (Σ[ zs ∈ ℂ ] xs ≡ ys ++ zs)
    prop (zs₀ , p) (zs₁ , q) = to-subtype-≡ (zs₀ , p) (zs₁ , q) (λ ws → ℂ-set xs (ys ++ ws)) (++-lemma xs ys zs₀ zs₁ p q)

cantor-poset : Poset ℓ-zero ℓ-zero
cantor-poset = ℂ , ((_≤_ , ℂ-set) , (≤-refl , ≤-trans , ≤-antisym))
  where
    ≤-refl : (xs : ℂ) → xs ≤ xs is-true
    ≤-refl xs = [] , refl
    ≤-trans : (xs ys zs : ℂ) → xs ≤ ys is-true → ys ≤ zs is-true → xs ≤ zs is-true
    ≤-trans xs ys zs xs≤ys ys≤zs = NTS xs≤ys ys≤zs
      where
        NTS : Σ[ as ∈ ℂ ] xs ≡ ys ++ as → Σ[ bs ∈ ℂ ] ys ≡ zs ++ bs → xs ≤ zs is-true
        NTS (as , p) (bs , q) = (bs ++ as) , NTS′
          where
            NTS′ : xs ≡ (zs ++ (bs ++ as))
            NTS′ = xs ≡⟨ p ⟩ (ys ++ as) ≡⟨ cong (λ - → - ++ as) q ⟩ ((zs ++ bs) ++ as) ≡⟨ sym (assoc zs bs as) ⟩ (zs ++ (bs ++ as)) ∎
    ≤-antisym : (xs ys : ℂ) → xs ≤ ys is-true → ys ≤ xs is-true → xs ≡ ys
    ≤-antisym xs ys xs≤ys ys≤xs = NTS xs≤ys ys≤xs
      where
        NTS : Σ[ as ∈ ℂ ] xs ≡ ys ++ as → Σ[ bs ∈ ℂ ] ys ≡ xs ++ bs → xs ≡ ys
        NTS ([] , p) ([] , q) = p
        NTS ([] , p) (bs ⌢ x , q) = p
        NTS (as ⌢ x , p) ([] , q) = sym q
        NTS (as ⌢ a , p) (bs ⌢ b  , q) = ⊥-elim (lemma3 xs ((bs ⌢ b) ++ as) a NTS′)
          where
            NTS′ : xs ≡ xs ++ ((bs ⌢ b) ++ (as ⌢ a))
            NTS′ = xs                           ≡⟨ p                                ⟩
                   ys ++ (as ⌢ a)               ≡⟨ cong (λ - → - ++ (as ⌢ a)) q     ⟩
                   (xs ++ (bs ⌢ b)) ++ (as ⌢ a) ≡⟨ sym (assoc xs (bs ⌢ b) (as ⌢ a)) ⟩
                   xs ++ ((bs ⌢ b) ++ (as ⌢ a)) ∎

Φ : (xs ys : ℂ) (x y : 𝔹) → (xs ⌢ x) ≤ (ys ⌢ y) is-true → xs ≤ ys is-true
Φ xs ys x y ([] , p) = [] , (lemma xs ys x y p)
Φ xs ys x y (zs ⌢ z , p) = (([] ⌢ y) ++ zs) , (xs ≡⟨ lemma xs ((ys ⌢ y) ++ zs) x z p ⟩ ((ys ⌢ y) ++ zs) ≡⟨ snoc-lemma ys zs y ⟩ ys ++ (([] ⌢ y) ++ zs) ∎)

[]-lemma : (xs ys : ℂ) → [] ≡ (xs ++ ys) → xs ≡ []
[]-lemma [] [] p = refl
[]-lemma [] (ys ⌢ x₁) p = refl
[]-lemma (xs ⌢ x) [] p = ⊥-elim (lemma2 xs x (sym p))
[]-lemma (xs ⌢ x) (ys ⌢ y) p = subst NTS p tt
  where
    NTS : ℂ → Type ℓ-zero
    NTS []       = Unit
    NTS (zs ⌢ z) = (xs ⌢ x) ≡ []

nonempty : ℂ → Type ℓ-zero
nonempty []       = ⊥
nonempty (xs ⌢ x) = Unit

head : (xs : ℂ) → nonempty xs → 𝔹
head ([] ⌢ x) p = x
head ((xs ⌢ x′) ⌢ x) p = head (xs ⌢ x′) tt

tail : (xs : ℂ) → nonempty xs → ℂ
tail ([] ⌢ x) tt = []
tail (xs ⌢ x₀ ⌢ x₁) p = (tail (xs ⌢ x₀) tt) ⌢ x₁

hd-tl-lemma : (xs : ℂ) → (ne : nonempty xs) → ([] ⌢ (head xs ne)) ++ (tail xs ne) ≡ xs
hd-tl-lemma ([] ⌢ x) tt = refl
hd-tl-lemma (xs ⌢ x₀ ⌢ x₁) tt = cong (λ - → - ⌢ x₁) (hd-tl-lemma (xs ⌢ x₀) tt)

cantor : FormalTopology ℓ-zero ℓ-zero
cantor = (cantor-poset , is , mono) , sim
  where
    is : InteractionStr ℂ
    is = (λ _ → Unit) , (λ _ → 𝔹) , λ {x = xs} b → xs ⌢ b
    mono : HasMonotonicity cantor-poset is
    mono a b c = [] ⌢ c , refl
    sim : HasSimulation (cantor-poset , is , mono)
    sim xs ys xs≤ys@([] , p)     tt = tt , (λ c₀ → c₀ , ([] , (cong (λ - → - ⌢ c₀) p)))
    sim [] ys xs≤ys@(zs ⌢ z , p) tt = tt , ⊥-elim (lemma2 (ys ++ zs) z (sym p))
    sim (xs ⌢ x) ys xs≤ys@(zs ⌢ z , p) tt = tt , NTS
      where
        IH : (c₀ : 𝔹) → Σ[ c ∈ 𝔹 ] (xs ⌢ c₀) ≤ (ys ⌢ c) is-true
        IH = π₁ (sim xs ys (zs , lemma xs (ys ++ zs) x z p) tt)
        NTS : (c₀ : 𝔹) → Σ[ c ∈ 𝔹 ] (xs ⌢ x ⌢ c₀) ≤ (ys ⌢ c) is-true
        NTS c₀ = head (zs ⌢ z) tt , subst (λ - → ((- ⌢ c₀) ≤ (ys ⌢ head (zs ⌢ z) tt)) is-true) (sym p) NTS′
          where
            NTS′ : ((ys ++ zs) ⌢ z ⌢ c₀) ≤ (ys ⌢ head (zs ⌢ z) tt) is-true
            NTS′ = ((tail (zs ⌢ z) tt) ⌢ c₀) , rem
              where
                rem : (ys ++ zs) ⌢ z ⌢ c₀ ≡ ((ys ⌢ head (zs ⌢ z) tt) ++ (tail (zs ⌢ z) tt ⌢ c₀))
                rem = (ys ++ zs) ⌢ z ⌢ c₀      ≡⟨ refl ⟩
                      (ys ++ (zs ⌢ z)) ⌢ c₀    ≡⟨ refl ⟩
                      ys ++ ((zs ⌢ z) ⌢ c₀)    ≡⟨ cong (λ - → ys ++ (- ⌢ c₀)) (sym (hd-tl-lemma (zs ⌢ z) tt)) ⟩
                      (ys ++ (([] ⌢ (head (zs ⌢ z) tt)) ++ (tail (zs ⌢ z) tt))) ⌢ c₀ ≡⟨ cong (λ - → - ⌢ c₀) (sym (snoc-lemma ys (tail (zs ⌢ z) tt) (head (zs ⌢ z) tt))) ⟩
                      ((ys ⌢ head (zs ⌢ z) tt) ++ tail (zs ⌢ z) tt) ⌢ c₀ ∎
