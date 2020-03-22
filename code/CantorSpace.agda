{-# OPTIONS --cubical --safe #-}

module CantorSpace where

open import Basis
open import Cubical.Core.Everything
open import Cubical.Relation.Nullary using (Discrete; yes; no; Dec; ¬_)
open import Cubical.Relation.Nullary.DecidableEq using (Discrete→isSet)
open import Cubical.Data.Empty.Base  using (⊥; ⊥-elim)
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

lemma3 : (xs : ℂ) (ys : ℂ) (y : 𝔹)  → ¬ (xs ≡ xs ++ (ys ⌢ y))
lemma3 [] ys y p = ⊥-elim (lemma2 ys y (ys ⌢ y ≡⟨ sym (cong (λ - → - ⌢ y) (++-left-id ys)) ⟩ ([] ++ ys) ⌢ y ≡⟨ sym p ⟩ [] ∎))
lemma3 (xs ⌢ x) [] y p = ⊥-elim (lemma3 xs [] x (lemma xs (xs ⌢ x) x y p))
lemma3 (xs ⌢ x) (ys ⌢ y′) y p = ⊥-elim (lemma3 xs ys y′ (lemma xs (xs ++ (ys ⌢ y′)) x {!!} {!p!}))

[]-left-id : (xs : ℂ) → [] ++ xs ≡ xs
[]-left-id []       = refl
[]-left-id (xs ⌢ x) = cong (λ - → - ⌢ x) ([]-left-id xs)

assoc : (xs ys zs : ℂ) → xs ++ (ys ++ zs) ≡ (xs ++ ys) ++ zs
assoc xs ys []       = refl
assoc xs ys (zs ⌢ z) = cong (λ - → - ⌢ z) (assoc xs ys zs)

_≤_ : ℂ → ℂ → hProp ℓ-zero
xs ≤ ys = ∥ Σ[ zs ∈ ℂ ] xs ≡ ys ++ zs ∥ , ∥∥-prop _

cantor-poset : Poset ℓ-zero ℓ-zero
cantor-poset = ℂ , ((_≤_ , ℂ-set) , (≤-refl , ≤-trans , ≤-antisym))
  where
    ≤-refl : (xs : ℂ) → xs ≤ xs is-true
    ≤-refl xs = ∣ [] , refl ∣
    ≤-trans : (xs ys zs : ℂ) → xs ≤ ys is-true → ys ≤ zs is-true → xs ≤ zs is-true
    ≤-trans xs ys zs xs≤ys ys≤zs = ∥∥-rec (π₁ (xs ≤ zs)) (λ p → ∥∥-rec (π₁ (xs ≤ zs)) (λ q → NTS p q) ys≤zs) xs≤ys
      where
        NTS : Σ[ as ∈ ℂ ] xs ≡ ys ++ as → Σ[ bs ∈ ℂ ] ys ≡ zs ++ bs → xs ≤ zs is-true
        NTS (as , p) (bs , q) = ∣ (bs ++ as) , NTS′ ∣
          where
            NTS′ : xs ≡ (zs ++ (bs ++ as))
            NTS′ = xs ≡⟨ p ⟩ (ys ++ as) ≡⟨ cong (λ - → - ++ as) q ⟩ ((zs ++ bs) ++ as) ≡⟨ sym (assoc zs bs as) ⟩ (zs ++ (bs ++ as)) ∎
    ≤-antisym : (xs ys : ℂ) → xs ≤ ys is-true → ys ≤ xs is-true → xs ≡ ys
    ≤-antisym xs ys xs≤ys ys≤xs = ∥∥-rec (ℂ-set xs ys) (λ p → ∥∥-rec (ℂ-set xs ys) (λ q → NTS p q) ys≤xs) xs≤ys
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

cantor : FormalTopology ℓ-zero ℓ-zero
cantor = (cantor-poset , {!!} , {!!}) , {!!}
  where
    is : InteractionStr ℂ
    is = (λ _ → ℂ) , {!!} , {!!}
