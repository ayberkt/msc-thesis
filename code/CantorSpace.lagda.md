```
{-# OPTIONS --cubical --safe #-}

module CantorSpace where

open import Basis
open import Cubical.Core.Everything
open import Cubical.Relation.Nullary using (Discrete; yes; no; Dec; ¬_)
open import Cubical.Relation.Nullary.DecidableEq using (Discrete→isSet)
open import Cubical.Data.Empty.Base  using (⊥; ⊥-elim)
open import Cubical.Data.Unit.Base   using (Unit; tt)
open import Cubical.Data.Bool.Base   using (true; false; _≟_) renaming (Bool to 𝔹)
open import Truncation
open import Poset
open import FormalTopology
open import SnocList 𝔹  _≟_ renaming (SnocList to ℂ; SnocList-set to ℂ-set)

_≤_ : ℂ → ℂ → hProp ℓ-zero
xs ≤ ys = (Σ[ zs ∈ ℂ ] xs ≡ ys ++ zs) , prop
  where
    prop : IsProp (Σ[ zs ∈ ℂ ] xs ≡ ys ++ zs)
    prop xs≤ys@(_ , p) xs≤ys′@(_ , q) =
      to-subtype-≡ xs≤ys xs≤ys′ (λ ws → ℂ-set xs (ys ++ ws)) (++-lemma p q)

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
            NTS′ : xs ≡ zs ++ (bs ++ as)
            NTS′ = xs               ≡⟨ p                      ⟩
                   ys ++ as         ≡⟨ cong (λ - → - ++ as) q ⟩
                   (zs ++ bs) ++ as ≡⟨ sym (assoc zs bs as)   ⟩
                   zs ++ (bs ++ as) ∎
    ≤-antisym : (xs ys : ℂ) → xs ≤ ys is-true → ys ≤ xs is-true → xs ≡ ys
    ≤-antisym xs ys xs≤ys ys≤xs = NTS xs≤ys ys≤xs
      where
        NTS : Σ[ as ∈ ℂ ] xs ≡ ys ++ as → Σ[ bs ∈ ℂ ] ys ≡ xs ++ bs → xs ≡ ys
        NTS ([] , p) ([] , q) = p
        NTS ([] , p) (bs ⌢ x , q) = p
        NTS (as ⌢ x , p) ([] , q) = sym q
        NTS (as ⌢ a , p) (bs ⌢ b  , q) = ⊥-elim (lemma3 NTS′)
          where
            NTS′ : xs ≡ xs ++ ((bs ⌢ b) ++ (as ⌢ a))
            NTS′ = xs                           ≡⟨ p                                ⟩
                   ys ++ (as ⌢ a)               ≡⟨ cong (λ - → - ++ (as ⌢ a)) q     ⟩
                   (xs ++ (bs ⌢ b)) ++ (as ⌢ a) ≡⟨ sym (assoc xs (bs ⌢ b) (as ⌢ a)) ⟩
                   xs ++ ((bs ⌢ b) ++ (as ⌢ a)) ∎

cantor : FormalTopology ℓ-zero ℓ-zero
cantor = (cantor-poset , is , mono) , sim
  where
    is : InteractionStr ℂ
    is = (λ _ → Unit) , (λ _ → 𝔹) , λ {x = xs} b → xs ⌢ b

    mono : HasMonotonicity cantor-poset is
    mono _ _ c = [] ⌢ c , refl

    sim : HasSimulation (cantor-poset , is , mono)
    sim xs ys xs≤ys@([] , p)     tt = tt , λ c₀ → c₀ , [] , cong (λ - → - ⌢ c₀) p
    sim xs ys xs≤ys@(zs ⌢ z , p) tt = tt , NTS
      where
        NTS : (c₀ : 𝔹) → Σ[ c ∈ 𝔹 ] (xs ⌢ c₀) ≤ (ys ⌢ c) is-true
        NTS c₀ =
          head (zs ⌢ z) tt , subst (λ - → (- ⌢ c₀) ≤ _ is-true) (sym p) NTS′
          where
            φ    = cong (λ - → ys ++ (- ⌢ c₀)) (sym (hd-tl-lemma (zs ⌢ z) tt))
            ψ    = cong (λ - → - ⌢ c₀) (sym (snoc-lemma ys _ _))
            rem  = (ys ++ zs) ⌢ z ⌢ c₀                                          ≡⟨ φ ⟩
                   (ys ++ (([] ⌢ head (zs ⌢ z) tt) ++ (tail (zs ⌢ z) tt))) ⌢ c₀ ≡⟨ ψ ⟩
                   ((ys ⌢ head (zs ⌢ z) tt) ++ tail (zs ⌢ z) tt) ⌢ c₀ ∎
            NTS′ : ((ys ++ zs) ⌢ z ⌢ c₀) ≤ (ys ⌢ head (zs ⌢ z) tt) is-true
            NTS′ = ((tail (zs ⌢ z) tt) ⌢ c₀) , rem

-- --}
-- --}
-- --}
```
