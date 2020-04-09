{-# OPTIONS --cubical #-}

module Uniqueness where

open import Basis
open import UniversalProperty public
open import FormalTopology hiding (pos)
open import Family
open import Frame
open import PowFamEquivalence
open import Poset

g-unique : (F : FormalTopology ℓ₀ ℓ₀) (R : Frame (suc ℓ₀) ℓ₀ ℓ₀) (fm : P ─m→ pos R)
           (f-flat : IsFlat R fm) (rep : represents R fm)
         → let
             open MainProof R fm f-flat rep
             L  = ?
             ηm = ?
           in
            (y : Σ[ g′ ∈ (L ─f→ R) ] (_∘m_ {P = P} {Q = pos L} {R = pos R} (π₀ g′) ηm ≡ fm))
         → ((gm , g-frame-homo) , g∘η=f) ≡ y
g-unique F R fm@(f , f-mono) f-flat rep ((g′m , g′-frame-homo) , φ) = to-subtype-≡ _ _ I II
  where
    g′ = _$ₘ_ g′m
    L  = ?
    η  = ?
    ηm = ?
    open MainProof R fm f-flat rep hiding (f)

    NTS₀ : (y : Σ (∣ pos L ∣ₚ → ∣ pos R ∣ₚ) (IsMonotonic (pos L) (pos R))) → IsProp ((_∘m_ {P = P} {Q = pos L} {R = pos R} y ηm) ≡ fm)
    NTS₀ y = isOfHLevelΣ 2 (∏-set λ _ → carrier-is-set (pos R)) (λ h → prop⇒set (IsMonotonic-prop P (pos R) h)) (_∘m_ {P = P} {Q = pos L} {R = pos R} y ηm) fm

    I : (h : L ─f→ R) → IsProp (_∘m_ {P = P} {Q = pos L} {R = pos R} (π₀ h) ηm ≡ fm)
    I h = isOfHLevelΣ 2 (∏-set λ _ → carrier-is-set (pos R)) (λ h → prop⇒set (IsMonotonic-prop P (pos R) h)) (_∘m_ {P = P} {Q = pos L} {R = pos R} (π₀ h) ηm) fm

    g~g′ : (𝔘 : ∣ L ∣F) → g 𝔘 ≡ g′ 𝔘
    g~g′ 𝔘@((U , U-dc) , fixing) =
      _  ≡⟨ cong g (main-lemma 𝔘) ⟩
      _  ≡⟨ π₁ (π₁ g-frame-homo) (∃ U , (λ { (x , _) → η x })) ⟩
      _  ≡⟨ cong (λ - → ⋃[ R ] (∃ U , (λ { (x , _) → - x }))) g∘η=f′ ⟩
      _  ≡⟨ cong (λ - → ⋃[ R ] (∃ U , (λ { (x , _) → - x }))) (sym (subst (λ { (h , _) → h ≡ f }) (sym φ) refl)) ⟩
      _  ≡⟨ sym (π₁ (π₁ g′-frame-homo) (∃ U , λ { (x , _) → η x })) ⟩
      _  ≡⟨ {! final′!} ⟩
      _ ∎
      where
        final : 𝔘 ≡ ⋃[ L ] (η ⊚ ⟪ ⦅ 𝔘 ⦆ ⟫)
        final = main-lemma 𝔘
        final′ : g′ (⋃[ L ] (η ⊚ ⟪ ⦅ 𝔘 ⦆ ⟫)) ≡ g′ ((U , U-dc) , fixing)
        final′ = cong g′ (sym final)

    II : (gm , g-frame-homo) ≡ (g′m , g′-frame-homo)
    II = to-subtype-≡ _ _ (IsFrameHomomorphism-prop L R) (to-subtype-≡ _ _ (IsMonotonic-prop (pos L) (pos R)) (fn-ext _ _ g~g′))
