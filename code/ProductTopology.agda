{-# OPTIONS --cubical --safe #-}

module ProductTopology where

open import Basis
open import Data.Sum
open import Poset
open import FormalTopology

module _ (𝔉 𝔊 : FormalTopology ℓ₀ ℓ₀) where
  D     = π₀ 𝔉
  E     = π₀ 𝔊
  monoF = π₁ (π₁ D)
  simF  = π₁ 𝔉
  monoG = π₁ (π₁ E)
  simG  = π₁ 𝔊
  P     = pos D
  Q     = pos E

  𝔉×𝔊 : FormalTopology ℓ₀ ℓ₀
  𝔉×𝔊 = (P ×ₚ Q , (×-exp , ×-out ,  λ {a} {b} c → ×-next {b = b} c) , mono) , sim
    where
      ×-exp : ∣ P ×ₚ Q ∣ₚ → Type ℓ₀
      ×-exp (a₀ , a₁) = exp D a₀ ⊎ exp E a₁

      ×-out : {a : ∣ P ×ₚ Q ∣ₚ} → ×-exp a → Type ℓ₀
      ×-out (inj₁ b) = outcome D b
      ×-out (inj₂ b) = outcome E b

      ×-next : {a : ∣ P ×ₚ Q ∣ₚ} {b : ×-exp a} → ×-out {a = a} b → ∣ P ×ₚ Q ∣ₚ
      ×-next {a = (a₀ , a₁)} {b = inj₁ b} c = (next D c) , a₁
      ×-next {a = (a₀ , a₁)} {b = inj₂ b} c = a₀         , (next E c)

      IS : InteractionStr ∣ P ×ₚ Q ∣ₚ
      IS = ×-exp , ×-out , λ {a} {b} c → ×-next {b = b} c

      mono : HasMonotonicity (P ×ₚ Q) IS
      mono (a₀ , a₁) (inj₁ b) c = (monoF a₀ b c)   , ⊑[ Q ]-refl a₁
      mono (a₀ , a₁) (inj₂ b) c = (⊑[ P ]-refl a₀) , monoG a₁ b c

      sim : HasSimulation (P ×ₚ Q , IS , mono)
      sim (a₀ , a₁) (a , a′) (a₀⊑a , a₁⊑a′) b with b
      ... | inj₁ b₀ = let (b₀ , p) = simF _ _ a₀⊑a b₀
                      in inj₁ b₀ , λ c₀ → π₀ (p c₀) , π₁ (p c₀) , a₁⊑a′
      ... | inj₂ b₁ = let (b₁ , p) = simG _ _ a₁⊑a′ b₁
                      in inj₂ b₁ , λ c₁ → π₀ (p c₁) , a₀⊑a , π₁ (p c₁)
