{-# OPTIONS --cubical --safe #-}

module FormalTopology where

open import Basis
open import Poset

InteractionStr : (A : Type ℓ) → Type (suc ℓ)
InteractionStr {ℓ = ℓ} A =
  Σ[ B ∈ (A → Type ℓ) ] Σ[ C ∈ ({x : A} → B x → Type ℓ) ]({x : A} → {y : B x} → C y → A)

InteractionSys : (ℓ : Level) → Type (suc ℓ)
InteractionSys ℓ = Σ (Type ℓ) InteractionStr

state       : InteractionSys ℓ → Type ℓ
action      : (D : InteractionSys ℓ) → state D → Type ℓ
reaction    : (D : InteractionSys ℓ) → {x : state D} → action D x → Type ℓ
δ           : (D : InteractionSys ℓ) {x : state D} {y : action D x}
            → reaction D y → state D

state    (A , _ , _ , _) = A
action   (_ , B , _ , _) = B
reaction (_ , _ , C , _) = C
δ        (_ , _ , _ , d) = d

HasMonotonicity : (P : Poset ℓ₀ ℓ₁) → InteractionStr ∣ P ∣ₚ → Type (ℓ₀ ⊔ ℓ₁)
HasMonotonicity P i =
  (a : state IS) (b : action IS a) (c : reaction IS b) → δ IS c ⊑[ P ] a is-true
  where
    IS : InteractionSys _
    IS = ∣ P ∣ₚ , i

Discipline : (ℓ₀ ℓ₁ : Level) → Type (suc ℓ₀ ⊔ suc ℓ₁)
Discipline ℓ₀ ℓ₁ =
  Σ[ P ∈ (Poset ℓ₀ ℓ₁) ] Σ[ IS ∈ (InteractionStr ∣ P ∣ₚ) ] HasMonotonicity P IS

pos : Discipline ℓ₀ ℓ₁ → Poset ℓ₀ ℓ₁
pos (P , _) = P

post : (D : Discipline ℓ₀ ℓ₁) → InteractionSys ℓ₀
post (P , P-disc , _) = ∣ P ∣ₚ , P-disc

module _ (D : Discipline ℓ₀ ℓ₁) where

  private
    P   = pos D
    str = π₀ (π₁ D)

  stage : Type ℓ₀
  stage = state (post D)

  exp : stage → Type ℓ₀
  exp = action (post D)

  outcome : {x : stage} → exp x → Type ℓ₀
  outcome = reaction (∣ P ∣ₚ , str)

  next : {a : stage} → {b : exp a} → outcome b → stage
  next = δ (post D)

  HasSimulation : Type (ℓ₀ ⊔ ℓ₁)
  HasSimulation =
    (a₀ a : ∣ P ∣ₚ) → a₀ ⊑[ pos D ] a is-true →
      (b : exp a) → Σ (exp a₀) (λ b₀ →
        (c₀ : outcome b₀) → Σ (outcome b) (λ c → next c₀ ⊑[ pos D ] next c is-true))

FormalTopology : (ℓ₀ ℓ₁ : Level) → Type (suc ℓ₀ ⊔ suc ℓ₁)
FormalTopology ℓ₀ ℓ₁ = Σ[ D ∈ (Discipline ℓ₀ ℓ₁) ] HasSimulation D
