{-# OPTIONS --cubical --safe #-}

module Misc where

open import Basis
open import Cubical.Foundations.Equiv using (_≃⟨_⟩_; _■)

foo : {P Q : hProp ℓ} →  [ P ⇔ Q ] ≃ ([ P ] ≃ [ Q ])
foo {P = P} {Q = Q} = isoToEquiv (iso f g sec-f-g ret-f-g)
  where
    f : [ P ⇔ Q ] → [ P ] ≃ [ Q ]
    f (f , g) = isoToEquiv (iso f g (λ x → π₁ Q (f (g x)) x) λ x → π₁ P (g (f x)) x)

    g : [ P ] ≃ [ Q ] → [ P ⇔ Q ]
    g e = Iso.fun (equivToIso e) , Iso.inv (equivToIso e)

    sec-f-g : section f g
    sec-f-g (f , f-equiv) = ΣProp≡ isPropIsEquiv refl

    ret-f-g : retract f g
    ret-f-g (f , g) = refl

Iso′ : (A : Type ℓ) (B : Type ℓ′) → Type (ℓ ⊔ ℓ′)
Iso′ A B = Σ[ f ∈ (A → B) ] Σ[ g ∈ (B → A) ] section f g × retract f g

Iso≃Iso′ : (A : Type ℓ) (B : Type ℓ′) → (Iso A B) ≃ (Iso′ A B)
Iso≃Iso′ A B = isoToEquiv (iso to from sec-to-from ret-to-from)
  where
    to : Iso A B → Iso′ A B
    to (iso fun inv rightInv leftInv) = fun , inv , rightInv , leftInv

    from : Iso′ A B → Iso A B
    from (f , g , sec , ret) = iso f g sec ret

    sec-to-from : section to from
    sec-to-from _ = refl

    ret-to-from : retract to from
    ret-to-from _ = refl

bar : (A B : Type ℓ) → isSet A → isSet B → (Iso A B) ≃ (A ≃ B)
bar A B A-set B-set = isoToEquiv (equivToIso (Iso A B ≃⟨ Iso≃Iso′ A B ⟩ Iso′ A B ≃⟨ isoToEquiv (iso to from sec-to-from ret-to-from) ⟩ A ≃ B ■))
  where
    to : Iso′ A B → A ≃ B
    to (f , g , sec-f-g , leftInv) = isoToEquiv (iso f g sec-f-g leftInv)

    from : A ≃ B → Iso′ A B
    from e = π₀ (Iso≃Iso′ A B) (equivToIso e)

    sec-to-from : section to from
    sec-to-from _ = ΣProp≡ isPropIsEquiv refl

    ret-to-from : retract to from
    ret-to-from is =
     ΣProp≡ (λ f → λ { (g , (sec-f-g , ret-f-g)) (g′ , (sec-f-g′ , ret-f-g′)) →
     ΣProp≡ (λ g₀ → isPropΣ (λ h₀ h₁ → funExt (λ b → B-set (f (g₀ b)) b (h₀ b) (h₁ b))) λ h₀ h₁ →
            λ ret → funExt (λ x → A-set (g₀ (f x)) x (h₁ x) (ret x))) (funExt λ x → subst (λ - → g - ≡ g′ -) (sec-f-g x) (g (f (g x)) ≡⟨ ret-f-g (g x) ⟩ g x ≡⟨  sym (ret-f-g′ (g x)) ⟩ g′ (f (g x)) ∎)) }) refl
