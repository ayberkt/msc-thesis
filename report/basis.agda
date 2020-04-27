{-# OPTIONS --cubical #-}

open import Cubical.Core.Everything         public using    ( _≡_
                                                            ; Type
                                                            ; Σ
                                                            ; Σ-syntax
                                                            ; _,_
                                                            ; _≃_
                                                            ; equivFun
                                                            ; isEquiv
                                                            ; equivProof
                                                            )
open import Cubical.Data.Prod               public using    (_,_; proj₁; proj₂)
                                                   renaming (_×_ to _××_)
open import Cubical.Data.Sigma.Properties   public using    ( Σ≡)
open import Cubical.Foundations.Prelude     public using    ( J
                                                            ; subst
                                                            ; isProp
                                                            ; cong; refl; sym
                                                            ; _≡⟨_⟩_; _∎
                                                            ; transport
                                                            ; transportRefl
                                                            ; isContr)
                                                   renaming ( isSet        to IsSet
                                                            ; isProp→isSet to prop⇒set )
open import Cubical.Foundations.Transport   public using    ( transportEquiv )
open import Cubical.Foundations.Equiv       public using    ( idEquiv; invEquiv; secEq; retEq; fiber)
open import Cubical.Foundations.SIP         public using    ( SNS; SNS'; join-SNS'
                                                            ; SNS''
                                                            ; SNS'''
                                                            ; SNS'≡SNS''
                                                            ; SNS→SNS'
                                                            ; SNS''→SNS'''
                                                            ; add-to-structure
                                                            ; add-to-iso
                                                            ; add-axioms-SNS'
                                                            ; pointed-structure
                                                            ; Pointed-Type
                                                            ; pointed-iso
                                                            ; pointed-is-SNS'
                                                            ; sip
                                                            ; SIP
                                                            ; _≃[_]_)
open import Cubical.Foundations.Univalence  public using    ( ua )
open import Cubical.Foundations.HLevels     public using    ( hProp
                                                            ; isSetHProp
                                                            ; isPropIsSet
                                                            ; isOfHLevelΣ
                                                            ; ΣProp≡
                                                            ; hLevelSuc )
open import Cubical.Data.Sigma              public using    ( sigmaPath→pathSigma
                                                            ; pathSigma→sigmaPath )
open import Cubical.Foundations.Isomorphism public using    ( isoToPath; iso; section; retract)
open import Cubical.Foundations.Logic       public using    ( _⇔_; _⇒_; ⇔toPath )
                                                   renaming ( _⊓_ to _∧_)
open import Data.Product                    public using    ( _×_; uncurry)
                                                   renaming ( proj₁ to π₀
                                                            ; proj₂ to π₁)
open import Function                        public using    (_∘_; id)
open import Level                           public

variable
  ℓ ℓ′ ℓ₀ ℓ₁ : Level

fn-ext : {A : Type ℓ₀} {B : A → Type ℓ₁}
        → (f g : (x : A) → B x) → ((x : A) → f x ≡ g x) → f ≡ g
fn-ext f g f~g i x = f~g x i

_is-true : hProp ℓ → Type ℓ
(P , _) is-true = P

is-true-prop : (P : hProp ℓ) → isProp (P is-true)
is-true-prop (P , P-prop) = P-prop

infix 5 _is-true

∏-prop : {A : Type ℓ₀} {B : A → Type ℓ₁}
       → ((x : A) → isProp (B x)) → isProp ((x : A) → B x)
∏-prop B-prop x y = fn-ext x y λ x′ → B-prop x′ (x x′) (y x′)
