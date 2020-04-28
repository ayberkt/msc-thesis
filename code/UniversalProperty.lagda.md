```
{-# OPTIONS --cubical --safe #-}

module UniversalProperty where

open import Basis
open import Frame
open import Poset
open import Powerset
open import Family
open import Truncation
open import FormalTopology hiding (pos)
open import CoverFormsNucleus

compr : {X : Type ℓ₀} {Y : Type ℓ₁} → (g : X → Y) → 𝒫 X → Sub ℓ₀ Y
compr g U = (index ⟪ U ⟫) , g ∘ (_$_ ⟪ U ⟫)

syntax compr (λ x → e) ℱ = ⁅ e ∣ x ∈ ℱ ⁆

module _ (F : FormalTopology ℓ₀ ℓ₀) where

  D       = π₀ F
  P       = π₀ (π₀ F)
  𝔉       = ∣ P ∣ₚ
  F↓      = downward-subset-frame P
  P↓      = pos F↓
  sim     = π₁ F
  mono    = π₁ D
  _⊑_     = λ (x y : stage D) → x ⊑[ P ] y

  open NucleusFrom F
```

## Representation

```
  represents : (R : Frame (suc ℓ₀) ℓ₀ ℓ₀) → (m : P ─m→ pos R) → Type ℓ₀
  represents R (f , _) =
    (x : 𝔉) (y : exp D x) →
      [ f x ⊑[ pos R ] (⋃[ R ] (outcome D y , λ u → f (next D u))) ]
```

## Flatness

```
  _↓_↓ : 𝔉 → 𝔉 → 𝒫 𝔉
  _↓_↓ a b = λ - → - ⊑[ P ] a ⊓ - ⊑[ P ] b

  IsFlat : (F : Frame (suc ℓ₀) ℓ₀ ℓ₀) → (m : P ─m→ pos F) → Type (suc ℓ₀)
  IsFlat F (f , _) = (𝟏[ F ] ≡ ⋃[ F ] (𝔉 , f))
                   × ((a b : 𝔉) → f a ⊓[ F ] f b ≡ ⋃[ F ] (f ⟨$⟩ ⟪ a ↓ b ↓ ⟫))
```

## The universal property

Statement.

```
  universal-prop : Type (suc (suc ℓ₀))
  universal-prop =
    (R : Frame (suc ℓ₀) ℓ₀ ℓ₀) (f : P ─m→ pos R) → IsFlat R f → represents R f →
      isContr (Σ[ g ∈ (L ─f→ R) ] (_∘m_ {P = P} {Q = pos L} {R = pos R} (π₀ g) ηm) ≡ f)
```

Before the proof we will need some lemmas.

```
  cover+ : {x y : 𝔉} ((U , _) : ∣ F↓ ∣F) → [ x ∈ ⦅ η y ⦆ ] → [ y ∈ U ] → x <| U
  cover+ {y = y} (_ , U-dc) x∈ηy y∈U = lem4 _ _ (λ z z⊑y → dir (U-dc y z y∈U z⊑y)) _ x∈ηy
```

```
  main-lemma : (𝔘 : ∣ L ∣F) → 𝔘 ≡ ⋃[ L ] ⁅ η u ∣ u ∈ ⦅ 𝔘 ⦆ ⁆
  main-lemma 𝔘@((U , U-dc) , U-fix) = ⊑[ pos L ]-antisym _ _ down up
    where
      down : [ 𝔘 ⊑[ pos L ] (⋃[ L ] ⁅ η x ∣ x ∈ U ⁆) ]
      down x xεU = dir ∣ (x , xεU) , dir (⊑[ P ]-refl x) ∣

      up : [ (⋃[ L ] ⁅ η x ∣ x ∈ U ⁆) ⊑[ pos L ] 𝔘 ]
      up x (dir xε⋁) = ∥∥-rec (is-true-prop (U x)) NTS xε⋁
        where
          NTS : Σ[ y ∈ _ ] [ x ∈ ⦅ η (π₀ y) ⦆ ] → [ x ∈ U ]
          NTS ((y , yεU) , x◀y↓) =
            subst (λ V → [ π₀ V x ]) U-fix  (cover+ (U , U-dc) x◀y↓ yεU)
      up x (branch b f) = subst (λ V → [ π₀ V x ]) U-fix (branch b (dir ∘ IH))
        where
          IH : (c : outcome D b) → [ next D c ∈ U ]
          IH c = up (next D c) (f c)
      up x (squash x◀⋁₀ x◀⋁₁ i) = is-true-prop (U x) (up x x◀⋁₀) (up x x◀⋁₁) i
```

Proof.

```
  module MainProof (R      : Frame (suc ℓ₀) ℓ₀ ℓ₀)
                   (fm     : P ─m→ pos R)
                   (f-flat : IsFlat R fm)
                   (rep    : represents R fm) where
    f      = _$ₘ_ fm
    f-mono = π₁ fm
```

```
    g : ∣ L ∣F → ∣ R ∣F
    g 𝔘 = ⋃[ R ] (f ⟨$⟩ ⟪ ⦅ 𝔘 ⦆ ⟫)
```

```
    g-mono : IsMonotonic (pos L) (pos R) g
    g-mono ((U , _) , _) ((V , _) , _) U⊆V =
      ⋃[ R ]-least _ _ (λ o oεfU → ⋃[ R ]-upper _ _ (NTS o oεfU ))
      where
        NTS : (x : ∣ R ∣F) → x ε (∃ U , f ∘ π₀) → x ε (∃ V , f ∘ π₀)
        NTS x ((x′ , x′εfU) , fUεi=x) = (x′ , U⊆V x′ x′εfU) , fUεi=x

    gm : pos L ─m→ pos R
    gm = g , g-mono
```

### `g` respects the top element

```
    g-resp-𝟏 : g 𝟏[ L ] ≡ 𝟏[ R ]
    g-resp-𝟏 = g 𝟏[ L ]                          ≡⟨ refl             ⟩
               ⋃[ R ] (f ⟨$⟩ (∃ ⦅ 𝟏[ L ] ⦆ , π₀))  ≡⟨ family-iff R NTS ⟩
               ⋃[ R ] (𝔉 , f)                    ≡⟨ sym (π₀ f-flat)  ⟩
               𝟏[ R ]                            ∎
      where
        NTS : (x : ∣ R ∣F)
            → (x ε (f ⟨$⟩ (∃ ⦅ 𝟏[ L ] ⦆ , π₀)) → x ε (𝔉 , f))
            × (x ε (𝔉 , f) → x ε (f ⟨$⟩ (∃ ⦅ 𝟏[ L ] ⦆ , π₀)))
        NTS x = (λ { ((y , _) , eq) → y , eq }) , (λ { (y , eq) → (y , tt) , eq })
```

### `g` respects the binary meets

```
    g-resp-⊓ : (𝔘 𝔙 : ∣ L ∣F) → g (𝔘 ⊓[ L ] 𝔙) ≡ g 𝔘 ⊓[ R ] g 𝔙
    g-resp-⊓ 𝔘 𝔙 =
      g (𝔘 ⊓[ L ] 𝔙)
        ≡⟨ refl ⟩
      ⋃[ R ] ⁅ f a ∣ a ∈ ⦅ 𝔘 ⊓[ L ] 𝔙 ⦆ ⁆
        ≡⟨ I ⟩
      ⋃[ R ] ((∃ ⦅ 𝔘 ⦆ × ∃ ⦅ 𝔙 ⦆) , λ { ((u , _) , v , _) → ⋃[ R ] (f ⟨$⟩ ⟪ u ↓ v ↓ ⟫) })
        ≡⟨ cong (λ - → (⋃[ R ] ((∃ ⦅ 𝔘 ⦆ × ∃ ⦅ 𝔙 ⦆) , -))) II ⟩
      ⋃[ R ] (((∃ ⦅ 𝔘 ⦆) × (∃ ⦅ 𝔙 ⦆)) , λ { ((u , _) , (v , _)) → f u ⊓[ R ] f v })
        ≡⟨ sym (sym-distr R (⁅ f u ∣ u ∈ ⦅ 𝔘 ⦆ ⁆) (⁅ f v ∣ v ∈ ⦅ 𝔙 ⦆ ⁆)) ⟩
      (⋃[ R ] ⁅ f u ∣ u ∈ ⦅ 𝔘 ⦆ ⁆) ⊓[ R ] (⋃[ R ] ⁅ f v ∣ v ∈ ⦅ 𝔙 ⦆ ⁆)
        ≡⟨ refl ⟩
      g 𝔘 ⊓[ R ] g 𝔙
        ∎
      where
        II : (λ { ((u , _) , (v , _)) → ⋃[ R ] (f ⟨$⟩ ⟪ u ↓ v ↓ ⟫) })
           ≡ (λ { ((u , _) , (v , _)) → (f u) ⊓[ R ] (f v) })
        II = sym (funExt λ { ((u , _) , (v , _)) → π₁ f-flat u v })
        I  : _
        I  = ⊑[ pos R ]-antisym _ _ down up
          where
            down : _
            down = ⋃[ R ]-least _ _ isUB
              where
                isUB : _
                isUB o ((i , (a , b)) , eq) =
                  ⋃[ R ]-upper _ _ (((i , a) , (i , b)) , subst (λ o′ → _ ≡ o′) eq φ)
                  where
                    down′ : [ (⋃[ R ] (f ⟨$⟩ ⟪ i ↓ i ↓ ⟫)) ⊑[ pos R ] f i ]
                    down′ =
                      ⋃[ R ]-least _ _ λ { z ((_ , (k , _)) , eq′) →
                        subst (λ - → [ - ⊑[ pos R ] _ ]) eq′ (f-mono _ _ k) }
                    up′ : [ f i ⊑[ pos R ] (⋃[ R ] (f ⟨$⟩ ⟪ i ↓ i ↓ ⟫)) ]
                    up′ = ⋃[ R ]-upper _ _ ((i , (⊑[ P ]-refl i , ⊑[ P ]-refl i)) , refl)
                    φ : ⋃[ R ] (f ⟨$⟩ ⟪ i ↓ i ↓ ⟫) ≡ f i
                    φ = ⊑[ pos R ]-antisym _ _ down′ up′
            up : _
            up = ⋃[ R ]-least _ _ isUB
              where
                isUB :  _
                isUB o (i@((x , xε𝔙) , (y , yε𝔘)) , eq) =
                  subst (λ o′ → [ o′ ⊑[ pos R ] _ ]) eq (⋃[ R ]-least _ _ NTS)
                  where
                    NTS : _
                    NTS w (j@(z , (z⊑x , z⊑y)) , eq′) = ⋃[ R ]-upper _ _ ((z , φ) ,  eq′)
                      where
                        φ : [ z ∈ (⦅ 𝔘 ⦆ ∩ ⦅ 𝔙 ⦆) ]
                        φ = (π₁ (π₀ 𝔘) x z xε𝔙 z⊑x) , (π₁ (π₀ 𝔙) y z yε𝔘 z⊑y)
```

### `g` respects the joins

```
    g-resp-⊔ : (ℱ : Sub ℓ₀ ∣ L ∣F) → g (⋃[ L ] ℱ) ≡ ⋃[ R ] (g ⟨$⟩ ℱ)
    g-resp-⊔ ℱ@(I , U) =
      ⋃[ R ] ⁅ f a ∣ a ∈ ⦅ ⋃[ L ] ℱ ⦆ ⁆
        ≡⟨ ⊑[ pos R ]-antisym _ _ down up ⟩
        ⋃[ R ] ((Σ[ i ∈ I ] ∃ ⦅ U i ⦆) , λ { (_ , y) → f (π₀ y) })
        ≡⟨ flatten R I (λ - → ∃ ⦅ U - ⦆) (λ _ j → f (π₀ j))   ⟩
      ⋃[ R ] (g ⟨$⟩ ℱ)
        ∎
      where
        LHS = ⋃[ R ] ⁅ f a ∣ a ∈ ⦅ ⋃[ L ] ℱ ⦆ ⁆
        RHS = ⋃[ R ] (Σ I (λ - → ∃ ⦅ U - ⦆) , λ { (x , y) → f (π₀ y) })

        down : [ LHS ⊑[ pos R ] RHS ]
        down = ⋃[ R ]-least _ _ ψ
          where
            ψ : (o : ∣ R ∣F) → o ε ⁅ f a ∣ a ∈ ⦅ ⋃[ L ] ℱ ⦆ ⁆ → [ o ⊑[ pos R ] RHS ]
            ψ o ((x , foo) , eq) = subst (λ - → [ - ⊑[ pos R ] RHS ]) eq (ϑ x foo)
              where
                open PosetReasoning (pos R) using (_⊑⟨_⟩_; _■)
                ϑ : (y : 𝔉) → [ y ∈ ⦅ ⋃[ L ] ℱ ⦆ ] → [ f y ⊑[ pos R ] RHS ]
                ϑ y (dir mem) = ∥∥-rec
                                  (is-true-prop (f y ⊑[ pos R ] RHS))
                                  (λ { (j , cov) →
                                         ⋃[ R ]-upper _ _ ((j , y , cov) , refl) }) mem
                ϑ y (branch b h) =
                  f y                               ⊑⟨ rep y b            ⟩
                  ⋃[ R ] (outcome D b , f ∘ next D) ⊑⟨ ⋃[ R ]-least _ _ ζ ⟩
                  RHS                               ■
                  where
                    ζ : (r : ∣ R ∣F)
                      → r ε (outcome D b , f ∘ next D)
                      → [ r ⊑[ pos R ] RHS ]
                    ζ r (c , eq-r) =
                      subst (λ - → [ - ⊑[ pos R ] RHS ]) eq-r (ϑ (next D c) (h c))
                ϑ y (squash φ ψ i) = is-true-prop (f y ⊑[ pos R ] RHS) (ϑ y φ) (ϑ y ψ) i

        up : [ RHS ⊑[ pos R ] LHS ]
        up = ⋃[ R ]-least _ _ λ { r ((i , (x , xεU)) , eq) →
               ⋃[ R ]-upper _ _ ((x , dir ∣ i , xεU ∣) , eq) }
```

### `g` is a frame homomorphism

```
    g-frame-homo : isFrameHomomorphism L R gm
    g-frame-homo = g-resp-𝟏 , (g-resp-⊓ , g-resp-⊔)
```

### `g` makes the diagram commute

```
    lem : (a a′ : 𝔉) → a′ <| π₀ (↓-clos a) → [ f a′ ⊑[ pos R ] f a ]
    lem a a′ (squash p q i) = is-true-prop (f a′ ⊑[ pos R ] f a) (lem _ _ p) (lem _ _ q) i
    lem a a′ (dir    a′⊑a)  = f-mono a′ a a′⊑a
    lem a a′ (branch b h)   =
      f a′                              ⊑⟨ rep a′ b              ⟩
      ⋃[ R ] (outcome D b , f ∘ next D) ⊑⟨ ⋃[ R ]-least _ _ isUB ⟩
      f a                               ■
      where
        open PosetReasoning (pos R) using (_⊑⟨_⟩_; _■)
        isUB : ∀ a₀ → a₀ ε (outcome D b , f ∘ next D) → [ a₀ ⊑[ pos R ] f a ]
        isUB a₀ (c , p) = a₀           ⊑⟨ ≡⇒⊑ (pos R) (sym p)    ⟩
                          f (next D c) ⊑⟨ lem a (next D c) (h c) ⟩
                          f a          ■

    gm∘ηm = _∘m_ {P = P} {Q = pos L} {R = pos R} gm ηm

    gm∘ηm~f : (x : 𝔉) → gm $ₘ (ηm $ₘ x) ≡ fm $ₘ x
    gm∘ηm~f x = ⊑[ pos R ]-antisym _ _ down (⋃[ R ]-upper _ _ ((x , x◀x↓ x) , refl))
      where
        down : [ (⋃[ R ] (∃ π₀ (e x) , f ∘ π₀)) ⊑[ pos R ] f x ]
        down = ⋃[ R ]-least _ _ λ { o ((y , φ) , eq) → subst (λ _ → _) eq (lem x y φ) }

    g∘η=f : gm∘ηm ≡ fm
    g∘η=f = ΣProp≡ (IsMonotonic-prop P (pos R)) (funExt gm∘ηm~f)

    g∘η=f′ : g ∘ η ≡ f
    g∘η=f′ = subst (λ { (h , _) → h ≡ f }) (sym g∘η=f) refl
```

### `g` is uniquely determined

```
    g-unique : (y : Σ[ g′ ∈ (L ─f→ R) ]
                     (_∘m_ {P = P} {Q = pos L} {R = pos R} (π₀ g′) ηm ≡ fm))
            → ((gm , g-frame-homo) , g∘η=f) ≡ y
    g-unique ((g′m , g′-frame-homo) , φ) = ΣProp≡ I II
      where
        g′ = _$ₘ_ g′m

        f=g′∘η : f ≡ g′ ∘ η
        f=g′∘η = subst (λ { (f′ , _) → f′ ≡ g′ ∘ η }) φ refl

        NTS₀ : (y : Σ (∣ pos L ∣ₚ → ∣ pos R ∣ₚ) (IsMonotonic (pos L) (pos R)))
             → isProp ((_∘m_ {P = P} {Q = pos L} {R = pos R} y ηm) ≡ fm)
        NTS₀ y = isOfHLevelΣ 2
                   (isSetΠ λ _ → carrier-is-set (pos R))
                   (λ h → isProp→isSet (IsMonotonic-prop P (pos R) h))
                   (_∘m_ {P = P} {Q = pos L} {R = pos R} y ηm) fm

        I : (h : L ─f→ R) → isProp (_∘m_ {P = P} {Q = pos L} {R = pos R} (π₀ h) ηm ≡ fm)
        I h = isOfHLevelΣ 2
                (isSetΠ λ _ → carrier-is-set (pos R))
                (λ h → isProp→isSet (IsMonotonic-prop P (pos R) h))
                (_∘m_ {P = P} {Q = pos L} {R = pos R} (π₀ h) ηm) fm

        g~g′ : (𝔘 : ∣ L ∣F) → g 𝔘 ≡ g′ 𝔘
        g~g′ 𝔘 =
          g 𝔘                            ≡⟨ refl                                       ⟩
          ⋃[ R ] ⁅ f u ∣ u ∈ ⦅ 𝔘 ⦆ ⁆     ≡⟨ cong g (main-lemma 𝔘)                      ⟩
          g (⋃[ L ] ⁅ η u ∣ u ∈ ⦅ 𝔘 ⦆ ⁆) ≡⟨ π₁ (π₁ g-frame-homo) (η ⟨$⟩ ⟪ ⦅ 𝔘 ⦆ ⟫)       ⟩
          ⋃[ R ] ⁅ g (η u) ∣ u ∈ ⦅ 𝔘 ⦆ ⁆ ≡⟨ cong (λ - → ⋃[ R ] (- ⟨$⟩ ⟪ ⦅ 𝔘 ⦆ ⟫)) g∘η=f′ ⟩
          ⋃[ R ] ⁅ f u     ∣ u ∈ ⦅ 𝔘 ⦆ ⁆ ≡⟨ eq₀                                        ⟩
          ⋃[ R ] ((g′ ∘ η) ⟨$⟩ ⟪ ⦅ 𝔘 ⦆ ⟫)  ≡⟨ eq₁                                        ⟩
          g′ (⋃[ L ] (η ⟨$⟩ ⟪ ⦅ 𝔘 ⦆ ⟫))    ≡⟨ eq₂                                        ⟩
          g′ 𝔘 ∎
          where
            eq₀ : ⋃[ R ] (f ⟨$⟩ ⟪ ⦅ 𝔘 ⦆ ⟫) ≡ ⋃[ R ] ((g′ ∘ η) ⟨$⟩ ⟪ ⦅ 𝔘 ⦆ ⟫)
            eq₀ = cong (λ - → ⋃[ R ] (- ⟨$⟩ ⟪ ⦅ 𝔘 ⦆ ⟫)) f=g′∘η
            eq₁ : ⋃[ R ] ((g′ ∘ η) ⟨$⟩ ⟪ ⦅ 𝔘 ⦆ ⟫) ≡ g′ (⋃[ L ] (η ⟨$⟩ ⟪ ⦅ 𝔘 ⦆ ⟫))
            eq₁ = sym (π₁ (π₁ g′-frame-homo) (η ⟨$⟩ ⟪ ⦅ 𝔘 ⦆ ⟫))
            eq₂ : g′ (⋃[ L ] ((η ⟨$⟩ ⟪ ⦅ 𝔘 ⦆ ⟫))) ≡ g′ 𝔘
            eq₂ = cong g′ (sym (main-lemma 𝔘))

        II : (gm , g-frame-homo) ≡ (g′m , g′-frame-homo)
        II = ΣProp≡
               (isFrameHomomorphism-prop L R)
               (ΣProp≡ (IsMonotonic-prop (pos L) (pos R)) (funExt g~g′))
```

### The final proof

```
  main : universal-prop
  main R fm@(f , f-mono) f-flat rep =
    (((g , g-mono) , g-resp-𝟏 , g-resp-⊓ , g-resp-⊔) , g∘η=f) , g-unique
    where
      open MainProof R fm f-flat rep
```
