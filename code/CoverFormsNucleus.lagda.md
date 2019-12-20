```
{-# OPTIONS --cubical --safe #-}

open import Basis
open import Poset
open import Frame
open import HITCoverage

module CoverFormsNucleus (F : ) where
```

Let us start by defining the frame formed by the downward-closed subsets of `P`.

```
  F↓ = downward-subset-frame P
```

```
  cover : ∣ F↓ ∣F → ∣ F↓ ∣F
  cover (U , U-down) = {!!}
```
