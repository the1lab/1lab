<!--
```agda
open import 1Lab.Prelude

open import Data.Partial.Total
open import Data.Partial.Base
open import Data.Vec.Base

open import Realisability.PCA

import Realisability.Data.Pair
import Realisability.PCA.Sugar
```
-->

```agda
module Realisability.PCA.Fixpoint {ℓ} (𝔸 : PCA ℓ) where
```

<!--
```agda
open Realisability.PCA.Sugar 𝔸
open Realisability.Data.Pair 𝔸

private variable x y : ↯ ⌞ 𝔸 ⌟
```
-->

# Fixed-point combinators in a PCA

Since [[partial combinatory algebras]] encode untyped higher-order
computation, we can import the definition of **fixed-point combinators**
from untyped lambda calculus to arbitrary [[programs in a PCA]]. The
most useful of these will be the `` `Z ``{.Agda} combinator, which
satisfies
$$
\tt{Z}\, \sf{f}\, \sf{a} = \sf{f}\, (\tt{Z}\, \sf{f})\, \sf{a}
$$,
and is always defined when applied to a single argument --- that is, it
lets us compute 'functions of at least one argument' by arbitrary
recursion, such that *the recursive function itself* is always defined
--- though of course *applying* the recursive function might still lead
to something undefined.

We introduce an intermediate combinator `` `X ``{.Agda}, and define
`` `Z ``{.Agda} as the self-application of `` `X ``{.Agda}.

```agda
`X : ↯⁺ 𝔸
`X = val ⟨ x ⟩ ⟨ y ⟩ ⟨ z ⟩ y `· (x `· x `· y) `· z

`Z : ↯⁺ 𝔸
`Z = record
  { fst = `X ⋆ `X
  ; snd = subst ⌞_⌟ (sym (abs-βₙ []v (`X ∷v []v))) (abs↓ _ _)
  }
```

This lets us prove the desired properties of `` `Z ``{.Agda}.

```agda
abstract
  `Z↓₁ : ⌞ x ⌟ → ⌞ `Z ⋆ x ⌟
  `Z↓₁ {x} xh = subst ⌞_⌟ (sym (abs-βₙ []v ((x , xh) ∷v `X ∷v []v))) (abs↓ _ _)

  `Z-β : ⌞ x ⌟ → ⌞ y ⌟ → `Z ⋆ x ⋆ y ≡ x ⋆ (`Z ⋆ x) ⋆ y
  `Z-β {x} {y} xh yh =
    `X ⋆ `X ⋆ x ⋆ y        ≡⟨ abs-βₙ []v ((y , yh) ∷v (x , xh) ∷v `X ∷v []v) ⟩
    x ⋆ (`X ⋆ `X ⋆ x) ⋆ y  ≡⟨⟩
    x ⋆ (`Z ⋆ x) ⋆ y       ∎
```
