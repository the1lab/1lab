---
description: |
  We prove various properties of hom functors and the yoneda embedding.
---
<!--
```agda
open import Cat.Functor.Properties
open import Cat.Functor.Base
open import Cat.Functor.Hom
open import Cat.Prelude

import Cat.Functor.Morphism
import Cat.Reasoning

open Functor
```
-->

```agda
module Cat.Functor.Hom.Properties where
```

# Properties of hom functors

This module contains a collection of useful facts about [[Hom
functors]], and the [[Yoneda embedding]].

<!--
```agda
module _ {o ℓ} {C : Precategory o ℓ} where
  open Cat.Reasoning C
  private
    module PSh[C] = Cat.Reasoning Cat[ C ^op , Sets ℓ ]
    module CoPSh[C] = Cat.Reasoning Cat[ C , Sets ℓ ]
    module よ = Cat.Functor.Morphism (よ C)
    module Hom[-,-] = Cat.Functor.Morphism (Hom[-,-] C)

  private
    variable
      x y z : Ob
      f g h : Hom x y

  open _=>_
```
-->

## Monos and epis

The Yoneda embedding preserves [[monomorphisms]]. Let $f : \cC(A,B)$ be
a mono, and let $\alpha, \beta : P \to \yo(A)$ be a pair of natural
transformations such that $\yo(f) \circ \alpha = \yo(f) \circ \beta$.
Equality of [[natural transformations]] is defined componentwise, so for
every $X : \cC$ and $p_x : P(x)$, we have $f \circ \alpha_x(p_x) = f
\circ \beta_x(p_x)$. Since $f$ is a mono, we can immediately deduce that
$\alpha = \beta$.

```agda
  よ-preserves-mono : is-monic f → PSh[C].is-monic (よ C .Functor.F₁ f)
  よ-preserves-mono f-mono α β p = ext λ x px →
    f-mono (α .η x px) (β .η x px) (unext p x px)
```

Furthermore, the Yoneda embedding is [[fully faithful]], so it reflects
both monos and [[epis|epimorphism]].

```agda
  よ-reflects-mono : PSh[C].is-monic (よ C .Functor.F₁ f) → is-monic f
  よ-reflects-mono = よ.faithful→reflects-mono (よ-is-faithful C)

  よ-reflects-epi : PSh[C].is-epic (よ C .Functor.F₁ f) → is-epic f
  よ-reflects-epi = よ.faithful→reflects-epi (よ-is-faithful C)
```

Likewise, the covariant Yoneda embedding takes epis to monos, reflects
monos to epis, and vice versa.

```agda
  Hom[-,-]-reverses-epi : is-epic f → CoPSh[C].is-monic (Hom[-,-] C .F₁ f)
  Hom[-,-]-reverses-epi {f = f} f-epic α β p = ext λ x px →
    f-epic (α .η x px) (β .η x px) (unext p x px)

  Hom[-,-]-reflects-mono-to-epi : CoPSh[C].is-monic (Hom[-,-] C .F₁ f) → is-epic f
  Hom[-,-]-reflects-mono-to-epi = Hom[-,-].faithful→reflects-mono (Hom[-,-]-is-faithful C)

  Hom[-,-]-reflects-epi-to-mono : CoPSh[C].is-epic (Hom[-,-] C .F₁ f) → is-monic f
  Hom[-,-]-reflects-epi-to-mono = Hom[-,-].faithful→reflects-epi (Hom[-,-]-is-faithful C)
```
