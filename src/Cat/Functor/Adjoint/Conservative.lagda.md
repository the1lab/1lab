---
description: |
  Conservative adjoints.
---
<!--
```agda
open import Cat.Functor.Adjoint.Properties
open import Cat.Diagram.Limit.Finite
open import Cat.Functor.Conservative
open import Cat.Functor.Properties
open import Cat.Functor.Morphism
open import Cat.Functor.Adjoint
open import Cat.Functor.Compose
open import Cat.Prelude

import Cat.Morphism.Strong.Epi
import Cat.Functor.Reasoning
import Cat.Natural.Reasoning
import Cat.Reasoning
```
-->
```agda
module Cat.Functor.Adjoint.Conservative where
```

# Conservative adjoint functors {defines="conservative-adjoint-functors"}

This short note proves that a [[right adjoint]] $R : \cD \to \cC$ from
a [[finitely complete]] category is [[conservative]] if and only if the
counit of the adjunction is a componentwise [[strong epimorphism]]. This
is a particularly useful result, as helps us satisfy one of the hypotheses
of the [[crude monadicity theorem]].

<!--
```agda
module _
  {oc ℓc od ℓd}
  {C : Precategory oc ℓc}
  {D : Precategory od ℓd}
  {L : Functor C D} {R : Functor D C}
  (L⊣R : L ⊣ R)
  where
  private
    module C = Cat.Reasoning C
    module D where
      open Cat.Reasoning D public
      open Cat.Morphism.Strong.Epi D public
    module L = Cat.Functor.Reasoning L
    module R = Cat.Functor.Reasoning R
    open _⊣_ L⊣R
```
-->

For the forward direction, suppose that $D$ is finitely complete, and $R$
is conservative; we need to show that $\eps_{X}$ is a strong epi. Because
$D$ is finitely complete, it suffices to prove that $\eps_{X}$ is an
[[extremal epi]]. Let $m \circ f$ be a factorization of $\eps_{X}$
with $m$ [[monic]]; we now need to show that $\eps_{X}$ is invertible.
However, $R$ is conservative, so it is sufficient to show that $R(m)$ is
invertible.

We will do this by showing that is monic $R(m)$ and has a section.
The former is immediate, as [[right adjoints preserve monos]]. The latter
will require a bit more mork, but only just: the [[adjunct]] of $f$
is a suitable candidate, and a quick calculation verifies that it is
indeed a section.

```agda
  right-conservative→counit-strong-epi
    : Finitely-complete D
    → is-conservative R
    → ∀ {x} → D.is-strong-epi (ε x)
  right-conservative→counit-strong-epi D-fc R-cons =
    D.is-extremal-epi→is-strong-epi D-fc λ m f ε=mf →
    R-cons $
    C.has-section+monic→invertible
      (C.make-section (L-adjunct L⊣R f) (R.pulll (sym ε=mf) ∙ zag))
      (right-adjoint→is-monic R L⊣R (D.monic m))
```

On to the reverse direction. Suppose that the counit is a strong epi,
and let $f : \cD(X,Y)$ such that $R(f)$ is invertible; our goal is to
show that $f$ is invertible. We shall do this by showing that $f$ is both
a mono and a strong epi.

```agda
  counit-strong-epi→right-conservative
    : (∀ {x} → D.is-strong-epi (ε x))
    → is-conservative R
  counit-strong-epi→right-conservative ε-strong-epi {x} {y} {f} Rf-inv =
    D.strong-epi+mono→invertible
      f-strong-epi
      f-monic
    where
```

The case where $f$ is monic is the easier of the two. Let $g, h : \cD(A,X)$
such that $f \circ g = g \circ h$; our aim is to show that $f = g$. By our
assumptions, $\eps$ is a strong epi (and thus an epi), so it suffices
to show that $g \circ eps = h \circ \eps$. By naturality, this is equivalent
to showing that $eps \circ L(R(g)) = \eps \circ L(R(h))$. Finally,
$R(f)$ is invertible, so it must be monic: this means that it suffices
to show that $R(f) \circ R(g) = R(f) \circ R(h)$, which follows directly
from our hypothesis that $f \circ g = f \circ h$.

```agda
      f-monic : D.is-monic f
      f-monic g h fg=fh =
        ε-strong-epi .fst g h $
        counit.viewl $
        ap L.₁ $
        C.invertible→monic Rf-inv (R.F₁ g) (R.F₁ h) (R.weave fg=fh)
```

Luckily, proving that $f$ is a strong epi is not that much harder.
Strong epis have a left-cancellation property, so it is sufficient
to show that $f \circ \eps$ is a strong epi. By naturality, this is
equivalent to showing that $\eps \circ L(R(f))$ is a strong epi.
Strong epis compose, and $\eps$ is a strong epi by our assumptions,
so all that remains is to show that $L(R(f))$ is a strong epi.
This is immediate: $L(R(f))$ is invertible, and invertible maps are
strong epis.

```agda
      f-strong-epi : D.is-strong-epi f
      f-strong-epi =
        D.strong-epi-cancelr f (ε x) $
        D.subst-is-strong-epi (counit.is-natural x y f) $
        D.strong-epi-∘ (ε y) (L.₁ (R.₁ f))
          ε-strong-epi
          (D.invertible→strong-epi (L.F-map-invertible Rf-inv))
```
