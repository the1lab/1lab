<!--
```agda
open import Cat.Functor.Adjoint.Comonadic
open import Cat.Diagram.Colimit.Base
open import Cat.Functor.Conservative
open import Cat.Functor.Kan.Unique
open import Cat.Functor.Kan.Base
open import Cat.Diagram.Product
open import Cat.Instances.Slice
open import Cat.Prelude

import Cat.Reasoning

open lifts-colimit
open Functor
open /-Obj
open /-Hom
open _=>_
```
-->

```agda
module Cat.Instances.Slice.Colimit
  {o ℓ} {C : Precategory o ℓ} {c : ⌞ C ⌟}
  where
```

# Colimits in slices {defines="colimits-in-slice-categories"}

Unlike [[limits in slice categories]], [[colimits]] in a [[slice category]]
are computed just like colimits in the base category; more precisely,
the `Forget/`{.Agda}ful functor $U : \cC/c \to \cC$ [[creates colimits]].

That is, if we are given a diagram $F : \cJ \to \cC/c$ such that $U
\circ F$ has a colimit in $\cC$, we can conclude:

- that $F$ has a colimit in $\cC/c$;
- that this colimit is [[preserved|preserved colimit]] by $U$;
- and that $U$ [[reflects colimits]] of $F$.

<!--
```agda
private
  module C   = Cat.Reasoning C
  module C/c = Cat.Reasoning (Slice C c)

  U : Functor (Slice C c) C
  U = Forget/

module
  _ {o' ℓ'} {J : Precategory o' ℓ'} (F : Functor J (Slice C c))
  where
  open make-is-colimit

  private
    module J = Cat.Reasoning J
    module F = Functor F
```
-->

As a guiding example, let us consider the case of coproducts, as in the
diagram below. We are given a binary diagram $a \to c \ot b$ in $\cC/c$
and a colimiting cocone $a \to a + b \ot b$ in $\cC$.

~~~{.quiver}
\[\begin{tikzcd}
  a & {a+b} & b \\
  & c
  \arrow[from=1-1, to=1-2]
  \arrow[from=1-1, to=2-2]
  \arrow[dashed, from=1-2, to=2-2]
  \arrow[from=1-3, to=1-2]
  \arrow[from=1-3, to=2-2]
\end{tikzcd}\]
~~~

The first observation is that there is a unique map $a + b \to c$ that
turns this into a cocone in $\cC/c$:

```agda
  Forget/-lifts-colimit : Colimit (U F∘ F) → Colimit F
  Forget/-lifts-colimit UF-colim = to-colimit K-colim
    module Forget/-lifts where
      module UF-colim = Colimit UF-colim
      K : C/c.Ob
      K .domain = UF-colim.coapex
      K .map = UF-colim.universal (λ j → F.₀ j .map) (λ f → F.₁ f .commutes)

      mk : make-is-colimit F K
      mk .ψ j .map = UF-colim.cocone .η j
      mk .ψ j .commutes = UF-colim.factors _ _
      mk .commutes f = ext (UF-colim.cocone .is-natural _ _ f ∙ C.idl _)
```

All that remains is to show that this cocone is colimiting in $\cC/c$.
Given another cocone with apex $z$ we get a map $a + b \to z$ by the
universal property of $a + b$, but we need to check that it commutes
with the relevant maps into $c$; this follows from the uniqueness of
the universal map.

```agda
      mk .universal eta comm .map = UF-colim.universal
        (λ j → eta j .map)
        (λ f → unext (comm f))
      mk .universal eta comm .commutes = ext (UF-colim.unique _ _ _ λ j →
        C.pullr (UF-colim.factors _ _) ∙ eta j .commutes)
      mk .factors eta comm = ext (UF-colim.factors _ _)
      mk .unique eta comm u fac = ext (UF-colim.unique _ _ _ λ j →
        unext (fac j))

      K-colim : is-colimit F K (to-cocone mk)
      K-colim = to-is-colimit mk
```

The colimit thus constructed is preserved by $U$ *by construction*, as
we haven't touched the "top" part of the diagram. This shows that $U$
[[lifts colimits]].

```agda
      K-colim-preserved : preserves-lan U K-colim
      K-colim-preserved = generalize-colimitp UF-colim.has-colimit refl

module _ {oj ℓj} {J : Precategory oj ℓj} where
  Forget/-lifts-colimits : lifts-colimits-of J U
  Forget/-lifts-colimits colim .lifted =
    Forget/-lifts-colimit _ colim
  Forget/-lifts-colimits colim .preserved =
    Forget/-lifts.K-colim-preserved _ colim
```

Finally, since $U$ is [[conservative]], it automatically reflects the
colimits that it preserves, hence it [[creates colimits]].

```agda
  Forget/-creates-colimits : creates-colimits-of J U
  Forget/-creates-colimits = conservative+lifts→creates-colimits
    Forget/-is-conservative Forget/-lifts-colimits
```

In particular, if a category $\cC$ is cocomplete, then so are its slices:

```agda
is-cocomplete→slice-is-cocomplete
  : ∀ {o' ℓ'}
  → is-cocomplete o' ℓ' C
  → is-cocomplete o' ℓ' (Slice C c)
is-cocomplete→slice-is-cocomplete =
  lifts-colimits→cocomplete Forget/ Forget/-lifts-colimits
```

::: note
If $\cC$ has binary [[products]] with $c$, then this result is a consequence
of `Forget/`{.Agda} [[being comonadic|constant family]], since [[comonadic
functors create colimits]]! However, this result is more general as it
does not require any products.

```agda
products→Forget/-creates-colimits
  : has-products C
  → ∀ {o' ℓ'} {J : Precategory o' ℓ'}
  → creates-colimits-of J U
products→Forget/-creates-colimits prods = comonadic→creates-colimits
  (Forget⊣constant-family prods) (Forget/-comonadic prods)
```
:::
