<!--
```agda
open import Cat.Diagram.Colimit.Base
open import Cat.Functor.Conservative
open import Cat.Functor.Kan.Unique
open import Cat.Functor.Kan.Base
open import Cat.Instances.Slice
open import Cat.Prelude

import Cat.Reasoning

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
are computed just like colimits in the base category. That is, if we are
given a diagram $F : \cJ \to \cC/c$ such that $U \circ F$ has a
colimit in $\cC$ (where $U$ is the `forgetful`{.Agda ident=Forget/} functor $\cC/c
\to \cC$), we can conclude:

- that $F$ has a colimit in $\cC/c$;
- that this colimit is [[preserved|preserved colimit]] by $U$;
- and that $U$ [[reflects|reflected colimit]] colimits of $F$.

In summary, we say that $U$ *creates* the colimits that exist in $\cC$.
To understand why the assumption that the colimit exists in $\cC$ is
necessary, consider the case where $\cC$ is a [[poset]], and we're
interested in computing [[bottom elements]] ([[initial objects]], i.e.
colimits of the empty diagram).
Note that the existence of a bottom element in $\cC/c$ only means that
there is a least element *that is less than $c$*, but does not imply
the existence of a global bottom element. For example, the poset
pictured below has an initial object $a$ in the slice over $c$, but
no global initial object.

~~~{.quiver}
\[\begin{tikzcd}
  c & d \\
  a & b
  \arrow[from=2-1, to=1-1]
  \arrow[from=2-2, to=1-2]
\end{tikzcd}\]
~~~

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

Back to categories, let's consider the case of coproducts, as in the
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
  Forget/-lifts-colimits : Colimit (U F∘ F) → Colimit F
  Forget/-lifts-colimits UF-colim = to-colimit K-colim
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

      preserved : preserves-lan U K-colim
      preserved = generalize-colimitp UF-colim.has-colimit refl
```

The colimit thus constructed is preserved by $U$ *by construction*, as
we haven't touched the "top" part of the diagram. We can generalise this
to all colimits of $F$.

```agda
  Forget/-preserves-colimits : Colimit (U F∘ F) → preserves-colimit U F
  Forget/-preserves-colimits UF-colim =
    preserves-lan→preserves-all U K-colim preserved
    where open Forget/-lifts UF-colim
```

Finally, $U$ is [[conservative]], hence it reflects the colimits that it
preserves, provided they exist in $\cC/c$. We can use the fact that
$U$ lifts limits to satisfy the hypotheses.

```agda
  Forget/-reflects-colimits : reflects-colimit U F
  Forget/-reflects-colimits UK-colim = conservative-reflects-colimits
    Forget/-is-conservative
    (Forget/-lifts-colimits UF-colim)
    (Forget/-preserves-colimits UF-colim)
    UK-colim
    where UF-colim = to-colimit UK-colim
```

In particular, if a category $\cC$ is cocomplete, then so are its slices:

```agda
is-cocomplete→slice-is-cocomplete
  : ∀ {o' ℓ'}
  → is-cocomplete o' ℓ' C
  → is-cocomplete o' ℓ' (Slice C c)
is-cocomplete→slice-is-cocomplete colims F =
  Forget/-lifts-colimits F (colims (U F∘ F))
```
