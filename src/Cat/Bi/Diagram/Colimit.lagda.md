<!--
```agda
open import Cat.Bi.Instances.Functor
open import Cat.Bi.Functor.Constant
open import Cat.Functor.Naturality
open import Cat.Functor.Bifunctor
open import Cat.Bi.Functor.Base
open import Cat.Bi.Equivalence hiding (is-equivalence)
open import Cat.Bi.Functor.Hom
open import Cat.Functor.Base
open import Cat.Bi.Duality hiding (_^op)
open import Cat.Bi.Solver
open import Cat.Bi.Base
open import Cat.Prelude

import Cat.Bi.Reasoning as Br
import Cat.Reasoning as Cr
```
-->

```agda
module Cat.Bi.Diagram.Colimit where
```

# Bicategorical colimits

<!--
```agda
private variable
  o h ℓ o' h' ℓ' : Level

module _
  {I : Prebicategory o h ℓ}
  {C : Prebicategory o' (o ⊔ h ⊔ ℓ ⊔ h' ⊔ ℓ') (o ⊔ h ⊔ ℓ ⊔ ℓ')}
  (F : Pseudofunctor I C)
  where

  open Prebicategory C
  open Pseudofunctor
  open Modification
  open Cr.Inverses
  open Cr._≅_
  open _=>ₗ_
  open _=>ₚ_
  open _=>_
```
-->

[[Colimits]] are ubiquitous in category theory, describing universal
constructions of a certain form.  The same is true in bicategory theory,
where we can consider diagrams given by pseudofunctors $F : \bicat{I}
\to \bicat{C}$, and colimiting objects $L \in \bicat{C}$ such that any
cocone over $F$ with apex $X$ corresponds to an essentially unique
morphism $L \to X$.

The primary difference in dealing with bicategorical colimits compared
to their 1-categorical counterparts is that commutativity requirements
are relaxed to 2-cell isomorphisms.  Bicategorical colimits are also
more expressive in that the diagram can specify whether commutativity
conditions should hold up to isomorphism or merely a directed
transformation. For example, in a 1-category, given two parallel
morphisms

~~~{.quiver}
\[\begin{tikzcd}
	A & B
	\arrow["f", shift left, from=1-1, to=1-2]
	\arrow["g"', shift right, from=1-1, to=1-2]
\end{tikzcd}\]
~~~

we can consider a [[coequaliser]], i.e., a universal morphism $h : B \to
C$ identifying $f$ and $g$ in the sense that $h f = h g$.  In a
bicategory we can consider a directed version of this construction, the
coinserter, which consists of a universal 1-cell $h : B \to C$ equipped
with a 2-cell $h f \To h g$.

Other prominent examples of bicategorical colimits include, e.g, cocomma
categories, [[localisations]], and [[Kleisli categories]].

## Bicolimits and lax colimits {defines="bicolimit lax-colimit"}

To avoid having to define the machinery of cones or Kan extensions at
the level of bicategories, we use the characterisation of colimits as
[representing objects].  In 1-category theory, a functor $G : \ca{I} \to
\ca{C}$ has a colimit $L$ if and only if there is an isomorphism
$\ca{C}(L,X) \cong \thecat{Nat}(G,\Delta_X)$ natural in $X$.  Similarly,
in the setting of bicategories, we say that a pseudofunctor $F :
\bicat{I} \to \bicat{C}$ has a **bicolimit** $L$ if and only if there is
an equivalence of categories $\bicat{C}(L,X) \cong
[\bicat{I},\bicat{C}](F,\Delta_X)$ pseudonatural in $X$, where
$\bicat{C}(L,-) : \bicat{C} \to \Cat$ is the [[bicategorical Hom
functor]], $\Delta_X$ is the [[constant pseudofunctor]] at $X$, and
$[\bicat{I},\bicat{C}]$ is the bicategory of pseudofunctors from
$\bicat{I}$ to $\bicat{C}$, pseudonatural transformations between
them, and modifications between those.

[representing objects]: Cat.Diagram.Colimit.Representable.html

Recall that a natural transformation $\alpha : G \To \Delta_X$ specifies
a cocone over the functor $G$.  In the same way, a pseudonatural
transformation $\phi : F \To \Delta_X$ specifies a cocone over the
pseudofunctor $F$, illustrated in the diagram below.

~~~{.quiver}
\[\begin{tikzcd}[column sep=2.25em]
	& X \\
	{F(i)} & {F(j)}
	\arrow[""{name=0, anchor=center, inner sep=0}, "{{\phi_i}}", from=2-1, to=1-2]
	\arrow["{{F(f)}}"', from=2-1, to=2-2]
	\arrow["{{\phi_j}}"', from=2-2, to=1-2]
	\arrow[Rightarrow, from=0, to=2-2, shorten <= 0.2em]
\end{tikzcd}\]
~~~

For each object $i$ in the diagram, $\phi_i : F(i) \to X$ gives a leg of
the cocone, and for any morphism $f : i \to j$, we have a 2-cell
isomorphism $\nu_f : \phi_i \cong \phi_j F(f)$ in place of the usual
commutativity requirement for cocones.

As is often the case in bicategorical definitions, we have the choice of
whether to consider cocones $F \to \Delta_X$ which commute strongly (so
that $\nu_f$ is an isomorphism as above), or to take cocones with
"directed" commutative squares (so that $\nu_f$ is a general
2-cell).  The latter choice yields the notion of a **lax colimit** (or
oplax, depending on the direction of the 2-cells).  It is known that
(op-)lax colimits can be expressed as bicolimits by altering the diagram
category, but in this page, we mainly deal with lax colimits, so we opt
to define those directly.

<!--
TODO: Also define bicolimits and oplax colimits properly.
-->

## Defining lax colimits

A lax colimit of a pseudofunctor $F : \bicat{I} \to \bicat{C}$ consists
of an object $L$ in $\bicat{C}$ together with a pseudonatural
equivalence $\bicat{C}(L,-) \cong [\bicat{I},\bicat{C}]_o(F,\Delta)$,
where $[\bicat{I},\bicat{C}]_o$ denotes the bicategory of pseudofunctors
from $\bicat{I}$ to $\bicat{C}$ together with *oplax* transformations
between them.[^why-oplax] The codomain of this equivalence can be
translated into Agda as follows.

[^why-oplax]: The reason that the lax colimit involves oplax
transformations is that a lax colimit is defined to coincide with a lax
limit in the opposite bicategory, which ends up reversing the direction
of cocone 2-cells.

```agda
  lax-cocones-at : Pseudofunctor C (Cat _ _)
  lax-cocones-at = Hom-from-bi (Pseudoₒ I C) (opᵖ F) P∘ Const-pseudoₒ
```

Now, by a bicategorical Yoneda argument, any pseudonatural equivalence
of the form discussed is determined by its value at $\id : L \to L$,
which is a cocone $F \To \Delta_L$, namely the universal colimiting
cocone.

Under the Yoneda correspondence, a cocone at $L$ induces a functor
$\bicat{C}(L,X) \to [\bicat{I},\bicat{C}]_o(F,\Delta_L)$ by
precomposition.

```agda
  module _ (L : Ob) (univ-cocone : opᵖ F .lax =>ₒ ConstP L .lax) where

    hom→cocone₀ : (X : Ob) → Functor (Hom L X) Pseudoₒ[ opᵖ F , ConstP X ]
    hom→cocone₀ X =
         preaction (Pseudoₒ _ _) {opᵖ F} {ConstP L} {ConstP X} univ-cocone
      F∘ Const-pseudoₒ.Const₁
```

<details>
<summary>
We can show that `hom→cocone₀`{.Agda} extends to a pseudonatural
transformation without too much effort.  We elide the details, which
mostly boil down to automated bicategory reasoning.
</summary>

```agda
    module _ {X Y : Ob} where
      hom→cocone-nat
        :  preaction (Cat _ _) (hom→cocone₀ Y)
        F∘ Flip (Lax.compose _ _) F∘ Const-pseudoₒ.Const₁
        ≅ⁿ postaction (Cat _ _) (hom→cocone₀ X) F∘ compose
      hom→cocone-nat = to-natural-iso ni where
        ni : make-natural-iso _ _
        ni .make-natural-iso.eta f .η g .Γ a         = α← _
        ni .make-natural-iso.eta f .η g .is-natural  = bicat! C
        ni .make-natural-iso.eta f .is-natural g h α = ext λ _ → bicat! C
        ni .make-natural-iso.inv f .η g .Γ a         = α→ _
        ni .make-natural-iso.inv f .η g .is-natural  = bicat! C
        ni .make-natural-iso.inv f .is-natural g h α = ext λ _ → bicat! C
        ni .make-natural-iso.eta∘inv f               = ext λ _ _ → Br.α≅ C .invr
        ni .make-natural-iso.inv∘eta f               = ext λ _ _ → Br.α≅ C .invl
        ni .make-natural-iso.natural g h α           = ext λ _ _ → bicat! C

    hom→cocone : Hom-from-bi C L .lax =>ₚ lax-cocones-at .lax
    hom→cocone .lax .σ                = hom→cocone₀
    hom→cocone .lax .naturator        = hom→cocone-nat .to
    hom→cocone .lax .ν-compositor f g = ext λ _ _ → bicat! C
    hom→cocone .lax .ν-unitor         = ext λ _ _ → bicat! C
    hom→cocone .naturator-inv f       =
      Cr.iso→invertible Cat[ _ , _ ] (isoⁿ→iso hom→cocone-nat f)

```

</details>

In other words, to show that $L$ is the lax colimit of $F$, it suffices
to provide a candidate cocone with apex $L$, and show that
`hom→cocone`{.Agda} is a pseudonatural equivalence, which corresponds to
showing that the provided cocone is universal.

```agda
    is-lax-colimit : Type _
    is-lax-colimit = is-equivalenceᵖ hom→cocone
```
