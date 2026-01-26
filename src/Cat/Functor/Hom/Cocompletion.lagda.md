<!--
```agda
open import Cat.Functor.Adjoint.Continuous
open import Cat.Functor.Kan.Pointwise
open import Cat.Diagram.Colimit.Base
open import Cat.Functor.Kan.Nerve
open import Cat.Instances.Functor
open import Cat.Functor.Kan.Base
open import Cat.Functor.Hom
open import Cat.Prelude
```
-->

```agda
module
  Cat.Functor.Hom.Cocompletion
    {κ o} (C : Precategory κ κ) (D : Precategory o κ)
    (colim : is-cocomplete κ κ D)
    where
```

<!--
```agda
private
  module C = Precategory C
  module D = Precategory D
open import Cat.Morphism Cat[ C , D ] using (_≅_)

open _=>_
```
-->

# Free cocompletions {defines="free-cocompletion"}

Let $\cC$ be a [$\kappa$-small] precategory. It, broadly speaking,
will not be cocomplete. Suppose that we're interested in passing from
$\cC$ to a cocomplete category; How might we go about this in a
universal way?

To substantiate this problem, it helps to picture a _geometric_ case.
We'll take $\cC = \Delta$, the [[simplex category]]. The objects and
maps in this category satisfy
equations which let us, broadly speaking, think of its objects as
"abstract (higher-dimensional) triangles", or _simplices_. For instance,
there are (families) of maps $[n]\to[n+1]$, exhibiting an
$n$-dimensional simplex as a face in an $(n+1)$-dimensional simplex.

[$\kappa$-small]: 1Lab.intro.html#universes-and-size-issues

Now, this category does _not_ have all colimits. For example, we should
be able to glue the red and blue triangles in the diagram below to obtain a
"square", but you'll find no such object in $\Delta$.

~~~{.quiver}
\[\begin{tikzcd}
  \bullet && \bullet \\
  \\
  \bullet && \bullet
  \arrow[shift right=1, color={rgb,255:red,92;green,92;blue,214}, from=1-1, to=3-3]
  \arrow[color={rgb,255:red,92;green,92;blue,214}, from=1-1, to=3-1]
  \arrow[color={rgb,255:red,92;green,92;blue,214}, from=3-1, to=3-3]
  \arrow[color={rgb,255:red,214;green,92;blue,92}, from=1-1, to=1-3]
  \arrow[color={rgb,255:red,214;green,92;blue,92}, from=1-3, to=3-3]
  \arrow[shift left=1, color={rgb,255:red,214;green,92;blue,92}, from=1-1, to=3-3]
\end{tikzcd}\]
~~~

Universally embedding $\Delta$ in a cocomplete category should then
result in a "category of shapes built by gluing simplices"; formally,
these are called _simplicial sets_. It turns out that the [Yoneda
embedding] satisfies the property we're looking for: any functor $F :
\cC \to \cD$ into a cocomplete category $\cD$ factors as

$$
\cC \xto{\yo} \psh(\cC) \xto{\Lan_\yo F} \cD
$$,

where $\Lan_\yo F$ is the [[left Kan extension]] of $F$ along the Yoneda
embedding, and furthermore this extension preserves colimits. While this
may sound like a _lot_ to prove, it turns out that the tide has already
risen above it: everything claimed above follows from the general theory
of Kan extensions.

[Yoneda embedding]: Cat.Functor.Hom.html#the-yoneda-embedding

```agda
よ-extension : (F : Functor C D) → Lan (よ C) F
よ-extension F = cocomplete→lan (よ C) F colim

よ-extension-cocontinuous
  : ∀ {o' κ' F} → is-cocontinuous o' κ' (よ-extension F .Lan.Ext)
よ-extension-cocontinuous = left-adjoint-is-cocontinuous
  (Realisation⊣Nerve _ colim)

よ-extension-extends : (F : Functor C D) → よ-extension F .Lan.Ext F∘ よ C ≅ F
よ-extension-extends F = ff→cocomplete-lan-ext (よ C) F colim
  (よ-is-fully-faithful C)
```
