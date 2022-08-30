```agda
open import Cat.Functor.Adjoint.Continuous
open import Cat.Diagram.Colimit.Base
open import Cat.Functor.Kan.Nerve
open import Cat.Instances.Functor
open import Cat.Functor.Hom
open import Cat.Functor.Kan
open import Cat.Prelude

module
  Cat.Functor.Hom.Cocompletion
    {κ o} (C : Precategory κ κ) (D : Precategory o κ)
    (colim : is-cocomplete κ κ D)
    where
```

<!--
```agda
open import Cat.Morphism Cat[ C , D ] using (_≅_)
```
-->

# Free cocompletions

Let $\ca{C}$ be a [$\kappa$-small] precategory. It, broadly speaking,
will not be cocomplete. Suppose that we're interested in passing from
$\ca{C}$ to a cocomplete category; How might we go about this in a
universal way?

To substantiate this problem, it helps to picture a _geometric_ case.
We'll take $\ca{C} = \Delta$, the category of non-empty finite ordinals
and monotonic functions. The objects and maps in this category satisfy
equations which let us, broadly speaking, think of its objects as
"abstract (higher-dimensional) triangles", or _simplices_. For instance,
there are (families) of maps $[n]\to[n+1]$, exhibiting an
$n$-dimensional simplex as a face in an $(n+1)$-dimensional simplex.

[$\kappa$-small]: 1Lab.intro.html#universes-and-size-issues

Now, this category does _not_ have all colimits. For example, we should
be able to the red and blue triangles in the diagram below to obtain a
"square", but you'll find no such object in $\Delta$.

~~~{.quiver}
\[\begin{tikzcd}
  \bullet && \bullet \\
  \\
  \bullet && \bullet
  \arrow[color={rgb,255:red,92;green,92;blue,214}, from=1-1, to=3-3]
  \arrow[color={rgb,255:red,92;green,92;blue,214}, from=3-1, to=1-1]
  \arrow[color={rgb,255:red,92;green,92;blue,214}, from=3-1, to=3-3]
  \arrow[color={rgb,255:red,214;green,92;blue,92}, from=1-1, to=1-3]
  \arrow[color={rgb,255:red,214;green,92;blue,92}, from=1-3, to=3-3]
  \arrow[shift left=1, color={rgb,255:red,214;green,92;blue,92}, from=1-1, to=3-3]
\end{tikzcd}\]
~~~

Universally embedding $\Delta$ in a cocomplete category should then
result in a "category of shapes built by gluing simplices"; Formally,
these are called _simplicial sets_. It turns out that the [Yoneda
embedding] satisfies the property we're looking for: Any functor $F :
\ca{C} \to \ca{D}$ into a cocomplete category $\ca{D}$ factors as

$$
\ca{C} \xto{\yo} \psh(\ca{C}) \xto{\Lan_\yo F} \ca{D}\text{,}
$$

where $\Lan_\yo F$ is the [left Kan extension] of $F$ along the Yoneda
embedding, and furthermore this extension preserves colimits. While this
may sound like a _lot_ to prove, it turns out that the tide has already
risen above it: Everything claimed above follows from the general theory
of Kan extensions.

[Yoneda embedding]: Cat.Functor.Hom.html#the-yoneda-embedding
[left Kan extension]: Cat.Functor.Kan.html

```agda
extend : Functor C D → Functor (PSh κ C) D
extend F = Realisation colim F

extend-cocontinuous
  : ∀ {od ℓd} {J : Precategory od ℓd} {Dg : Functor J (PSh κ C)} (F : Functor C D)
  → Colimit Dg → Colimit (extend F F∘ Dg)
extend-cocontinuous F = left-adjoint-colimit (Realisation⊣Nerve colim F)

extend-factors : (F : Functor C D) → (extend F F∘ よ C) ≅ F
extend-factors F = ff-lan-ext colim (よ C) F (よ-is-fully-faithful C)
```
