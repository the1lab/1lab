<!--
```agda
open import Cat.Functor.Equivalence
open import Cat.Functor.Properties
open import Cat.Diagram.Pullback
open import Cat.Diagram.Initial
open import Cat.Functor.Adjoint
open import Cat.Functor.Compose
open import Cat.Instances.Comma
open import Cat.Instances.Slice
open import Cat.Prelude

import Cat.Reasoning
```
-->

```agda
module Cat.Functor.Pullback
  {o ℓ} {C : Precategory o ℓ}
  where
```

<!--
```agda
open Cat.Reasoning C
open Initial
open Functor
open _=>_
open /-Obj
open /-Hom
```
-->

# Base change {defines="pullback-functor"}

Let $\cC$ be a category with all [[pullbacks]], and $f : Y \to X$ a
morphism in $\cC$. Then we have a functor $f^* : \cC/X \to \cC/Y$, called
the **base change**, where the action on objects is given by pulling
back along $f$.

On objects, the functor maps as in the diagram below. It's a bit busy,
so look at it in parts: On the left we have the object $K \xto{g} X$ of
$\cC/X$, and on the right we have the whole pullback diagram, showing
how the parts fit together. The _actual_ object of $\cC/Y$ the
functor gives is the vertical arrow $Y \times_X K \to Y$.

~~~{.quiver}
\[\begin{tikzcd}
  & {Y \times_X K} && K \\
  {(K,K\xrightarrow{g}X)} \\
  & Y && X
  \arrow[""{name=0, anchor=center, inner sep=0}, "{f^*g}", from=1-2, to=3-2]
  \arrow[from=1-2, to=1-4]
  \arrow["g"', from=1-4, to=3-4]
  \arrow["f", from=3-2, to=3-4]
  \arrow[shorten >=6pt, Rightarrow, maps to, from=2-1, to=0]
\end{tikzcd}\]
~~~

```agda
module _ (pullbacks : Pullbacks C) {X Y : Ob} (f : Hom Y X) where
  open Pullbacks pullbacks

  Base-change : Functor (Slice C X) (Slice C Y)
  Base-change .F₀ x = ob where
    ob : /-Obj Y
    ob .domain = Pb (x .map) f
    ob .map    = p₂ (x .map) f
```

On morphisms, we use the universal property of the pullback to obtain a
map $Y \times_X K \to Y \times_X K'$, by observing that the square
diagram below is a cone over $K' \to X \ot Y$.

~~~{.quiver}
\[\begin{tikzcd}
  {Y\times_XK} && {K'} \\
  \\
  X && Y
  \arrow["{p^*}", from=1-1, to=3-1]
  \arrow["{p'}", from=1-3, to=3-3]
  \arrow["{g \circ p_2}"{description}, from=1-1, to=1-3]
  \arrow["f"{description}, from=3-1, to=3-3]
\end{tikzcd}\]
~~~

```agda
  Base-change .F₁ {x} {y} dh = dh' where
    dh' : /-Hom _ _
    dh' .map = pb (dh .map ∘ p₁ (x .map) f) _ (pulll (dh .commutes) ∙ square)
    dh' .commutes = p₂∘pb
```

<details>
<summary>The properties of pullbacks also guarantee that this operation is
functorial, but the details are not particularly enlightening.</summary>

```agda
  Base-change .F-id {x} = ext (sym (pb-unique id-comm (idr _)))

  Base-change .F-∘ {x} {y} {z} am bm =
    ext (sym (pb-unique
      (pulll p₁∘pb ∙ pullr p₁∘pb ∙ assoc _ _ _)
      (pulll p₂∘pb ∙ p₂∘pb)))
```

</details>

## Properties

The base change functor is a right adjoint. We construct the left
adjoint directly, then give the unit and counit, and finally prove the
triangle identities.

The [[left adjoint]], called _dependent sum_ and written $\sum_f$, is given
on objects by precomposition with $f$, and on morphisms by what is
essentially the identity function --- only the witness of commutativity
must change.

```agda
module _ {X Y : Ob} (f : Hom Y X) where
  Σf : Functor (Slice C Y) (Slice C X)
  Σf .F₀ o = cut (f ∘ o .map)
  Σf .F₁ dh = record { map = dh .map ; commutes = pullr (dh .commutes) }
  Σf .F-id = trivial!
  Σf .F-∘ f g = trivial!

  open _⊣_
```

<!--
```agda
Σ-iso-equiv
  : {X Y : Ob} {f : Hom Y X}
  → Cat.Reasoning.is-invertible C f
  → is-equivalence (Σf f)
Σ-iso-equiv {X} {f = f} isom = ff+split-eso→is-equivalence Σ-ff Σ-seso where
  module Sl = Cat.Reasoning (Slice C X)
  module isom = is-invertible isom

  func = Σf f
  Σ-ff : ∀ {x y} → is-equiv (func .F₁ {x} {y})
  Σ-ff = is-iso→is-equiv (iso ∘inv (λ x → trivial!) λ x → trivial!) where
    ∘inv : /-Hom _ _ → /-Hom _ _
    ∘inv o .map = o .map
    ∘inv o .commutes = invertible→monic isom _ _ (assoc _ _ _ ∙ o .commutes)

  Σ-seso : is-split-eso func
  Σ-seso y = cut (isom.inv ∘ y .map)
           , Sl.make-iso into from' (ext (eliml refl)) (ext (eliml refl))
    where
    into : /-Hom _ _
    into .map = id
    into .commutes = id-comm ∙ sym (pulll isom.invl)

    from' : /-Hom _ _
    from' .map = id
    from' .commutes = elimr refl ∙ cancell isom.invl
```
-->

The adjunction unit and counit are given by the universal properties of
pullbacks. ⚠️ WIP ⚠️

<!-- TODO [Amy 2022-03-23]
Explain this better
-->

```agda
module _ (pullbacks : Pullbacks C) {X Y : Ob} (f : Hom Y X) where
  open Pullbacks pullbacks
  open _⊣_
  open _=>_

  Σf⊣f* : Σf f ⊣ Base-change pullbacks f
  Σf⊣f* .unit .η obj = dh where
    dh : /-Hom _ _
    dh .map = pb id (obj .map) (idr _)
    dh .commutes = p₂∘pb
  Σf⊣f* .unit .is-natural x y g =
    ext (pb-unique₂
      {p = (f ∘ y .map) ∘ id ∘ g .map ≡⟨ cat! C ⟩ f ∘ y .map ∘ g .map ∎}
      (pulll p₁∘pb)
      (pulll p₂∘pb)
      (pulll p₁∘pb ∙ pullr p₁∘pb ∙ id-comm)
      (pulll p₂∘pb ∙ p₂∘pb ∙ sym (g .commutes)))

  Σf⊣f* .counit .η obj = dh where
    dh : /-Hom _ _
    dh .map = p₁ (obj .map) f
    dh .commutes = square
  Σf⊣f* .counit .is-natural x y g = ext p₁∘pb
  Σf⊣f* .zig {A} = ext p₁∘pb
  Σf⊣f* .zag {B} = ext
    (sym (pb-unique₂ {p = square}
      (idr _) (idr _)
      (pulll p₁∘pb ∙ pullr p₁∘pb ∙ idr _)
      (pulll p₂∘pb ∙ p₂∘pb)))
```

## Equifibred natural transformations {defines="equifibred cartesian-natural-transformation"}

A [[natural transformation]] $F \To G$ is called **equifibred**, or
**cartesian**, if each of its naturality squares is a [[pullback]]:

~~~{.quiver}
\[\begin{tikzcd}
  Fa & Fb \\
  Ga & Gb
  \arrow["Ff", from=1-1, to=1-2]
  \arrow["{\alpha_a}"', from=1-1, to=2-1]
  \arrow["Gf"', from=2-1, to=2-2]
  \arrow["{\alpha_b}", from=1-2, to=2-2]
  \arrow["\lrcorner"{anchor=center, pos=0.125}, draw=none, from=1-1, to=2-2]
\end{tikzcd}\]
~~~

```agda
is-equifibred
  : ∀ {oj ℓj} {J : Precategory oj ℓj} {F G : Functor J C}
  → F => G → Type _
is-equifibred {J = J} {F} {G} α =
  ∀ {x y} (f : J .Precategory.Hom x y)
  → is-pullback C (F .F₁ f) (α .η y) (α .η x) (G .F₁ f)
```

An easy property of equifibered transformations is that they are
closed under pre-whiskering:

```agda
◂-equifibred
  : ∀ {oj ℓj ok ℓk} {J : Precategory oj ℓj} {K : Precategory ok ℓk}
  → {F G : Functor J C} (H : Functor K J) (α : F => G)
  → is-equifibred α → is-equifibred (α ◂ H)
◂-equifibred H α eq f = eq (H .F₁ f)
```
