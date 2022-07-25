```agda
open import Cat.Functor.Equivalence
open import Cat.Diagram.Pullback
open import Cat.Diagram.Initial
open import Cat.Functor.Adjoint
open import Cat.Instances.Comma
open import Cat.Instances.Slice
open import Cat.Functor.Base
open import Cat.Prelude

import Cat.Reasoning

module Cat.Functor.Pullback
  {o ℓ} {C : Precategory o ℓ}
  where
```

<!--
```agda
open Cat.Reasoning C
open is-pullback
open Pullback
open Initial
open Functor
open /-Obj
open /-Hom
```
-->

# Base change

Let $\ca{C}$ be a category with all [pullbacks], and $f : Y \to X$ a
morphism in $\ca{C}$. Then we have a functor $f* : \ca{C}/X \to
\ca{C}/Y$, called the **base change**, where the action on objects is
given by pulling back along $f$.

[pullbacks]: Cat.Diagram.Pullback.html

On objects, the functor maps as in the diagram below. It's a bit busy,
so look at it in parts: On the left we have the object $K \xto{g} X$ of
$\ca{C}/X$, and on the right we have the whole pullback diagram, showing
how the parts fit together. The _actual_ object of $\ca{C}/Y$ the
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
module _ (pullbacks : ∀ {X Y Z} f g → Pullback C {X} {Y} {Z} f g) {X Y : Ob} (f : Hom Y X) where
  Base-change : Functor (Slice C X) (Slice C Y)
  Base-change .F₀ x = ob where
    ob : /-Obj Y
    ob .domain = pullbacks (x .map) f .apex
    ob .map    = pullbacks (x .map) f .p₂
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
  Base-change .F₁ {x} {y} dh = dh′ where
    module ypb = Pullback (pullbacks (y .map) f)
    module xpb = Pullback (pullbacks (x .map) f)
    dh′ : /-Hom _ _
    dh′ .map = ypb.limiting {p₁' = dh .map ∘ xpb.p₁}
      (pulll (dh .commutes) ∙ xpb.square)
    dh′ .commutes = ypb.p₂∘limiting
```

<details>
<summary>The properties of pullbacks also guarantee that this operation is
functorial, but the details are not particularly enlightening.</summary>

```agda
  Base-change .F-id {x} = /-Hom-path (sym (xpb.unique id-comm (idr _)))
    where module xpb = Pullback (pullbacks (x .map) f)

  Base-change .F-∘ {x} {y} {z} am bm =
    /-Hom-path (sym (zpb.unique
      (pulll zpb.p₁∘limiting ∙ pullr ypb.p₁∘limiting ∙ assoc _ _ _)
      (pulll zpb.p₂∘limiting ∙ ypb.p₂∘limiting)))
    where
      module ypb = Pullback (pullbacks (y .map) f)
      module zpb = Pullback (pullbacks (z .map) f)
```

</details>

## Properties

The base change functor is a right adjoint. We construct the left
adjoint directly, then give the unit and counit, and finally prove the
triangle identities.

The left adjoint, called _dependent sum_ and written $\sum_f$, is given
on objects by precomposition with $f$, and on morphisms by what is
essentially the identity function --- only the witness of commutativity
must change.

```agda
module _ {X Y : Ob} (f : Hom Y X) where
  Σf : Functor (Slice C Y) (Slice C X)
  Σf .F₀ o = cut (f ∘ o .map)
  Σf .F₁ dh = record { map = dh .map ; commutes = pullr (dh .commutes) }
  Σf .F-id = /-Hom-path refl
  Σf .F-∘ f g = /-Hom-path refl

  open _⊣_
  open _=>_
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
  Σ-ff = is-iso→is-equiv (iso ∘inv (λ x → /-Hom-path refl) λ x →  /-Hom-path refl) where
    ∘inv : /-Hom _ _ → /-Hom _ _
    ∘inv o .map = o .map
    ∘inv o .commutes = invertible→monic isom _ _ (assoc _ _ _ ∙ o .commutes)

  Σ-seso : is-split-eso func
  Σ-seso y = cut (isom.inv ∘ y .map)
           , Sl.make-iso into from′ (/-Hom-path (eliml refl)) (/-Hom-path (eliml refl))
    where
    into : /-Hom _ _
    into .map = id
    into .commutes = id-comm ∙ sym (pulll isom.invl)

    from′ : /-Hom _ _
    from′ .map = id
    from′ .commutes = elimr refl ∙ cancell isom.invl
```
-->

The adjunction unit and counit are given by the universal properties of
pullbacks. ⚠️ WIP ⚠️

<!-- TODO [Amy 2022-03-23]
Explain this better
-->

```agda
module _ (pullbacks : ∀ {X Y Z} f g → Pullback C {X} {Y} {Z} f g) {X Y : Ob} (f : Hom Y X) where
  open _⊣_
  open _=>_

  Σf⊣f* : Σf f ⊣ Base-change pullbacks f
  Σf⊣f* .unit .η obj = dh where
    module pb = Pullback (pullbacks (f ∘ obj .map) f)
    dh : /-Hom _ _
    dh .map = pb.limiting {p₁' = id} {p₂' = obj .map} (idr _)
    dh .commutes = pb.p₂∘limiting
  Σf⊣f* .unit .is-natural x y g =
    /-Hom-path (pb.unique₂
      {p = (f ∘ y .map) ∘ id ∘ g .map ≡⟨ solve! C ⟩ f ∘ y .map ∘ g .map ∎}
      (pulll pb.p₁∘limiting)
      (pulll pb.p₂∘limiting)
      (pulll pb.p₁∘limiting ∙ pullr pb′.p₁∘limiting ∙ id-comm)
      (pulll pb.p₂∘limiting ∙ pb′.p₂∘limiting ∙ sym (g .commutes)))
    where
      module pb = Pullback (pullbacks (f ∘ y .map) f)
      module pb′ = Pullback (pullbacks (f ∘ x .map) f)

  Σf⊣f* .counit .η obj = dh where
    module pb = Pullback (pullbacks (obj .map) f)
    dh : /-Hom _ _
    dh .map = pb.p₁
    dh .commutes = pb.square
  Σf⊣f* .counit .is-natural x y g = /-Hom-path pb.p₁∘limiting
    where module pb = Pullback (pullbacks (y .map) f)

  Σf⊣f* .zig {A} = /-Hom-path pb.p₁∘limiting
    where module pb = Pullback (pullbacks (f ∘ A .map) f)

  Σf⊣f* .zag {B} = /-Hom-path
    (sym (pb.unique₂ {p = pb.square}
      (idr _) (idr _)
      (pulll pb.p₁∘limiting ∙ pullr pb′.p₁∘limiting ∙ idr _)
      (pulll pb.p₂∘limiting ∙ pb′.p₂∘limiting))) where
    module pb = Pullback (pullbacks (B .map) f)
    module pb′ = Pullback (pullbacks (f ∘ pb.p₂) f)
```
