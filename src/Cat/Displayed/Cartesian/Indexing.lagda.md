<!--
```agda
{-# OPTIONS --lossy-unification #-}
open import Cat.Bi.Instances.Discrete
open import Cat.Displayed.Cartesian
open import Cat.Instances.Discrete
open import Cat.Instances.Functor
open import Cat.Displayed.Fibre
open import Cat.Displayed.Base
open import Cat.Bi.Base
open import Cat.Prelude

import Cat.Displayed.Reasoning
import Cat.Reasoning
import Cat.Morphism as Mor
```
-->

```agda
module Cat.Displayed.Cartesian.Indexing
  {o ℓ o′ ℓ′} {B : Precategory o ℓ}
  (E : Displayed B o′ ℓ′)
  (cartesian : Cartesian-fibration E)
  where
```

<!--
```agda
open Cartesian-fibration cartesian
open Cat.Displayed.Reasoning E
open Cat.Reasoning B
open Cartesian-lift
open is-cartesian
open Functor
```
-->

# Reindexing for Cartesian fibrations

A [cartesian fibration] can be thought of as a [displayed category]
$\cE$ whose [fibre categories] $\cE^*(b)$ depend
([pseudo])functorially on the object $b : \cB$ from the base
category. A canonical example is [the canonical self-indexing]: If
$\cC$ is a category with [pullbacks], then each $b \xto{f} a :
\cC$ gives rise to [a functor] $\cC/a \to \cC/b$, the _change
of base_ along $f$.

[cartesian fibration]: Cat.Displayed.Cartesian.html
[displayed category]: Cat.Displayed.Base.html
[fibre categories]: Cat.Displayed.Fibre.html
[pseudo]: Cat.Bi.Base.html#pseudofunctors
[the canonical self-indexing]: Cat.Displayed.Instances.Slice.html
[pullbacks]: Cat.Diagram.Pullback.html
[a functor]: Cat.Functor.Pullback.html

```agda
module _ {𝒶 𝒷} (f : Hom 𝒶 𝒷) where
  base-change : Functor (Fibre E 𝒷) (Fibre E 𝒶)
  base-change .F₀ ob = has-lift f ob .x′
  base-change .F₁ {x} {y} vert = rebase f vert
```

<!--
```agda
  base-change .F-id {x} =
    sym $ has-lift.uniquev _ _ _ $ to-pathp $
      idr[] ∙ (sym $ cancel _ _ (idl′ _))

  base-change .F-∘ {x} {y} {z} f′ g′ =
    sym $ has-lift.uniquev _ _ _ $ to-pathp $
      smashr _ _
      ·· revive₁ (pulll[] (idr f) (has-lift.commutesv _ _ _))
      ·· smashl _ _
      ·· revive₁ (pullr[] (idr f) (has-lift.commutesv _ _ _))
      ·· smashr _ _
      ·· assoc[]
      ·· sym (smashl _ _)
```
-->

Moreover, this assignment is _itself_ functorial in $f$: Along the
identity morphism, it's the same thing as not changing bases at all.

```agda
module _ {𝒶} where
  private
    module FC = Cat.Reasoning (Cat[ Fibre E 𝒶 , Fibre E 𝒶 ])
    module Fa = Cat.Reasoning (Fibre E 𝒶)

  base-change-id : base-change id FC.≅ Id
```

<details>
<summary> I'll warn you in advance that this proof is not for the faint
of heart. </summary>
```agda
  base-change-id = to-natural-iso mi where
    open make-natural-iso
    mi : make-natural-iso (base-change id) Id
    mi .eta x = has-lift.lifting id x
    mi .inv x = has-lift.universalv id x id′
    mi .eta∘inv x = cancel _ _ (has-lift.commutesv _ _ _)
    mi .inv∘eta x = sym $
      has-lift.uniquev₂ id x Fa.id _ (cast[] $ idr′ _) $
      to-pathp (smashr _ _ ∙ cancel _ _ (cancell[] _ (has-lift.commutesv _ _ _)))
    mi .natural x y f = ap hom[] $ sym $
      has-lift.commutes _ _ _ _ ·· hom[]-∙ _ _ ·· liberate _
```
</details>

And similarly, composing changes of base is the same thing as changing
base along a composite.

```agda
module _ {𝒶} {𝒷} {𝒸} (f : Hom 𝒷 𝒸) (g : Hom 𝒶 𝒷) where
  private
    module FC = Cat.Reasoning (Cat[ Fibre E 𝒸 , Fibre E 𝒶 ])
    module Fa = Cat.Reasoning (Fibre E 𝒶)

  base-change-comp : base-change (f ∘ g) FC.≅ (base-change g F∘ base-change f)
```

<details>
<summary> This proof is a truly nightmarish application of universal
properties and I recommend that nobody look at it, ever. </summary>.

```agda
  base-change-comp = to-natural-iso mi where
    open make-natural-iso
    mi : make-natural-iso (base-change (f ∘ g)) (base-change g F∘ base-change f)
    mi .eta x =
      has-lift.universalv g _ $ has-lift.universal f x g (has-lift.lifting (f ∘ g) x)
    mi .inv x =
      has-lift.universalv (f ∘ g) x (has-lift.lifting f _ ∘′ has-lift.lifting g _)
    mi .eta∘inv x =
      has-lift.uniquev₂ g _ _ _
        (to-pathp $
          smashr _ _
          ·· revive₁ (pulll[] _ (has-lift.commutesv g _ _))
          ·· has-lift.uniquep₂ f _ refl refl refl _ _
            (pulll-indexr _ (has-lift.commutes f _ _ _)
            ∙ cancel _ _ (has-lift.commutesv (f ∘ g) _ _))
            refl)
        (idr′ _)
    mi .inv∘eta x =
      has-lift.uniquev₂ (f ∘ g) _ _ _
        (to-pathp $
          smashr _ _
          ·· revive₁ (pulll[] _ (has-lift.commutesv (f ∘ g) _ _))
          ·· revive₁ (pullr[] _ (has-lift.commutesv g _ _))
          ∙ cancel _ _ (has-lift.commutes f _ _ _))
        (idr′ _)
    mi .natural x y f′ =
      ap hom[] $ cartesian→weak-monic E (has-lift.cartesian g _) _ _ $
        from-pathp⁻ (pulll[] _ (has-lift.commutes g _ _ _))
        ·· smashl _ _ ·· smashl _ _
        ·· revive₁ (pullr[] _ (has-lift.commutesv g _ _ ))
        ·· (cartesian→weak-monic E (has-lift.cartesian f _) _ _ $
          whisker-r _
          ·· revive₁ (pulll[] _ (has-lift.commutesv f _ _))
          ·· smashl _ _
          ·· revive₁ (pullr[] _ (has-lift.commutes f _ _ _))
          ·· duplicate _ (ap (f ∘_) (intror (idl id))) _
          ·· revive₁ (symP (has-lift.commutesv (f ∘ g) _ _))
          ·· revive₁ (pushl[] _ (symP $ has-lift.commutes f _ _ _))
          ·· unwhisker-r _ (ap (g ∘_) (sym $ idl id))
          ·· ap (has-lift.lifting f _ ∘′_) (expandl _ _ ∙ reindex _ _))
        ∙ cancel (sym $ assoc _ _ _) _ (pushl[] _ (symP $ has-lift.commutes g _ _ _))
```
</details>
