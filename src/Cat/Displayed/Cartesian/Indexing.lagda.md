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
open Displayed E
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
  base-change .F₀ ob = has-lift.x′ f ob
  base-change .F₁ {x} {y} v .base = id
  base-change .F₁ {x} {y} v .is-id = refl
  base-change .F₁ {x} {y} v .vert =
    has-lift.universal′ f _ (idr _ ∙ introl (v .is-id))
      (v .vert ∘′ has-lift.lifting f _)
```

<!--
```agda
  base-change .F-id = Fibre-hom-path E 𝒶 refl $ sym $
    has-lift.unique _ _ _ $
      from-pathp⁻ (idr′ _)
      ∙ sym (revive₁ (idl′ _) ∙ reindex _ _)
  base-change .F-∘ g h = Fibre-hom-path E _ (sym (idl id)) $
    symP $ has-lift.uniquep _ _
      (elimr (idr _) ∙ introl (elimr (h .is-id) ∙ g .is-id)) (idl id) _ _
       $ to-pathp (revive₁ (pulll[] (idr _ ∙ introl (g .is-id)) (has-lift.commutesp f _ _ _))
      ·· revive₁ (pullr[] (idr _ ∙ introl (h .is-id)) (has-lift.commutesp f _ _ _))
      ·· assoc[] ∙ liberate refl)
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
    mi .eta x = from-vert _ (has-lift.lifting id x)
    mi .inv x = from-vert _ (has-lift.universal′ id x (idl _) id′)
    mi .eta∘inv x =
      Fibre-hom-path _ _ (idl _) $
      has-lift.commutesp _ _ _ _
    mi .inv∘eta x =
      Fibre-hom-path _ _ (idr _) $
      has-lift.uniquep₂ id x (idl _ ∙ idl _ ) _ _ _ _
        (to-pathp $ cancel _ _ (cancell[] (idl _) (has-lift.commutesp _ _ _ _)))
        (idr′ _) 
    mi .natural x y f =
      Fibre-hom-path _ _ (ap₂ _∘_ (f .is-id) refl) $
      to-pathp⁻ $ sym $
      cancel _ (idr _ ∙ introl (f .is-id)) (has-lift.commutesp _ _ _ _)
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
      from-vert _ $
      has-lift.universalv g _ (has-lift.universal f x g (has-lift.lifting (f ∘ g) x))
    mi .inv x =
      from-vert _ $
      has-lift.universalv (f ∘ g) x (has-lift.lifting f _ ∘′ has-lift.lifting g _)
    mi .eta∘inv x =
      Fibre-hom-path _ _ (idr _) $
      has-lift.uniquep₂ _ _ (elimr (idl _)) _ _ _ _
        (to-pathp $
          revive₁ (pulll[] _ (has-lift.commutesv g _ _))
          ∙ has-lift.uniquep₂ f x _ _ refl _ _
              (whisker-r _ ∙ revive₁ (pulll[] _ (has-lift.commutes _ _ _ _))
              ∙ cancel _ _ (has-lift.commutesv _ _ _))
              refl)
        (idr′ _)
    mi .inv∘eta x =
      Fibre-hom-path _ _ (idr _) $
      has-lift.uniquep₂ _ _ (elimr (idr _)) _ _ _ _
        (to-pathp $
          revive₁ (pulll[] _ (has-lift.commutesv _ _ _))
          ∙ revive₁ (pullr[] _ (has-lift.commutesv _ _ _))
          ∙ cancel _ _ (has-lift.commutes _ _ _ _))
        (idr′ _)
    mi .natural x y f' =
      Fibre-hom-path _ _ _ $
      cartesian→weak-monic E (has-lift.cartesian g _) _ _ $
      to-pathp $
      revive₁ (pulll[] _ (has-lift.commutes _ _ _ _))
      ∙ smashl _ _ 
      ∙ revive₁ (pullr[] _ (has-lift.commutesv g _ _))
      ∙ (cartesian→weak-monic E (has-lift.cartesian f _) _ _ $
          whisker-r _
          ∙ revive₁ (pulll[] _ (has-lift.commutes f _ _ _))
          ∙ smashl _ _
          ∙ revive₁ (pullr[] _ (has-lift.commutes f _ _ _))
          ∙ revive₁ (symP (has-lift.commutesp (f ∘ g) _ _ _))
          ∙ revive₁ (pushl[] _ (sym $ has-lift.commutes f _ _ _))
          ∙ unwhisker-r _ (ap₂ _∘_ refl (sym (idl _)))
          ∙ ap (has-lift.lifting f _ ∘′_) (expandl _ _))
      ∙ cancel _ _ (pushl[] _ (sym (has-lift.commutes g _ _ _)))
       
```
</details>
