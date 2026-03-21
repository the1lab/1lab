<!--
```agda
open import Cat.Instances.Product
open import Cat.Functor.Base
open import Cat.Prelude

import Cat.Functor.Reasoning as Fr
import Cat.Functor.Bifunctor as Bi
import Cat.Reasoning as Cr

open Make-bifunctor
open Precategory
open Functor
open _=>_
```
-->

```agda
module Cat.Functor.Closed where
```

<!--
```agda
private variable
  o h o₁ h₁ o₂ h₂ : Level
  B C D E : Precategory o h
  F G : Functor C D
```
-->

When taken as a [(bi)category][cat], the collection of (pre)categories
is, in a suitably weak sense, [[Cartesian closed]]: there is an
[equivalence] between the [functor categories] $[\cC \times \cD, \cE]$
and $[\cC, [\cD, \cE]]$. We do not define the full equivalence here,
leaving the natural isomorphisms aside and focusing on the inverse
functors themselves: `Curry`{.Agda} and `Uncurry`{.Agda}.

[cat]: Cat.Bi.Base.html#the-bicategory-of-categories
[equivalence]: Cat.Functor.Equivalence.html
[functor categories]: Cat.Functor.Base.html

The two conversion functions act on objects essentially in the same way
as currying and uncurrying behave on funct*ions*: the difference is that
we must properly stage the action on morphisms. Currying a functor $F :
\cC \times \cD \to \cE$ fixes a morphism $f : x \to y \in \cC$, and we
must show that $g \mapsto F(f,g)$ is natural in $g$. It follows from a
bit of calculation using the functoriality of $F$.

```agda
Curry : Functor (C ×ᶜ D) E → Bifunctor C D E
Curry {C = C} {D = D} F =
  make-bifunctor λ where
    .F₀ a x  → F.₀ (a , x)
    .lmap f  → F.₁ (f , D.id)
    .rmap g  → F.₁ (C.id , g)
    .lmap-id → F.F-id
    .rmap-id → F.F-id
    .lmap-∘ f g → ap F.₁ (refl ,ₚ sym (D.idr _)) ∙ F.F-∘ _ _
    .rmap-∘ f g → ap F.₁ (sym (C.idr _) ,ₚ refl) ∙ F.F-∘ _ _
    .lrmap  f g → Fr.weave F (C.idr _ ∙ sym (C.idl _) ,ₚ D.idl _ ∙ sym (D.idr _))
  where
    module C = Precategory C
    module D = Precategory D
    module F = Functor F

```

```agda
open _=>_
evF : Bifunctor (Cat[ C , D ]) C D
evF {C = C} {D = D} = make-bifunctor record where
  module C = Cr C
  module D = Cr D
  F₀ F x = F .F₀ x

  lmap     f = f .η _
  lmap-id    = refl
  lmap-∘ f g = refl

  rmap    {a = F}   f = F .F₁ f
  rmap-id {a = F}     = F .F-id
  rmap-∘  {a = F} _ _ = F .F-∘ _ _

  lrmap f g = f .is-natural _ _ _

eval-at : ⌞ C ⌟ → Functor Cat[ C , D ] D
eval-at {C = C} {D = D} = Bi.Left evF
```
