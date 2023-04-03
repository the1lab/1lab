```agda
open import Cat.Displayed.Cocartesian
open import Cat.Instances.Functor
open import Cat.Displayed.Fibre
open import Cat.Displayed.Base
open import Cat.Prelude

import Cat.Displayed.Reasoning
import Cat.Reasoning

module Cat.Displayed.Cocartesian.Indexing
  {o ℓ o′ ℓ′} {ℬ : Precategory o ℓ}
  (ℰ : Displayed ℬ o′ ℓ′)
  (opfibration : Cocartesian-fibration ℰ)
  where
```

<!--
```agda
open Cat.Reasoning ℬ
open Displayed ℰ
open Cat.Displayed.Reasoning ℰ
open Cocartesian-fibration opfibration
open Functor
```
-->

# Opreindexing for Cocartesian fibrations

[Opfibrations] are dual to [fibrations], so they inherit the ability
to [reindex along morphisms in the base]. However, this reindexing is
*covariant* for opfibrations, whereas it is *contravariant* for
fibrations.

[Opfibrations]: Cat.Displayed.Cocartesian.html
[fibrations]: Cat.Displayed.Cartesian.html
[reindex along morphisms in the base] Cat.Displayed.Cartesian.Indexing.html

This difference in variance gives opfibrations a distinct character.
Reindexing in fibrations can be thought of a sort of restriction map.
This can be seen clearly with [the canonical self-indexing], where the
reindexing functors are given by [pullbacks]. On the other hand,
opreindexing can be thought of as an extension map. We can again use the
the canonical self-indexing as our example: opreindexing is given by
postcomposition, which extends families over $X$ to families over $Y$ by
adding in empty fibres.

[the canonical self-indexing]: Cat.Displayed.Instances.Slice.html
[pullbacks]: Cat.Diagram.Pullback.html

```agda
cobase-change : ∀ {x y} (f : Hom x y) → Functor (Fibre ℰ x) (Fibre ℰ y)
cobase-change f .F₀ ob = has-lift.y′ f ob
cobase-change f .F₁ v .base = id
cobase-change f .F₁ v .is-id = refl
cobase-change f .F₁ v .vert =
  has-lift.universal′ f _ (idl _ ∙ intror (v .is-id))
    (has-lift.lifting f _ ∘′ v .vert)
```

<!--
```agda
cobase-change f .F-id =
  Fibre-hom-path _ _ refl $ sym $
  has-lift.unique _ _ _ $
  from-pathp⁻ (idl′ _)
  ∙ sym (revive₁ (idr′ _) ∙ reindex _ _)
cobase-change f .F-∘ g h =
  Fibre-hom-path _ _ (sym (idr id)) $ symP $
  has-lift.uniquep f _ (eliml (idl _) ∙ intror (eliml (g .is-id) ∙ h .is-id)) (idr id)
  (idl _ ∙ intror (eliml (g .is-id) ∙ h .is-id)) _ $ to-pathp $
    revive₁ (pullr[] (idl _ ∙ intror (h .is-id)) (has-lift.commutesp f _ _ _))
    ·· revive₁ (pulll[] (idl _ ∙ intror (g .is-id)) (has-lift.commutesp f _ _ _))
    ·· sym assoc[]
    ∙ liberate refl
```
-->
