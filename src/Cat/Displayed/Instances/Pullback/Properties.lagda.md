<!--
```agda
open import Cat.Displayed.Base
open import Cat.Displayed.Cartesian
open import Cat.Displayed.Functor
open import Cat.Displayed.Instances.Pullback

open import Cat.Prelude

import Cat.Reasoning
import Cat.Displayed.Reasoning
```
-->

```agda
module Cat.Displayed.Instances.Pullback.Properties where
```

# Properties of pullbacks of displayed categories

```agda
module _
  {oa ℓa ob ℓb oe ℓe}
  {A : Precategory oa ℓa}
  {B : Precategory ob ℓb}
  {K : Functor A B}
  {L : Functor A B}
  {E : Displayed B oe ℓe}
  (fib : Cartesian-fibration E)
  (σ : K => L)
  where
  private
    module A = Cat.Reasoning A
    module B = Cat.Reasoning B
    module K = Functor K
    module L = Functor L
    open Displayed E
    open Cat.Displayed.Reasoning E
    open Cartesian-fibration fib
    open _=>_

  Func : Vertical-functor (Change-of-base L E) (Change-of-base K E)
  Func = vert where
    open Vertical-functor

    vert : Vertical-functor (Change-of-base L E) (Change-of-base K E)
    vert .F₀′ {a} x′ = has-lift.x′ (σ .η a) x′
    vert .F₁′ {a} {b} {x′} {y′} f′ =
      has-lift.universal′ (σ .η b) _
        (σ .is-natural a b x′)
        (f′ ∘′ has-lift.lifting (σ .η a) y′)
    vert .F-id′ = symP $
      has-lift.uniquep (σ .η _) _ _ refl (σ .is-natural _ _ _) _
        (unwrapr _
        ∙[] idr′ _
        ∙[] symP (idl′ _)
        ∙[] wrapl _)
    vert .F-∘′ {f′ = f′} {g′ = g′} =
      symP $ has-lift.uniquep (σ .η _) _ _ refl (σ .is-natural _ _ _) _ $
        unwrapr _
        ∙[ σ .is-natural _ _ _ ]
           pulll[] _ (has-lift.commutesp (σ .η _) _ (σ .is-natural _ _ _) _)
        ∙[ ap₂ B._∘_ refl (sym $ K.F-∘ _ _) ∙ σ .is-natural _ _ _ ]
          pullr[] _ (has-lift.commutesp (σ .η _) _ (σ .is-natural _ _ _) _)
        ∙[ B.pullr (σ .is-natural _ _ _) ∙ B.pulll (sym $ L.F-∘ _ _) ]
          assoc′ _ _ _
        ∙[ B.pulll (sym $ L.F-∘ _ _) ]
          wrapl _
```

