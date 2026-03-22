<!--
```agda
open import Cat.Diagram.Colimit.Base
open import Cat.Functor.Bifunctor
open import Cat.Instances.Product
open import Cat.Instances.Twisted
open import Cat.Functor.Constant
open import Cat.Diagram.Initial
open import Cat.Diagram.Coend
open import Cat.Functor.Base
open import Cat.Prelude

import Cat.Functor.Reasoning as F-r
import Cat.Reasoning as Cat
```
-->

```agda
module Cat.Diagram.Coend.Formula
  {o ℓ o' ℓ'} {C : Precategory o ℓ} {D : Precategory o' ℓ'}
  where
```

<!--
```agda
open Cowedge
```
-->

# Computing coends

Using the [twisted arrow category] as a mediating notion, we show how to
compute [coends] as ordinary [colimits]. The calculation is actually a
bit more straightforward than it might seem at first. The first thing we
note is that any functor $F : C\op \times C \to D$ generates a functor
from the twisted arrow category of $\cC\op$:

$$
\rm{Tw}(\cC\op)\op \xto{\pi_t} C\op \times C \xto{F} D
$$

[twisted arrow category]: Cat.Instances.Twisted.html
[coends]: Cat.Diagram.Coend.html
[colimits]: Cat.Diagram.Colimit.Base.html

This is the fundamental part of our theorem: The twisted arrow category,
in a sense, "classifies cowedges", in that cocones under $F\pi_t$ (the
composite above) are the same thing as cowedges from $F$. The proof is
entirely shuffling some data around, but the
commutativity/extranaturality conditions need to be massaged a bit.
Check it out, it's not too long:

```agda
module _ (F : Bifunctor (C ^op) C D) where
  private
    module C = Cat C
    module D = Cat D
    module F = Bifunctor F
    open _=>_
    open Twist

  cocone→cowedge : ∀ {x} → twistᵒᵖ F => Const x → Cowedge F
  cocone→cowedge eta .nadir = _
  cocone→cowedge eta .ψ c = eta .η ((c , c) , C.id)
  cocone→cowedge eta .extranatural f =
    ap₂ D._∘_ refl (D.introl F.lmap-id)
    ∙ eta .is-natural _ _ (twist _ _ (C.eliml (C.idl _)))
    ∙ sym (eta .is-natural _ _ (twist _ _ (C.cancelr (C.idl _))))
    ∙ ap₂ D._∘_ refl (D.elimr F.rmap-id)

  cowedge→cocone : (W : Cowedge F) → twistᵒᵖ F => Const (W .nadir)
  cowedge→cocone W .η ((c , c') , f) = W .ψ c D.∘ F.rmap f
  cowedge→cocone W .is-natural ((a , b) , f) ((x , y) , g) h =
    (ψ W x D.∘ (x F.▶ g)) D.∘ (before h F.◀ y) D.∘ (a F.▶ after h) ≡⟨ D.pushl (W .extranatural g) ⟩
    ψ W y D.∘ (g F.◀ y) D.∘ (before h F.◀ y) D.∘ (a F.▶ after h)   ≡⟨ ap₂ D._∘_ refl (D.pulll (sym (F.lmap-∘ _ _)) ∙ F.lrmap _ _) ⟩
    ψ W y D.∘ (y F.▶ after h) D.∘ (before h C.∘ g F.◀ b)           ≡⟨ D.extendl (W .extranatural _) ⟩
    ψ W b D.∘ (after h F.◀ b) D.∘ (before h C.∘ g F.◀ b)           ≡⟨ ap₂ D._∘_ refl (sym (F.lmap-∘ _ _) ∙ ap F.lmap (h .commutes)) ⟩
    ψ W b D.∘ (f F.◀ b)                                            ≡˘⟨ W .extranatural _ ⟩
    ψ W a D.∘ (a F.▶ f)                                            ≡⟨ D.introl refl ⟩
    D.id D.∘ ψ W a D.∘ (a F.▶ f)                                   ∎
```

We can now extend that correspondence to calculating coends as certain
colimits: $\cD$ has a coend for $F$ if it has a colimit for $F\pi_t$.

```agda
  colimit→coend : Colimit (twistᵒᵖ F) → Coend F
  colimit→coend colim = coend where
    open Coend
    module W = Colimit colim
    coend : Coend F
    coend .cowedge = cocone→cowedge W.cocone
    coend .factor W' = W.universal
      (cowedge→cocone W' .η)
      (λ f → cowedge→cocone W' .is-natural _ _ f ∙ D.idl _)
    coend .commutes {W = W'} = W.factors _ _ ∙ D.elimr F.rmap-id
    coend .unique {W = W'} comm = W.unique _ _ _ $ λ j → sym $
      W' .extranatural _
      ∙∙ D.pushl (sym comm)
      ∙∙ ap₂ D._∘_ refl (ap₂ D._∘_ refl (D.intror F.rmap-id)
        ∙ W.commutes (twist _ _ (C.cancelr (C.idl _))))


  cocomplete→coend : is-cocomplete (o ⊔ ℓ) ℓ D → Coend F
  cocomplete→coend colim = colimit→coend (colim _)

  module cocomplete→∫ (cocomp : is-cocomplete (o ⊔ ℓ) ℓ D) where
    open Coend (cocomplete→coend cocomp) public
```
