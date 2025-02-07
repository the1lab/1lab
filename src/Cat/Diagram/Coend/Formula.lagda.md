<!--
```agda
open import Cat.Diagram.Colimit.Base
open import Cat.Instances.Product
open import Cat.Instances.Twisted
open import Cat.Functor.Constant
open import Cat.Diagram.Initial
open import Cat.Diagram.Coend
open import Cat.Prelude

import Cat.Functor.Bifunctor as Bifunctor
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
module _ (F : Functor (C ^op ×ᶜ C) D) where
  private
    module C = Cat C
    module D = Cat D
    module F = F-r F
    open _=>_
    open Twist
    open Bifunctor

  cocone→cowedge : ∀ {x} → twistᵒᵖ F => Const x → Cowedge F
  cocone→cowedge eta .nadir = _
  cocone→cowedge eta .ψ c = eta .η ((c , c) , C.id)
  cocone→cowedge eta .extranatural f =
    eta .is-natural _ _ (twist _ _ (C.eliml (C.idl _)))
    ∙ (sym $ eta .is-natural _ _ (twist _ _ (C.cancelr (C.idl _))))

  cowedge→cocone : (W : Cowedge F) → twistᵒᵖ F => Const (W .nadir)
  cowedge→cocone W .η ((c , c') , f) = W .ψ c D.∘ second F f
  cowedge→cocone W .is-natural ((a , b) , f) ((x , y) , g) h =
    (W .ψ x D.∘ F.F₁ (C.id , g)) D.∘ F.F₁ (_ , _)                           ≡⟨ W .extranatural g D.⟩∘⟨refl ⟩
    (W .ψ y D.∘ F.F₁ (g , C.id)) D.∘ F.F₁ (h .before , h .after)            ≡⟨ D.pullr (F.weave (C.introl refl ,ₚ refl)) ⟩
    W .ψ y D.∘ ((F.F₁ (h .before C.∘ g , C.id)) D.∘ F.F₁ (C.id , h .after)) ≡⟨ D.extendl (sym (W .extranatural _)) ⟩
    (W .ψ a D.∘ (F.F₁ (C.id , h .before C.∘ g) D.∘ F.F₁ (C.id , h .after))) ≡⟨ D.refl⟩∘⟨ sym (Bifunctor.second∘second F) ∙ ap (Bifunctor.second F) (h .commutes) ⟩
    W .ψ a D.∘ F.F₁ (C.id , f)                                              ≡⟨ sym (D.idl _) ⟩
    D.id D.∘ W .ψ a D.∘ F.F₁ (C.id , f) ∎
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
    coend .factor W' =
      W.universal
        (cowedge→cocone W' .η)
        (λ f → cowedge→cocone W' .is-natural _ _ f ∙ D.idl _)
    coend .commutes {W = W'} =
      W.factors _ _ ∙ D.elimr (Bifunctor.second-id F)
    coend .unique {W = W'} comm =
      W.unique _ _ _ $ λ j →
        sym $
          W' .extranatural _
          ·· D.pushl (sym comm)
          ·· (D.refl⟩∘⟨ (W.commutes (twist _ _ (C.cancelr (C.idl _)))))

  cocomplete→coend : is-cocomplete (o ⊔ ℓ) ℓ D → Coend F
  cocomplete→coend colim = colimit→coend (colim _)

  module cocomplete→∫ (cocomp : is-cocomplete (o ⊔ ℓ) ℓ D) where
    open Coend (cocomplete→coend cocomp) public
```
