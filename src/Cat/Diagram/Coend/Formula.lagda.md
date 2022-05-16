```agda
open import Cat.Diagram.Colimit.Base
open import Cat.Instances.Product
open import Cat.Instances.Twisted
open import Cat.Diagram.Initial
open import Cat.Diagram.Coend
open import Cat.Prelude

import Cat.Functor.Bifunctor as Bifunctor
import Cat.Functor.Reasoning as F-r
import Cat.Reasoning as Cat

module Cat.Diagram.Coend.Formula
  {o ℓ o′ ℓ′} {C : Precategory o ℓ} {D : Precategory o′ ℓ′}
  where
```

<!--
```agda
open Cocone-hom
open Cowedge
open Cocone
```
-->

# Computing coends

Using the [twisted arrow category] as a mediating notion, we show how to
compute [coends] as ordinary [colimits]. The calculation is actually a
bit more straightforward than it might seem at first. The first thing we
note is that any functor $F : C\op \times C \to D$ generates a functor
from thw twisted arrow category of $\ca{C}\op$:

$$
\id{Tw}(\ca{C}\op)\op \xto{\pi_t} C\op \times C \xto{F} D
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

  cocone→cowedge : Cocone (twistᵒᵖ F) → Cowedge F
  cocone→cowedge x .nadir = x .coapex
  cocone→cowedge x .ψ c = x .ψ ((c , c) , C.id)
  cocone→cowedge x .extranatural f =
    x .ψ (_ , C.id) D.∘ Bifunctor.second F f ≡⟨ x .commutes (record { commutes = C.eliml (C.idl C.id) }) ⟩
    x .ψ (_ , f)                             ≡˘⟨ x .commutes (record { commutes = C.cancelr (C.idl C.id) }) ⟩
    x .ψ (_ , C.id) D.∘ Bifunctor.first F f  ∎

  cowedge→cocone : Cowedge F → Cocone (twistᵒᵖ F)
  cowedge→cocone W .coapex = W .nadir
  cowedge→cocone W .ψ ((c , c′) , f) = W .ψ c D.∘ Bifunctor.second F f
  cowedge→cocone W .commutes {(a , b) , f} {(x , y) , g} h =
    (W .ψ x D.∘ Bifunctor.second F g) D.∘ F.₁ (_ , _)                                           ≡⟨ W .extranatural g D.⟩∘⟨refl ⟩
    (W .ψ y D.∘ Bifunctor.first F g) D.∘ F.₁ (_ , _)                                            ≡⟨ D.pullr (F.weave (Σ-pathp (C.introl refl) refl)) ⟩
    W .ψ y D.∘ Bifunctor.first F (Twist.before h C.∘ g) D.∘ Bifunctor.second F (Twist.after h)  ≡⟨ D.extendl (sym (W .extranatural _)) ⟩
    W .ψ a D.∘ Bifunctor.second F (Twist.before h C.∘ g) D.∘ Bifunctor.second F (Twist.after h) ≡⟨ D.refl⟩∘⟨ sym (Bifunctor.second∘second F) ∙ ap (Bifunctor.second F) (h .Twist.commutes) ⟩
    W .ψ a D.∘ Bifunctor.second F f                                                             ∎
```

We can now extend that correspondence to calculating coends as certain
colimits: $\ca{D}$ has a coend for $F$ if it has a colimit for $F\pi_t$.

```agda
  colimit→coend : Colimit (twistᵒᵖ F) → Coend F
  colimit→coend colim = coend where
    open Coend
    module W = Initial colim
    coend : Coend F

    coend .Coend.cowedge = cocone→cowedge (colim .Initial.bot)
    coend .Coend.factor W′ = W.¡ {x = cowedge→cocone W′} .hom
    coend .Coend.commutes = W.¡ .commutes _ ∙ D.elimr F.F-id
    coend .Coend.unique {W = W} {g = g} comm =
      ap hom ⊙ sym $ W.¡-unique $ cocone-hom _ λ o → sym $ square (o .snd) where
      square : ∀ {a b} (f : C.Hom b a) → _
      square {a} {b} f =
        W .ψ a D.∘ Bifunctor.second F f                   ≡⟨ W .extranatural f ⟩
        W .ψ b D.∘ Bifunctor.first F f                    ≡⟨ D.pushl (sym comm) ⟩
        g D.∘ W.bot .ψ (_ , C.id) D.∘ Bifunctor.first F f ≡⟨ D.refl⟩∘⟨ W.bot .commutes (record { before = f ; after = C.id ; commutes = C.cancelr (C.idl _) }) ⟩
        g D.∘ W.bot .ψ (_ , f)                            ∎

  cocomplete→coend : is-cocomplete (o ⊔ ℓ) ℓ D → Coend F
  cocomplete→coend colim = colimit→coend (colim _)

  module cocomplete→∫ (cocomp : is-cocomplete (o ⊔ ℓ) ℓ D) where
    open Coend (cocomplete→coend cocomp) public
```
