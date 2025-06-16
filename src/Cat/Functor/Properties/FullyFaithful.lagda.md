<!--
```agda
open import Cat.Diagram.Colimit.Coequaliser
open import Cat.Diagram.Colimit.Coproduct
open import Cat.Instances.Shape.Terminal
open import Cat.Diagram.Colimit.Initial
open import Cat.Diagram.Limit.Equaliser
open import Cat.Diagram.Limit.Terminal
open import Cat.Diagram.Limit.Product
open import Cat.Diagram.Colimit.Base
open import Cat.Diagram.Coequaliser
open import Cat.Diagram.Limit.Base
open import Cat.Functor.Kan.Unique
open import Cat.Functor.Naturality
open import Cat.Functor.Properties
open import Cat.Diagram.Coproduct
open import Cat.Diagram.Equaliser
open import Cat.Functor.Coherence
open import Cat.Diagram.Terminal
open import Cat.Functor.Kan.Base
open import Cat.Diagram.Initial
open import Cat.Diagram.Product
open import Cat.Functor.Base
open import Cat.Prelude

import Cat.Functor.Reasoning.FullyFaithful as FF
import Cat.Reasoning

open Functor
open _=>_
```
-->

```agda
module Cat.Functor.Properties.FullyFaithful
  {oc od ℓc ℓd} {C : Precategory oc ℓc} {D : Precategory od ℓd}
  (F : Functor C D) (ff : is-fully-faithful F)
  where
```

<!--
```agda
private
  module C = Cat.Reasoning C
  module D = Cat.Reasoning D
  module F = FF F ff
```
-->

# Properties of fully faithful functors

This module collects various properties of [[fully faithful functors]].

## Interaction with composition functors

If $F$ is fully faithful, then we can "unwhisker" any natural transformation
$\theta : F \circ G \To F \circ H$ to a natural transformation $F^{-1}\theta : G \To H$
whose whiskering with $F$ on the left is $\theta$. This implies that the
[[postcomposition functor]] $F \circ -$ is fully faithful.

```agda
module _ {oe ℓe} {E : Precategory oe ℓe} where
  unwhisker : ∀ {G H : Functor E C} → F F∘ G => F F∘ H → G => H
  unwhisker θ .η d = F.from (θ .η d)
  unwhisker θ .is-natural x y f = sym (F.ε-twist (sym (θ .is-natural x y f)))

  ff→postcompose-ff : is-fully-faithful (postcompose F {D = E})
  ff→postcompose-ff = is-iso→is-equiv $ iso unwhisker
    (λ _ → ext λ d → F.ε _) (λ _ → ext λ d → F.η _)
```

## Fully faithful functors reflect (co)limits {defines="ff-reflect-limits ff-reflect-colimits"}

[[Fully faithful functors]] reflect both left and right [[Kan extensions]],
hence in particular [[limits]] and [[colimits]].
Thinking of such functors as [[full subcategory]] inclusions, this means
that, if a (co)cone *entirely contained within the subcategory*
is universal in the whole category, then it is also universal in the
subcategory. The converse is *not* true: fully faithful functors do not
preserve Kan extensions in general.

<!--
```agda
module _ {oj ou hj hu} {J : Precategory oj hj} {U : Precategory ou hu} where
  open is-lan
  open is-ran
```
-->

```agda
  ff→reflects-lan
    : ∀ {p : Functor J U} {G : Functor J C}
    → reflects-lan p G F
  ff→reflects-lan lan .σ eta = unwhisker (lan .σ (nat-assoc-to (F ▸ eta)))
  ff→reflects-lan lan .σ-comm = ext λ j → F.whackl (lan .σ-comm ηₚ j)
  ff→reflects-lan lan .σ-uniq {σ' = σ'} com = ext λ u → sym $ F.adjunctl $ sym $
    lan .σ-uniq {σ' = F ▸ σ'} (ext λ j → F.expand (com ηₚ j)) ηₚ u

  ff→reflects-ran
    : ∀ {p : Functor J U} {G : Functor J C}
    → reflects-ran p G F
  ff→reflects-ran ran .σ eps = unwhisker (ran .σ (nat-assoc-from (F ▸ eps)))
  ff→reflects-ran ran .σ-comm = ext λ j → F.whackr (ran .σ-comm ηₚ j)
  ff→reflects-ran ran .σ-uniq {σ' = σ'} com = ext λ u → sym $ F.adjunctl $ sym $
    ran .σ-uniq {σ' = F ▸ σ'} (ext λ j → F.expand (com ηₚ j)) ηₚ u
```

<!--
```agda
_ = Limit
_ = Colimit
module _ {oj hj} {J : Precategory oj hj} (G : Functor J C) where
  open Limit
  open Colimit
```
-->

```agda
  ff→reflects-limit : reflects-limit F G
  ff→reflects-limit = ff→reflects-ran

  ff→reflects-colimit : reflects-colimit F G
  ff→reflects-colimit = ff→reflects-lan
```

We prove the following convenience lemma: given a `Limit`{.Agda} of
$F \circ G$ whose apex is isomorphic to $F(o)$ for some object $o : \cC$,
we can lift it to a `Limit`{.Agda} of $G$ (and similarly for
`Colimit`{.Agda}s).

```agda
  ff→reflects-Limit
    : (Lim : Limit (F F∘ G))
    → ∀ {o} → apex Lim D.≅ F.₀ o
    → Limit G
  ff→reflects-Limit Lim {o} is = to-limit (ff→reflects-limit lim) where
    eps' : F F∘ !Const o F∘ !F => F F∘ G
    eps' = nat-unassoc-from
      (Lim .eps ∘nt (!constⁿ (is .D.from) ◂ !F))

    lim : is-ran !F (F F∘ G) (F F∘ !Const o) (nat-assoc-from (F ▸ unwhisker eps'))
    lim = natural-isos→is-ran idni idni
      (!const-isoⁿ is)
      (ext λ j → D.idl _ ∙∙ (D.refl⟩∘⟨ D.eliml (Lim .Ext .F-id)) ∙∙ sym (F.ε _))
      (Lim .has-ran)

  ff→reflects-Colimit
    : (Colim : Colimit (F F∘ G))
    → ∀ {o} → coapex Colim D.≅ F.₀ o
    → Colimit G
  ff→reflects-Colimit Colim {o} is = to-colimit (ff→reflects-colimit colim) where
    eta' : F F∘ G => F F∘ !Const o F∘ !F
    eta' = nat-unassoc-to
      ((!constⁿ (is .D.to) ◂ !F) ∘nt Colim .eta)

    colim : is-lan !F (F F∘ G) (F F∘ !Const o) (nat-assoc-to (F ▸ unwhisker eta'))
    colim = natural-isos→is-lan idni idni
      (!const-isoⁿ is)
      (ext λ j → (F.eliml refl D.⟩∘⟨ D.idr _) ∙ sym (F.ε _))
      (Colim .has-lan)
```

<!--
```agda
ff→reflects-Terminal
  : (term : Terminal D)
  → ∀ {o} → term .Terminal.top D.≅ F.₀ o
  → Terminal C
ff→reflects-Terminal term is =
  Limit→Terminal C (ff→reflects-Limit _ (Terminal→Limit D term) is)

ff→reflects-Initial
  : (init : Initial D)
  → ∀ {o} → init .Initial.bot D.≅ F.₀ o
  → Initial C
ff→reflects-Initial init is =
  Colimit→Initial C (ff→reflects-Colimit _ (Initial→Colimit D init) is)

ff→reflects-Product
  : ∀ {a b} → (prod : Product D (F.₀ a) (F.₀ b))
  → ∀ {o} → prod .Product.apex D.≅ F.₀ o
  → Product C a b
ff→reflects-Product prod is =
  Limit→Product C (ff→reflects-Limit _ (Product→Limit D prod) is)

ff→reflects-Coproduct
  : ∀ {a b} → (coprod : Coproduct D (F.₀ a) (F.₀ b))
  → ∀ {o} → coprod .Coproduct.coapex D.≅ F.₀ o
  → Coproduct C a b
ff→reflects-Coproduct coprod is =
  Colimit→Coproduct C (ff→reflects-Colimit _ (Coproduct→Colimit D coprod) is)

ff→reflects-Equaliser
  : ∀ {a b} {f g : C.Hom a b} (eq : Equaliser D (F.₁ f) (F.₁ g))
  → ∀ {o} → eq .Equaliser.apex D.≅ F.₀ o
  → Equaliser C f g
ff→reflects-Equaliser eq is =
  Limit→Equaliser C (ff→reflects-Limit _ (Equaliser→Limit D eq) is)

ff→reflects-Coequaliser
  : ∀ {a b} {f g : C.Hom a b} (coeq : Coequaliser D (F.₁ f) (F.₁ g))
  → ∀ {o} → coeq .Coequaliser.coapex D.≅ F.₀ o
  → Coequaliser C f g
ff→reflects-Coequaliser coeq is =
  Colimit→Coequaliser C (ff→reflects-Colimit _ (Coequaliser→Colimit D coeq) is)
```
-->
