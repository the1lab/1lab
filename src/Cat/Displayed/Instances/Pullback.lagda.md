```agda
open import Cat.Instances.Functor
open import Cat.Displayed.Base
open import Cat.Prelude

import Cat.Displayed.Reasoning as Dr

module
  Cat.Displayed.Instances.Pullback
    {o ℓ o′ ℓ′ o′′ ℓ′′}
    {X : Precategory o ℓ} {B : Precategory o′ ℓ′}
    (F : Functor X B)
    (E : Displayed B o′′ ℓ′′)
  where
```

# Pullback of a displayed category

If we have a category $E$ displayed over $B$, then a functor $F : X \to
B$ defines a (contravariant) "change-of-base" action, reasulting in a
category $F^*(E)$ displayed over $X$.

<!--
```agda
private
  module X = Precategory X
  module B = Precategory B
  module E = Displayed E

open Functor F
open Displayed
open Dr E
```
-->

The reason for this contravariance is the following: A category
displayed over $X$ must have a $X$-indexed space of objects; But our
category $E$ has a $B$-indexed space of objects. Fortunately, $F$ gives
us a map $x \mapsto F_0(x)$ which allows us to convert our $X$-indices
to $B$-indices. The same goes for indexing the displayed $\hom$-sets.

```agda
Change-of-base : Displayed X o′′ ℓ′′
Change-of-base .Ob[_] x      = E.Ob[ F₀ x ]
Change-of-base .Hom[_] f x y = E.Hom[ F₁ f ] x y
Change-of-base .Hom[_]-set f = E.Hom[ F₁ f ]-set
Change-of-base .id′          = hom[ sym F-id ] E.id′
Change-of-base ._∘′_ f′ g′   = hom[ sym (F-∘ _ _) ] (f′ E.∘′ g′)
```

Proving that the pullback $F^*(E)$ is indeed a displayed category is a
bit trickier than it might seem --- we must adjust the identity and
composites in $E$ by the paths witnessing functoriality of $F$, and this
really throws a spanner in the works --- but the handy [displayed
category reasoning combinators][dr] are here to help.

[dr]: Cat.Displayed.Reasoning.html

```agda
Change-of-base .idr′ {f = f} f′ = to-pathp $
  hom[ ap F₁ (X.idr f) ] (hom[ F-∘ _ _ ]⁻ (f′ E.∘′ hom[ F-id ]⁻ _)) ≡⟨ hom[]⟩⟨ smashr _ _ ⟩
  hom[ ap F₁ (X.idr f) ] (hom[] (f′ E.∘′ E.id′))                    ≡⟨ hom[]-∙ _ _ ⟩
  hom[] (f′ E.∘′ E.id′)                                             ≡⟨ cancel _ _ (E.idr′ f′) ⟩
  f′                                                                ∎

Change-of-base .idl′ f′ = to-pathp $
  hom[ ap F₁ (X.idl _) ] (hom[ F-∘ _ _ ]⁻ (hom[ F-id ]⁻ _ E.∘′ f′)) ≡⟨ hom[]⟩⟨ smashl _ _ ⟩
  hom[ ap F₁ (X.idl _) ] (hom[] (E.id′ E.∘′ f′))                    ≡⟨ hom[]-∙ _ _ ⟩
  hom[] (E.id′ E.∘′ f′)                                             ≡⟨ cancel _ _ (E.idl′ f′) ⟩
  f′                                                                ∎

Change-of-base .assoc′ f′ g′ h′ = to-pathp $
  hom[ ap F₁ _ ] (hom[ F-∘ _ _ ]⁻ (f′ E.∘′ hom[ F-∘ _ _ ]⁻ (g′ E.∘′ h′)))   ≡⟨ hom[]⟩⟨ smashr _ _ ⟩
  hom[] (hom[] (f′ E.∘′ g′ E.∘′ h′))                                        ≡⟨ hom[]-∙ _ _ ⟩
  hom[ (ap (_ B.∘_) _ ∙ sym (F-∘ _ _)) ∙ ap F₁ _ ] (f′ E.∘′ g′ E.∘′ h′)     ≡⟨ weave _ _ _ (E.assoc′ f′ g′ h′) ⟩
  hom[ ap (B._∘ _) (sym (F-∘ _ _)) ∙ sym (F-∘ _ _) ] ((f′ E.∘′ g′) E.∘′ h′) ≡˘⟨ smashl _ _ ⟩
  hom[ sym (F-∘ _ _) ] (hom[ sym (F-∘ _ _) ] (f′ E.∘′ g′) E.∘′ h′)          ∎
```
