---
description: We establish that right adjoints preserve limits.
---
<!--
```agda
open import Cat.Diagram.Pullback.Properties
open import Cat.Instances.Shape.Terminal
open import Cat.Diagram.Colimit.Base
open import Cat.Diagram.Limit.Finite
open import Cat.Functor.Adjoint.Kan
open import Cat.Diagram.Limit.Base
open import Cat.Diagram.Terminal
open import Cat.Functor.Kan.Base
open import Cat.Functor.Adjoint
open import Cat.Prelude

import Cat.Functor.Reasoning as Func
import Cat.Reasoning as Cat
```
-->

```agda
module Cat.Functor.Adjoint.Continuous where
```

<!--
```agda
module _
    {o o' ℓ ℓ'} {C : Precategory o ℓ} {D : Precategory o' ℓ'}
    {L : Functor C D} {R : Functor D C}
    (L⊣R : L ⊣ R)
  where
  private
    module L = Func L
    module R = Func R
    module C = Cat C
    module D = Cat D
    module adj = _⊣_ L⊣R
    open _=>_
```
-->

# Continuity of adjoints {defines="rapl right-adjoints-preserve-limits lapc left-adjoints-preserve-colimits"}

We prove that every functor $R : \cD \to \cC$ admitting a [[left
adjoint]] $L \dashv R$ preserves every limit which exists in $\cD$. We
then instantiate this theorem to the "canonical" shapes of limit:
[[terminal objects]], [[products]], [[pullback]] and [[equalisers]].

This follows directly from the fact that [[adjoints preserve Kan
extensions]].


```agda
  right-adjoint-is-continuous
    : ∀ {os ℓs} → is-continuous os ℓs R
  right-adjoint-is-continuous = right-adjoint→preserves-ran L⊣R

  left-adjoint-is-cocontinuous
    : ∀ {os ℓs} → is-cocontinuous os ℓs L
  left-adjoint-is-cocontinuous = left-adjoint→preserves-lan L⊣R

  module _ {od ℓd} {J : Precategory od ℓd} where
    right-adjoint-limit : ∀ {F : Functor J D} → Limit F → Limit (R F∘ F)
    right-adjoint-limit lim =
      to-limit (right-adjoint-is-continuous (Limit.has-limit lim))

    left-adjoint-colimit : ∀ {F : Functor J C} → Colimit F → Colimit (L F∘ F)
    left-adjoint-colimit colim =
      to-colimit (left-adjoint-is-cocontinuous (Colimit.has-colimit colim))
```

## Concrete limits

We now show that adjoint functors preserve "concrete limits". We could
show this using general abstract nonsense, but we can avoid transports
if we do it by hand.

<!--
```agda
  open import Cat.Diagram.Equaliser
  open import Cat.Diagram.Pullback
  open import Cat.Diagram.Product
```
-->

```agda
  right-adjoint→is-product
    : ∀ {x a b} {p1 : D.Hom x a} {p2 : D.Hom x b}
    → is-product D p1 p2
    → is-product C (R.₁ p1) (R.₁ p2)
  right-adjoint→is-product {x = x} {a} {b} {p1} {p2} d-prod = c-prod where
    open is-product

    c-prod : is-product C (R.₁ p1) (R.₁ p2)
    c-prod .⟨_,_⟩ f g =
      L-adjunct L⊣R (d-prod .⟨_,_⟩ (R-adjunct L⊣R f) (R-adjunct L⊣R g))
    c-prod .π₁∘⟨⟩ =
      R.pulll (d-prod .π₁∘⟨⟩) ∙ L-R-adjunct L⊣R _
    c-prod .π₂∘⟨⟩ =
      R.pulll (d-prod .π₂∘⟨⟩) ∙ L-R-adjunct L⊣R _
    c-prod .unique {other = other} p q =
      sym (L-R-adjunct L⊣R other)
      ∙ ap (L-adjunct L⊣R)
           (d-prod .unique (R-adjunct-ap L⊣R p) (R-adjunct-ap L⊣R q))

  right-adjoint→is-pullback
    : ∀ {p x y z}
    → {p1 : D.Hom p x} {f : D.Hom x z} {p2 : D.Hom p y} {g : D.Hom y z}
    → is-pullback D p1 f p2 g
    → is-pullback C (R.₁ p1) (R.₁ f) (R.₁ p2) (R.₁ g)
  right-adjoint→is-pullback {p1 = p1} {f} {p2} {g} d-pb = c-pb where
    open is-pullback

    c-pb : is-pullback C (R.₁ p1) (R.₁ f) (R.₁ p2) (R.₁ g)
    c-pb .square = R.weave (d-pb .square)
    c-pb .universal sq =
      L-adjunct L⊣R (d-pb .universal (R-adjunct-square L⊣R sq))
    c-pb .p₁∘universal =
      R.pulll (d-pb .p₁∘universal) ∙ L-R-adjunct L⊣R _
    c-pb .p₂∘universal =
      R.pulll (d-pb .p₂∘universal) ∙ L-R-adjunct L⊣R _
    c-pb .unique {_} {p₁'} {p₂'} {sq} {other} p q =
      sym (L-R-adjunct L⊣R other)
      ∙ ap (L-adjunct L⊣R)
           (d-pb .unique (R-adjunct-ap L⊣R p) (R-adjunct-ap L⊣R q))

  right-adjoint→is-equaliser
    : ∀ {e a b} {f g : D.Hom a b} {equ : D.Hom e a}
    → is-equaliser D f g equ
    → is-equaliser C (R.₁ f) (R.₁ g) (R.₁ equ)
  right-adjoint→is-equaliser {f = f} {g} {equ} d-equal = c-equal where
    open is-equaliser

    c-equal : is-equaliser C (R.₁ f) (R.₁ g) (R.₁ equ)
    c-equal .equal = R.weave (d-equal .equal)
    c-equal .universal sq =
      L-adjunct L⊣R (d-equal .universal (R-adjunct-square L⊣R sq))
    c-equal .factors =
      R.pulll (d-equal .factors) ∙ L-R-adjunct L⊣R _
    c-equal .unique p =
      sym (L-R-adjunct L⊣R _)
      ∙ ap (L-adjunct L⊣R)
           (d-equal .unique (R-adjunct-ap L⊣R p))

  right-adjoint→terminal
    : ∀ {x} → is-terminal D x → is-terminal C (R.₀ x)
  {-# INLINE right-adjoint→terminal #-}
  right-adjoint→terminal term = record
    { ! = L-adjunct L⊣R !
    ; !-unique = λ h → sym $ Equiv.adjunctr (_ , L-adjunct-is-equiv L⊣R) (sym (!-unique _))
    } where open is-terminal term

  right-adjoint→lex : is-lex R
  right-adjoint→lex .is-lex.pres-⊤ =
    right-adjoint→terminal
  right-adjoint→lex .is-lex.pres-pullback {f = f} {g = g} pb =
    right-adjoint→is-pullback pb
```
