<!--
```agda
open import 1Lab.Equiv
open import 1Lab.Path

open import Cat.Functor.Base using (module F-iso)
open import Cat.Base

import Cat.Reasoning
```
-->

```agda
module Cat.Functor.Reasoning
  {o ℓ o' ℓ'}
  {𝒞 : Precategory o ℓ} {𝒟 : Precategory o' ℓ'}
  (F : Functor 𝒞 𝒟)
  where

private
  module 𝒞 = Cat.Reasoning 𝒞
  module 𝒟 = Cat.Reasoning 𝒟
open Functor F public
open F-iso F public
```

<!--
```agda
private variable
  A B C : 𝒞.Ob
  a a' b b' c c' d : 𝒞.Hom A B
  X Y Z : 𝒟.Ob
  f g h i : 𝒟.Hom X Y
```
-->


# Reasoning combinators for functors

The combinators exposed in [category reasoning] abstract out a lot of common
algebraic manipulations, and make proofs much more concise. However, once functors
get involved, those combinators start to get unwieldy! Therefore, we have
to write some new combinators for working with functors specifically.
This module is meant to be imported qualified.

[category reasoning]: Cat.Reasoning.html

## Identity morphisms

```agda
module _ (a≡id : a ≡ 𝒞.id) where
  elim : F₁ a ≡ 𝒟.id
  elim = ap F₁ a≡id ∙ F-id

  eliml : F₁ a 𝒟.∘ f ≡ f
  eliml = 𝒟.eliml elim

  elimr : f 𝒟.∘ F₁ a ≡ f
  elimr = 𝒟.elimr elim

  intro : 𝒟.id ≡ F₁ a
  intro = sym F-id ∙ ap F₁ (sym a≡id)

  introl : f ≡ F₁ a 𝒟.∘ f
  introl = 𝒟.introl elim

  intror : f ≡ f 𝒟.∘ F₁ a
  intror = 𝒟.intror elim

module _ {X : 𝒞.Ob} {f : 𝒟.Hom (F₀ X) (F₀ X)} where

  id-equivr : (f ≡ F₁ 𝒞.id) ≃ (f ≡ 𝒟.id)
  id-equivr = ∙-post-equiv F-id

  id-equivl : (F₁ 𝒞.id ≡ f) ≃ (𝒟.id ≡ f)
  id-equivl = ∙-pre-equiv (sym F-id)

  module id-equivr = Equiv id-equivr
  module id-equivl = Equiv id-equivl
```

## Reassociations

```agda
module _ (ab≡c : a 𝒞.∘ b ≡ c) where
  collapse : F₁ a 𝒟.∘ F₁ b ≡ F₁ c
  collapse = sym (F-∘ a b) ∙ ap F₁ ab≡c

  pulll : F₁ a 𝒟.∘ (F₁ b 𝒟.∘ f) ≡ F₁ c 𝒟.∘ f
  pulll = 𝒟.pulll collapse

  pullr : (f 𝒟.∘ F₁ a) 𝒟.∘ F₁ b ≡ f 𝒟.∘ F₁ c
  pullr = 𝒟.pullr collapse

module _ (abc≡d : a 𝒞.∘ b 𝒞.∘ c ≡ d) where
  collapse3 : F₁ a 𝒟.∘ F₁ b 𝒟.∘ F₁ c ≡ F₁ d
  collapse3 = ap (F₁ a 𝒟.∘_) (sym (F-∘ b c)) ∙ collapse abc≡d

  pulll3 : F₁ a 𝒟.∘ (F₁ b 𝒟.∘ (F₁ c 𝒟.∘ f)) ≡ F₁ d 𝒟.∘ f
  pulll3 = 𝒟.pulll3 collapse3

  pullr3 : ((f 𝒟.∘ F₁ a) 𝒟.∘ F₁ b) 𝒟.∘ F₁ c ≡ f 𝒟.∘ F₁ d
  pullr3 = 𝒟.pullr3 collapse3

module _ (c≡ab : c ≡ a 𝒞.∘ b) where
  expand : F₁ c ≡ F₁ a 𝒟.∘ F₁ b
  expand = sym (collapse (sym c≡ab))

  pushl : F₁ c 𝒟.∘ f ≡ F₁ a 𝒟.∘ (F₁ b 𝒟.∘ f)
  pushl = 𝒟.pushl expand

  pushr : f 𝒟.∘ F₁ c ≡ (f 𝒟.∘ F₁ a) 𝒟.∘ F₁ b
  pushr = 𝒟.pushr expand

module _ (p : a 𝒞.∘ c ≡ b 𝒞.∘ d) where
  weave : F₁ a 𝒟.∘ F₁ c ≡ F₁ b 𝒟.∘ F₁ d
  weave = sym (F-∘ a c) ∙∙ ap F₁ p ∙∙ F-∘ b d

  extendl : F₁ a 𝒟.∘ (F₁ c 𝒟.∘ f) ≡ F₁ b 𝒟.∘ (F₁ d 𝒟.∘ f)
  extendl = 𝒟.extendl weave

  extendr : (f 𝒟.∘ F₁ a) 𝒟.∘ F₁ c ≡ (f 𝒟.∘ F₁ b) 𝒟.∘ F₁ d
  extendr = 𝒟.extendr weave

  extend-inner :
    f 𝒟.∘ F₁ a 𝒟.∘ F₁ c 𝒟.∘ g ≡ f 𝒟.∘ F₁ b 𝒟.∘ F₁ d 𝒟.∘ g
  extend-inner = 𝒟.extend-inner weave

module _ (p : a 𝒞.∘ b 𝒞.∘ c ≡ a' 𝒞.∘ b' 𝒞.∘ c') where
  weave3 : F₁ a 𝒟.∘ F₁ b 𝒟.∘ F₁ c ≡ F₁ a' 𝒟.∘ F₁ b' 𝒟.∘ F₁ c'
  weave3 = ap (_ 𝒟.∘_) (sym (F-∘ b c)) ∙∙ weave p ∙∙ ap (_ 𝒟.∘_) (F-∘ b' c')

  extendl3 : F₁ a 𝒟.∘ (F₁ b 𝒟.∘ (F₁ c 𝒟.∘ f)) ≡ F₁ a' 𝒟.∘ (F₁ b' 𝒟.∘ (F₁ c' 𝒟.∘ f))
  extendl3 = 𝒟.extendl3 weave3

  extendr3 : ((f 𝒟.∘ F₁ a) 𝒟.∘ F₁ b) 𝒟.∘ F₁ c ≡ ((f 𝒟.∘ F₁ a') 𝒟.∘ F₁ b') 𝒟.∘ F₁ c'
  extendr3 = 𝒟.extendr3 weave3

module _ (p : F₁ a 𝒟.∘ F₁ c ≡ F₁ b 𝒟.∘ F₁ d) where
  swap : F₁ (a 𝒞.∘ c) ≡ F₁ (b 𝒞.∘ d)
  swap = F-∘ a c ∙∙ p ∙∙ sym (F-∘  b d)

popl : f 𝒟.∘ F₁ a ≡ g → f 𝒟.∘ F₁ (a 𝒞.∘ b) ≡ g 𝒟.∘ F₁ b
popl p = 𝒟.pushr (F-∘ _ _) ∙ ap₂ 𝒟._∘_ p refl

popr : F₁ b 𝒟.∘ f ≡ g → F₁ (a 𝒞.∘ b) 𝒟.∘ f ≡ F₁ a 𝒟.∘ g
popr p = 𝒟.pushl (F-∘ _ _) ∙ ap₂ 𝒟._∘_ refl p

pokel : g ≡ f 𝒟.∘ F₁ a → g 𝒟.∘ F₁ b ≡ f 𝒟.∘ F₁ (a 𝒞.∘ b)
pokel p = ap₂ 𝒟._∘_ p refl ∙ 𝒟.pullr (sym (F-∘ _ _))

poker : g ≡ F₁ b 𝒟.∘ f → F₁ a 𝒟.∘ g ≡ F₁ (a 𝒞.∘ b) 𝒟.∘ f
poker p = ap₂ 𝒟._∘_ refl p ∙ 𝒟.pulll (sym (F-∘ _ _))

shufflel : f 𝒟.∘ F₁ a ≡ g 𝒟.∘ h → f 𝒟.∘ F₁ (a 𝒞.∘ b) ≡ g 𝒟.∘ h 𝒟.∘ F₁ b
shufflel p = popl p ∙ sym (𝒟.assoc _ _ _)

shuffler : F₁ b 𝒟.∘ f ≡ g 𝒟.∘ h → F₁ (a 𝒞.∘ b) 𝒟.∘ f ≡ (F₁ a 𝒟.∘ g) 𝒟.∘ h
shuffler p = popr p ∙ (𝒟.assoc _ _ _)

remover : F₁ b 𝒟.∘ f ≡ 𝒟.id → F₁ (a 𝒞.∘ b) 𝒟.∘ f ≡ F₁ a
remover p = popr p ∙ 𝒟.idr _

removel : f 𝒟.∘ F₁ a ≡ 𝒟.id → f 𝒟.∘ F₁ (a 𝒞.∘ b) ≡ F₁ b
removel p = popl p ∙ 𝒟.idl _
```

## Cancellation

```agda
module _ (inv : a 𝒞.∘ b ≡ 𝒞.id) where
  annihilate : F₁ a 𝒟.∘ F₁ b ≡ 𝒟.id
  annihilate = collapse inv ∙ F-id

  cancell : F₁ a 𝒟.∘ (F₁ b 𝒟.∘ f) ≡ f
  cancell = 𝒟.cancell annihilate

  cancelr : (f 𝒟.∘ F₁ a) 𝒟.∘ F₁ b ≡ f
  cancelr = 𝒟.cancelr annihilate

  insertl : f ≡ F₁ a 𝒟.∘ (F₁ b 𝒟.∘ f)
  insertl = 𝒟.insertl annihilate

  insertr : f ≡ (f 𝒟.∘ F₁ a) 𝒟.∘ F₁ b
  insertr = 𝒟.insertr annihilate

  cancel-inner : (f 𝒟.∘ F₁ a) 𝒟.∘ (F₁ b 𝒟.∘ g) ≡ f 𝒟.∘ g
  cancel-inner = 𝒟.cancel-inner annihilate

module _ (inv : a 𝒞.∘ b 𝒞.∘ c ≡ 𝒞.id) where
  annihilate3 : F₁ a 𝒟.∘ F₁ b 𝒟.∘ F₁ c ≡ 𝒟.id
  annihilate3 = collapse3 inv ∙ F-id

  cancell3 : F₁ a 𝒟.∘ (F₁ b 𝒟.∘ (F₁ c 𝒟.∘ f)) ≡ f
  cancell3 = 𝒟.cancell3 annihilate3

  cancelr3 : ((f 𝒟.∘ F₁ a) 𝒟.∘ F₁ b) 𝒟.∘ F₁ c ≡ f
  cancelr3 = 𝒟.cancelr3 annihilate3

  insertl3 : f ≡ F₁ a 𝒟.∘ (F₁ b 𝒟.∘ (F₁ c 𝒟.∘ f))
  insertl3 = 𝒟.insertl3 annihilate3

  insertr3 : f ≡ ((f 𝒟.∘ F₁ a) 𝒟.∘ F₁ b) 𝒟.∘ F₁ c
  insertr3 = 𝒟.insertr3 annihilate3
```

## Lenses

```agda
unpackl
  : F₁ a 𝒟.∘ F₁ b ≡ f
  → F₁ (a 𝒞.∘ b) ≡ f
unpackl p = F-∘ _ _ ∙ p

packl
  : F₁ (a 𝒞.∘ b) ≡ f
  → F₁ a 𝒟.∘ F₁ b ≡ f
packl p = sym (F-∘ _ _) ∙ p

unpackr
  : f ≡ F₁ a 𝒟.∘ F₁ b
  → f ≡ F₁ (a 𝒞.∘ b)
unpackr p = p ∙ sym (F-∘ _ _)

packr
  : f ≡ F₁ (a 𝒞.∘ b)
  → f ≡ F₁ a 𝒟.∘ F₁ b
packr p = p ∙ F-∘ _ _
```


## Notation

Writing `ap F₁ p` is somewhat clunky, so we define a bit of notation
to make it somewhat cleaner.

```agda
⟨_⟩ : a ≡ b → F₁ a ≡ F₁ b
⟨_⟩ = ap F₁
```
