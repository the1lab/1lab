<!--
```agda
open import Cat.Displayed.Reasoning as Dr
open import Cat.Displayed.Morphism as Dm
open import Cat.Functor.Properties
open import Cat.Displayed.Functor
open import Cat.Displayed.Base
open import Cat.Reasoning as Cr
open import Cat.Prelude
```
-->

```agda
module Cat.Displayed.Functor.Properties 
  {oa ℓa ob ℓb oe ℓe of ℓf}
  {A : Precategory oa ℓa} {B : Precategory ob ℓb}
  {ℰ : Displayed A oe ℓe} {ℱ : Displayed B of ℓf}
  where
```

<!--
```agda
private
  module A = Cr A
  module ℰ where 
    open Dr ℰ public
    open Dm ℰ public
  module ℱ where
    open Dr ℱ public
    open Dm ℱ public
  variable
    F : Functor A B

open Functor
open Displayed-functor
```
-->

# Properties of displayed functors

This module mirrors the corresponding one for [ordinary functors]
by defining the corresponding classes of [[displayed functors|displayed functor]].

[ordinary functors]: Cat.Functor.Properties.html

:::{.definition #fully-displayed-functor}
A displayed functor is **fully displayed** when its action on hom-sets 
_over_ any morphism is surjective:

```agda
is-full' : Displayed-functor F ℰ ℱ → Type _
is-full' F' = ∀ {x y f} {x' : ℰ.Ob[ x ]} {y' : ℰ.Ob[ y ]}
  → is-surjective {A = ℰ.Hom[ f ] x' y'} (₁' F')
```
:::

:::{.definition #faithfully-displayed-functor}
A displayed functor is **faithfully displayed** when its action on
hom-sets _over_ any morphism is injective:

```agda
is-faithful' : Displayed-functor F ℰ ℱ → Type _
is-faithful' F' = ∀ {x y f} {x' : ℰ.Ob[ x ]} {y' : ℰ.Ob[ y ]}
  → injective {A = ℰ.Hom[ f ] x' y'} (₁' F')
```
:::

## Fully faithfully displayed functors {defines="fully-faithfully-displayed-functor fully-faithfully-functor"}

A displayed functor is **fully faithfully displayed** when its action on
hom-sets _over_ any morphism is an equivalence.

```agda
is-ff' : Displayed-functor F ℰ ℱ → Type _
is-ff' F' = ∀ {x y f} {x' : ℰ.Ob[ x ]} {y' : ℰ.Ob[ y ]} 
  →  is-equiv {A = ℰ.Hom[ f ] x' y'} (₁' F')

ff'→faithful' : {F' : Displayed-functor F ℰ ℱ} → is-ff' F' → is-faithful' F'
ff'→faithful' {F' = F'} has-is-ff = Equiv.injective (₁' F' , has-is-ff)

ff'→full' : {F' : Displayed-functor F ℰ ℱ} → is-ff' F' → is-full' F'
ff'→full' has-is-ff f' = inc (equiv→inverse has-is-ff f' , equiv→counit has-is-ff f')

full'+faithful'→ff' : {F' : Displayed-functor F ℰ ℱ}
  → is-full' F' → is-faithful' F' → is-ff' F'
full'+faithful'→ff' {F = F} {F' = F'} has-is-full has-is-faithful .is-eqv = p where
  img-is-prop : ∀ {x y f} {x' : ℰ.Ob[ x ]} {y' : ℰ.Ob[ y ]} f'
    → is-prop (fibre {A = ℰ.Hom[ f ] x' y'} (₁' F') f')
  img-is-prop f' (g' , p) (h' , q) = Σ-prop-path 
    (λ x → ℱ.Hom[ ₁ F _ ]-set (₀' F' _) (₀' F' _) (₁' F' x) f') 
    (has-is-faithful (p ∙ sym q))

  p : ∀ {x y f} {x' : ℰ.Ob[ x ]} {y' : ℰ.Ob[ y ]} f' 
    → is-contr (fibre {A = ℰ.Hom[ f ] x' y'} (₁' F') f')
  p f' .centre = ∥-∥-elim (λ _ → img-is-prop f') (λ x → x) (has-is-full f')
  p f' .paths = img-is-prop f' _
```

## Essential fibres

One way to generalize [[essential fibres|essential fibre]] is as 
follows:

```agda
Essential-fibre[_] 
  : ∀ {b} ((a , f) : Essential-fibre F b) → Displayed-functor F ℰ ℱ 
  → ℱ.Ob[ b ] → Type _
Essential-fibre[_] {b = b} (a , f) F' b' = Σ ℰ.Ob[ a ] λ a' → ₀' F' a' ℱ.≅[ f ] b'

is-split-eso[_] : is-split-eso F → Displayed-functor F ℰ ℱ → Type _
is-split-eso[ eso ] F' = ∀ {b} b' → Essential-fibre[ eso b ] F' b'
```