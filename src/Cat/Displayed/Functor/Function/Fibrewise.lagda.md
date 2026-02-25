<!--
```agda
open import 1Lab.Function.Fibrewise

open import Cat.Displayed.Reasoning as Dr
open import Cat.Displayed.Functor
open import Cat.Displayed.Base
open import Cat.Reasoning as Cr
open import Cat.Prelude
```
-->

```agda
module Cat.Displayed.Functor.Function.Fibrewise 
  {oa ℓa oe ℓe ob ℓb of ℓf}
  {A : Precategory oa ℓa} {B : Precategory ob ℓb} {F : Functor A B}
  {ℰ : Displayed A oe ℓe} {ℱ : Displayed B of ℓf} (F' : Displayed-functor F ℰ ℱ)
  where
```

# Displayed functors give functions over

The data `F₀'`{.Agda} and `F₁`{.Agda} of a [[displayed functor]] are
naturally repackaged as [[functions over|function over]] the 
corresponding data of the base functor.

<!--
```agda
private
  module ℰ = Dr ℰ
  module ℱ = Dr ℱ 

open Functor F
open Displayed-functor F'
```
-->

```agda
F₀-over : ℰ.Ob[_] -[ F₀ ]→ ℱ.Ob[_]
F₀-over a b p a' = subst ℱ.Ob[_] p (F₀' a')

F₁-over 
  : ∀ {a b} {a' : ℰ.Ob[ a ]} {b' : ℰ.Ob[ b ]} 
  → (λ f → ℰ.Hom[ f ] a' b') -[ F₁ ]→ λ g → ℱ.Hom[ g ] (F₀' a') (F₀' b')

F₁-over {a' = a'} {b' = b'} f g p f' = ℱ.hom[ p ] (F₁' f')
```
