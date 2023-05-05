<!--
```agda
open import Cat.Displayed.Base
open import Cat.Displayed.Functor
open import Cat.Prelude

import Cat.Reasoning
import Cat.Displayed.Reasoning
```
-->

```agda
module Cat.Displayed.Functor.Vertical.Reasoning
  {ob ℓb oe ℓe of ℓf}
  {B : Precategory ob ℓb}
  {ℰ : Displayed B oe ℓe} {ℱ : Displayed B of ℓf}
  (F : Vertical-functor ℰ ℱ)
  where
```

# Reasoning Combinators for Vertical Functors

This module provides versions of the [functor reasoning combinators][func]
that have been adapted to work with vertical functors.

[func]: Cat.Functor.Reasoning.html

<!--
```agda
open Cat.Reasoning B
private
  module ℰ = Cat.Displayed.Reasoning ℰ
  module ℱ = Cat.Displayed.Reasoning ℱ

open Vertical-functor F public
```
-->

```agda
F-∘[]
  : ∀ {x y z x′ y′ z′} {f : Hom y z} {g : Hom x y} {h : Hom x z}
  → {p : f ∘ g ≡ h}
  → (f′ : ℰ.Hom[ f ] y′ z′) (g′ : ℰ.Hom[ g ] x′ y′)
  → F₁′ (ℰ.hom[ p ] (f′ ℰ.∘′ g′)) ≡ ℱ.hom[ p ] (F₁′ f′ ℱ.∘′ F₁′ g′)
F-∘[] {x′ = x′} {z′ = z′} {p = p} f′ g′ i =
  comp (λ j → ℱ.Hom[ p j ] (F₀′ x′) (F₀′ z′)) (∂ i) λ where
    j (i = i0) →
      F₁′ (transp (λ i → ℰ.Hom[ p (i ∧ j) ] x′ z′) (~ j) (f′ ℰ.∘′ g′))
    j (i = i1) →
      transp (λ i → ℱ.Hom[ p (i ∧ j) ] (F₀′ x′) (F₀′ z′)) (~ j)
        (F₁′ f′ ℱ.∘′ F₁′ g′) 
    j (j = i0) → F-∘′ {f′ = f′} {g′ = g′} i
```

```agda
collapse′
  : ∀ {x y z x′ y′ z′} {f : Hom y z} {g : Hom x y} {h : Hom x z}
  → {f′ : ℰ.Hom[ f ] y′ z′} {g′ : ℰ.Hom[ g ] x′ y′}  {h′ : ℰ.Hom[ h ] x′ z′}
  → {p : f ∘ g ≡ h}
  → f′ ℰ.∘′ g′ ℰ.≡[ p ] h′
  → F₁′ f′ ℱ.∘′ F₁′ g′ ℱ.≡[ p ] F₁′ h′
collapse′ q = ℱ.cast[] (symP F-∘′ ℱ.∙[] (λ i → F₁′ (q i)))
```
