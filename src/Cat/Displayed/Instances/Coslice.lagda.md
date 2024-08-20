---
description: |
  Coslice categories.
---
<!--
```agda
open import Cat.Instances.Coslice
open import Cat.Displayed.Base
open import Cat.Prelude

import Cat.Reasoning
```
-->
```agda
module Cat.Displayed.Instances.Coslice {o ℓ} (B : Precategory o ℓ) where
```

<!--
```agda
open Cat.Reasoning B
open Displayed
open \-Obj
```
-->

```agda
record
  Coslice-hom
    {x y} (f : Hom x y)
    (px : \-Obj {C = B} x) (py : \-Obj {C = B} y)
    : Type ℓ
  where
  constructor coslice-hom
  field
    to      : Hom (px .codomain) (py .codomain)
    commute : to ∘ px .map ≡ py .map ∘ f

open Coslice-hom
```

<!--
```agda
module _ {x y} {f g : Hom x y} {px : \-Obj x} {py : \-Obj y}
         {f' : Coslice-hom f px py} {g' : Coslice-hom g px py} where

  Coslice-pathp : (p : f ≡ g) → (f' .to ≡ g' .to) → PathP (λ i → Coslice-hom (p i) px py) f' g'
  Coslice-pathp p p' i .to = p' i
  Coslice-pathp p p' i .commute =
    is-prop→pathp
      (λ i → Hom-set _ _ (p' i ∘ px .map) (py .map ∘ (p i)))
      (f' .commute)
      (g' .commute)
      i

Coslice-path
  : ∀ {x y} {f : Hom x y} {px : \-Obj x} {py : \-Obj y}
  → {f' g' : Coslice-hom f px py}
  → (f' .to ≡ g' .to)
  → f' ≡ g'
Coslice-path = Coslice-pathp refl

unquoteDecl H-Level-Coslice-hom = declare-record-hlevel 2 H-Level-Coslice-hom (quote Coslice-hom)
```
-->

```agda
Coslices : Displayed B (o ⊔ ℓ) ℓ
Coslices .Ob[_] x = \-Obj {C = B} x
Coslices .Hom[_] = Coslice-hom
Coslices .Hom[_]-set _ _ _ = hlevel 2
Coslices .id' .to = id
Coslices .id' .commute = id-comm-sym
Coslices ._∘'_ f g .to = f .to ∘ g .to
Coslices ._∘'_ f g .commute = pullr (g .commute) ∙ extendl (f .commute)
Coslices .idr' _ = Coslice-pathp (idr _) (idr _)
Coslices .idl' _ = Coslice-pathp (idl _) (idl _)
Coslices .assoc' _ _ _ = Coslice-pathp (assoc _ _ _) (assoc _ _ _)
```
