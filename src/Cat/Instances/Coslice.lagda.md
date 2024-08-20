---
description: |
  Coslice categories
---
<!--
```agda
open import Cat.Prelude

import Cat.Reasoning
```
-->
```agda
module Cat.Instances.Coslice where
```

# Coslice categories {defines="coslice-category"}

<!--
```agda
private variable
  o ℓ o' ℓ' : Level
open Functor
open _=>_

module _ {o ℓ} {C : Precategory o ℓ} where
  private
    module C = Cat.Reasoning C
    variable a b c : C.Ob
```
-->

```agda
  record \-Obj (c : C.Ob) : Type (o ⊔ ℓ) where
    constructor cut
    field
      {codomain} : C.Ob
      map      : C.Hom c codomain

  open \-Obj
```

```agda
  record \-Hom (a b : \-Obj c) : Type ℓ where
    no-eta-equality
    private
      module a = \-Obj a
      module b = \-Obj b
    field
      map      : C.Hom a.codomain b.codomain
      commutes : map C.∘ a.map ≡ b.map

  open \-Hom
```

<!--
```agda
  \-Hom-pathp
    : ∀ {c a a' b b'} (p : a ≡ a') (q : b ≡ b')
    → {x : \-Hom {c = c} a b} {y : \-Hom a' b'}
    → PathP (λ i → C.Hom (p i .codomain) (q i .codomain))
        (x .map) (y .map)
    → PathP (λ i → \-Hom (p i) (q i)) x y
  \-Hom-pathp p q {x} {y} r = path where
    path : PathP (λ i → \-Hom (p i) (q i))  x y
    path i .map = r i
    path i .commutes =
      is-prop→pathp
        (λ i → C.Hom-set _ (q i .codomain) (r i C.∘ p i .map) (q i .map))
        (x .commutes) (y .commutes) i

  \-Hom-path : ∀ {c a b} {x y : \-Hom {c = c} a b}
             → x .map ≡ y .map
             → x ≡ y
  \-Hom-path = \-Hom-pathp refl refl

  instance
    Extensional-\-Hom
      : ∀ {c a b ℓ} ⦃ sa : Extensional (C.Hom (\-Obj.codomain a) (\-Obj.codomain b)) ℓ ⦄
      → Extensional (\-Hom {c = c} a b) ℓ
    Extensional-\-Hom ⦃ sa ⦄ = injection→extensional! \-Hom-path sa


unquoteDecl H-Level-\-Hom = declare-record-hlevel 2 H-Level-\-Hom (quote \-Hom)
```
-->

```agda
Coslice : (C : Precategory o ℓ) → ⌞ C ⌟ → Precategory _ _
Coslice C c = precat where
  module C = Cat.Reasoning C
  open Precategory
  open \-Hom
  open \-Obj

  precat : Precategory _ _
  precat .Ob = \-Obj {C = C} c
  precat .Hom = \-Hom
  precat .Hom-set _ _ = hlevel 2
  precat .id .map = C.id
  precat .id .commutes = C.idl _
  precat ._∘_ f g .map = f .map C.∘ g .map
  precat ._∘_ f g .commutes = C.pullr (g .commutes) ∙ f .commutes
  precat .idr _ = ext (C.idr _)
  precat .idl _ = ext (C.idl _)
  precat .assoc _ _ _ = ext (C.assoc _ _ _)
```
