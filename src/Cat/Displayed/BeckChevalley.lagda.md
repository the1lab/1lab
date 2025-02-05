---
description: |
  Beck-Chevalley conditions.
---
<!--
```agda
open import Cat.Displayed.Cocartesian
open import Cat.Displayed.Cartesian
open import Cat.Displayed.Base
open import Cat.Prelude
```
-->
```agda
module Cat.Displayed.BeckChevalley where
```

# Beck-Chevalley conditions

<!--
```agda
module _
  {o ℓ o' ℓ'}
  {B : Precategory o ℓ}
  (E : Displayed B o' ℓ')
  where
  open Precategory B
  open Displayed E
```
-->

```agda
  record cocartesian-beck-chevalley
    {a b c d : Ob}
    (f : Hom b d) (g : Hom a b) (h : Hom c d) (k : Hom a c)
    (p : f ∘ g ≡ h ∘ k)
    : Type (o ⊔ ℓ ⊔ o' ⊔ ℓ') where
    no-eta-equality
    field
      cocart-stable
        : {a' : Ob[ a ]} {b' : Ob[ b ]} {c' : Ob[ c ]} {d' : Ob[ d ]}
        → {f' : Hom[ f ] b' d'} {g' : Hom[ g ] a' b'}
        → {h' : Hom[ h ] c' d'} {k' : Hom[ k ] a' c'}
        → f' ∘' g' ≡[ p ] h' ∘' k'
        → is-cocartesian E f f' → is-cartesian E g g'
        → is-cartesian E h h' → is-cocartesian E k k'

```

```agda
  record cartesian-beck-chevalley
    {a b c d : Ob}
    (f : Hom b d) (g : Hom a b) (h : Hom c d) (k : Hom a c)
    (p : f ∘ g ≡ h ∘ k)
    : Type (o ⊔ ℓ ⊔ o' ⊔ ℓ') where
    no-eta-equality
    field
      cart-stable
        : {a' : Ob[ a ]} {b' : Ob[ b ]} {c' : Ob[ c ]} {d' : Ob[ d ]}
        → {f' : Hom[ f ] b' d'} {g' : Hom[ g ] a' b'}
        → {h' : Hom[ h ] c' d'} {k' : Hom[ k ] a' c'}
        → f' ∘' g' ≡[ p ] h' ∘' k'
        → is-cocartesian E f f' → is-cartesian E g g'
        → is-cocartesian E k k' → is-cartesian E h h'
```
