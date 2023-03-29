```agda
open import Cat.Diagram.Product
open import Cat.Diagram.Product.Functor
open import Cat.Displayed.Base
open import Cat.Displayed.Fibre
open import Cat.Displayed.Cartesian
open import Cat.Prelude

import Cat.Displayed.Cartesian.Indexing

module Cat.Displayed.Cartesian.Diagram.Product where

```

<!--
```agda
module _ 
  {o ℓ o' ℓ'} {B : Precategory o ℓ} {E : Displayed B o' ℓ'}
  (fib : Cartesian-fibration E)
  where
  private
    module B = Precategory B
    module E = Displayed E
    open Cat.Displayed.Cartesian.Indexing E fib
```
-->

# Fibrewise Products

We say that a [fibration] has **fibrewise products** if each [fibre] has
[products], and those products are preserved by [reindexing functors].
Fibrewise products are a general case of [fibrewise limits]; we define
them separately to make things easier to work with.

[fibration]: Cat.Displayed.Cartesian.html
[fibre]: Cat.Displayed.Fibre.html
[products]: Cat.Diagram.Product.html
[reindexing functors]: Cat.Displayed.Cartesian.Indexing.html
[fibrewise limits]: Cat.Displayed.Cartesian.Diagram.Limit.html

```agda
  record Fibrewise-products : Type (o ⊔ o' ⊔ ℓ ⊔ ℓ') where
    no-eta-equality
    field
      fibrewise-product : ∀ x → has-products (Fibre E x)
      reindex-preserves : ∀ {x y} (f : B.Hom x y) → preserves-products (base-change f)
```
