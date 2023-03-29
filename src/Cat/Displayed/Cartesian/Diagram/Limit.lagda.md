```agda
open import Cat.Diagram.Limit.Base
open import Cat.Displayed.Base
open import Cat.Displayed.Fibre
open import Cat.Displayed.Cartesian
open import Cat.Prelude

import Cat.Displayed.Cartesian.Indexing

module Cat.Displayed.Cartesian.Diagram.Limit where
```

# Fibrewise Limits

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

We say that a [fibration] has **fibrewise limits** of some diagram
if each [fibre] has a [limit] of the diagram, and those limits are
preserved by [reindexing functors].

[fibration]: Cat.Displayed.Cartesian.html
[fibre]: Cat.Displayed.Fibre.html
[limit]: Cat.Diagram.Limit.Base.html
[reindexing functors]: Cat.Displayed.Cartesian.Indexing.html

```agda
  record Fibrewise-limit
    {o'' ℓ''} {J : Precategory o'' ℓ''}
    (Dia : ∀ x → Functor J (Fibre E x))
    : Type (o ⊔ o' ⊔ o'' ⊔ ℓ ⊔ ℓ' ⊔ ℓ'') where
    no-eta-equality
    field
      fibrewise-limit : ∀ x → Limit (Dia x)
      reindex-preserves
        : ∀ {x y} (f : B.Hom x y)
        → preserves-limit (base-change f) (Dia y)
```
