```agda
open import Cat.Prelude

open import Data.Bool

module Cat.Instances.Shape.Pair where
```

# The "pair of objects" category

The pair of objects category is the category with 2 objects,
and only identity morphisms. It is the shape of [product] and
[coproduct] diagrams.

[product]: Cat.Diagram.Product.html
[coproduct]: Cat.Diagram.Coproduct.html

```agda
·· : Precategory lzero lzero
·· = precat where
  open Precategory
  precat : Precategory _ _
  precat .Ob = Bool

  precat .Hom false false = ⊤
  precat .Hom false true = ⊥
  precat .Hom true false = ⊥
  precat .Hom true true = ⊤
```

<!--
````
  precat .Hom-set false false = hlevel 2
  precat .Hom-set false true = hlevel 2
  precat .Hom-set true false = hlevel 2
  precat .Hom-set true true = hlevel 2

  precat .id {x = false} = tt
  precat .id {x = true} = tt

  precat ._∘_ {false} {false} {false} _ _ = tt
  precat ._∘_ {true} {true} {true} _ _ = tt

  precat .idr {false} {false} _ = refl
  precat .idr {true} {true} _ = refl

  precat .idl {false} {false} _ = refl
  precat .idl {true} {true} _ = refl

  precat .assoc {false} {false} {false} {false} _ _ _ = refl
  precat .assoc {true} {true} {true} {true} _ _ _ = refl
```
-->

```agda
module _ {o ℓ} {C : Precategory o ℓ} where
  open Precategory C
  open Functor
   
  2-objects→pair-diagram : ∀ (a b : Ob) → Functor ·· C
  2-objects→pair-diagram a b = funct where
    funct : Functor _ _
    funct .F₀ false = a
    funct .F₀ true = b
    funct .F₁ {false} {false} _ = id
    funct .F₁ {true} {true} _ = id
    funct .F-id {false} = refl
    funct .F-id {true} = refl
    funct .F-∘ {false} {false} {false} _ _ = sym (idl _)
    funct .F-∘ {true} {true} {true} _ _ = sym (idl _)
```
