```agda
open import Cat.Diagram.Limit.Finite
open import Cat.Diagram.Limit.Base
open import Cat.Instances.Discrete
open import Cat.Prelude

open import Data.Fin

import Cat.Reasoning as Cat

module Cat.Instances.FinSet where
```

# The category of finite sets

Throughout this page, let $n$ be a natural number and $[n]$ denote the
[standard $n$-element ordinal]. The **category of finite sets**,
$\finsets$, is the category with set of objects $\bb{N}$ the natural
numbers, with set of maps $\hom(j,k)$ the set of functions $[j] \to
[k]$. This category is not [univalent], but it is [weakly equivalent] to the
full subcategory of $\sets$ on those objects which are [merely]
isomorphic to a finite ordinal. The reason for this "skeletal"
definition is that $\finsets$ is a small category, so that presheaves on
$\finsets$ are a [Grothendieck topos].

[standard $n$-element ordinal]: Data.Fin.html
[univalent]: Cat.Univalent.html
[weakly equivalent]: Cat.Functor.Equivalence.html#between-categories
[merely]: 1Lab.HIT.Truncation.html
[Grothendieck topos]: Topoi.Base.html

```agda
FinSets : Precategory lzero lzero
FinSets .Precategory.Ob = Nat
FinSets .Precategory.Hom j k = Fin j → Fin k
FinSets .Precategory.Hom-set x y = hlevel 2
FinSets .Precategory.id x = x
FinSets .Precategory._∘_ f g x = f (g x)
FinSets .Precategory.idr f = refl
FinSets .Precategory.idl f = refl
FinSets .Precategory.assoc f g h = refl
```
