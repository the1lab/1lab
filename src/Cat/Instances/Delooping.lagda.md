<!--
```agda
open import Algebra.Monoid

open import Cat.Instances.Localisation
open import Cat.Connected
open import Cat.Prelude

open is-connected-cat
open Precategory
```
-->

```agda
module Cat.Instances.Delooping where
```

# The delooping of a monoid {defines="delooping-category delooping-of-a-monoid"}

<!--
```agda
private variable
  ℓ : Level
```
-->

Given a monoid $M$, we build a pointed, [[connected|connected category]]
precategory $\B{M}$, where the endomorphism monoid of the point recovers $M$.

```agda
module _ {ℓ} {M : Type ℓ} (mm : Monoid-on M) where
  module mm = Monoid-on mm

  B : Precategory lzero ℓ
  B .Ob = ⊤
  B .Hom _ _ = M
  B .Hom-set _ _ = mm.has-is-set
  B .Precategory.id = mm.identity
  B .Precategory._∘_ = mm._⋆_
  B .idr _ = mm.idr
  B .idl _ = mm.idl
  B .assoc _ _ _ = mm.associative

  B-is-connected : is-connected-cat B
  B-is-connected .point      = inc tt
  B-is-connected .zigzag _ _ = inc []
```
