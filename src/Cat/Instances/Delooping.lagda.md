<!--
```agda
open import Algebra.Monoid

open import Cat.Prelude
```
-->

```agda
module Cat.Instances.Delooping where
```

<!--
```agda
private variable
  ℓ : Level
```
-->

Given a monoid $M$, we build a pointed precategory $\B{M}$, where the
endomorphism monoid of the point recovers $M$.

```agda
B : ∀ {ℓ} {M : Type ℓ} → Monoid-on M → Precategory lzero ℓ
B {M = M} mm = r where
  module mm = Monoid-on mm
  open Precategory

  r : Precategory _ _
  r .Ob = ⊤
  r .Hom _ _ = M
  r .Hom-set _ _ = mm.has-is-set
  r .Precategory.id = mm.identity
  r .Precategory._∘_ = mm._⋆_
  r .idr _ = mm.idr
  r .idl _ = mm.idl
  r .assoc _ _ _ = mm.associative
```
