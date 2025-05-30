---
description: |
  The initial quasigroup.
---
<!--
```agda
open import Algebra.Quasigroup

open import Cat.Diagram.Initial
open import Cat.Displayed.Total
open import Cat.Prelude hiding (_/_)
```
-->

```agda
module Algebra.Quasigroup.Instances.Initial where
```

# The initial quasigroup {defines="initial-quasigroup empty-quasigroup"}

The empty type trivially forms a [[quasigroup]].

<!--
```agda
private variable
  ℓ : Level

open ∫Hom
```
-->

```agda
Empty-quasigroup : ∀ {ℓ} → Quasigroup ℓ
Empty-quasigroup = to-quasigroup ⊥-quasigroup where
  open make-quasigroup

  ⊥-quasigroup : make-quasigroup (Lift _ ⊥)
  ⊥-quasigroup .quasigroup-is-set = hlevel 2
  ⊥-quasigroup ._⋆_ ()
  ⊥-quasigroup ._⧵_ ()
  ⊥-quasigroup ._/_ ()
  ⊥-quasigroup ./-invl ()
  ⊥-quasigroup ./-invr ()
  ⊥-quasigroup .⧵-invr ()
  ⊥-quasigroup .⧵-invl ()
```

Moreover, the empty quasigroup is an [[initial object]] in the category
of quasigroups, as there is a unique function out of the empty type.

```agda
Empty-quasigroup-is-initial : is-initial (Quasigroups ℓ) Empty-quasigroup
Empty-quasigroup-is-initial A .centre .fst ()
Empty-quasigroup-is-initial A .centre .snd .is-quasigroup-hom.pres-⋆ ()
Empty-quasigroup-is-initial A .paths f = ext λ ()

Initial-quasigroup : Initial (Quasigroups ℓ)
Initial-quasigroup .Initial.bot = Empty-quasigroup
Initial-quasigroup .Initial.has⊥ = Empty-quasigroup-is-initial
```

In fact, the empty quasigroup is a [[strict initial object]].

```agda
Initial-quasigroup-is-strict
  : is-strict-initial (Quasigroups ℓ) Initial-quasigroup
Initial-quasigroup-is-strict =
  make-is-strict-initial (Quasigroups _) Initial-quasigroup $ λ A f → ext λ a →
  absurd (Lift.lower (f · a))
```

<!--
```agda
Strict-initial-quasigroup : Strict-initial (Quasigroups ℓ)
Strict-initial-quasigroup .Strict-initial.initial =
  Initial-quasigroup
Strict-initial-quasigroup .Strict-initial.has-is-strict =
  Initial-quasigroup-is-strict
```
-->
