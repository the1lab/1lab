---
description: |
  Reasoning with modules.
---
<!--
```agda
open import Algebra.Ring.Module
open import Algebra.Group.Ab
open import Algebra.Group
open import Algebra.Ring

open import Cat.Prelude hiding (_+_)
```
-->
```agda
module Algebra.Ring.Module.Reasoning
  {ℓ ℓm} {R : Ring ℓ}
  (M : Module R ℓm)
  where
```

# Reasoning with modules

```agda
  open Module-on (M .snd) public

  Ab-group : Abelian-group ℓm
  Ab-group = (M .fst , Module-on→Abelian-group-on (M .snd))
```
