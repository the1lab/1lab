---
description: |
  Isofibrations.
---

<!--
```agda
open import Cat.Displayed.Base
open import Cat.Prelude

import Cat.Displayed.Morphism
import Cat.Morphism
```
-->

```agda
module Cat.Displayed.Isofibration where
```

<!--
```agda
private variable
  ob ℓb oe ℓe : Level
```
-->

# Isofibrations

```agda
record Isofibration {B : Precategory ob ℓb} (E : Displayed B oe ℓe) : Type (ob ⊔ ℓb ⊔ oe ⊔ ℓe) where
  no-eta-equality
  open Cat.Morphism B
  open Cat.Displayed.Morphism E
  open Displayed E
  field
    _^*_ : ∀ {a b} (x : Ob[ b ]) (u : a ≅ b) → Ob[ a ]
    iso* : ∀ {a b} (x : Ob[ b ]) (u : a ≅ b) → (x ^* u) ≅[ u ] x
```
