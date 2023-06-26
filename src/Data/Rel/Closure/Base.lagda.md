<!--
```agda
open import 1Lab.Prelude
open import Data.Sum

open import Data.Rel.Base

import Data.Nat as Nat
import Data.Nat.Order as Nat
```
-->

```agda
module Data.Rel.Closure.Base where
```

<!--
```agda
private variable
  ℓ ℓ' ℓ'' : Level
  A B X : Type ℓ
  R R' S : A → A → Type ℓ
```
-->

# Closures of relations

A **closure operator** $-^{+}$ on relations takes a relation $R$ on a type
$A$ to a new relation $R^{+}$ on $A$, where $R^{+}$ is the smallest
relation containing $R$ that satisfies some property.

Intuitively, the closure of a relation should enjoy the following properties:
- If $R \subseteq S$, then $R^{+} \subseteq S^{+}$.
- $R \subseteq R^{+}$
- $(R^{+})^{+} \subseteq R^{+}$, as closing $R$ under a property twice shouldn't
  add any more elements.

This ends up forming a [monad], though we do not define a closure operator as
such due to annoying size restrictions.

[monad]: Cat.Diagram.Monad.html

```agda
record is-rel-closure
  (K : ∀ {ℓ ℓ'} {A : Type ℓ} → Rel A A ℓ' → Rel A A (ℓ ⊔ ℓ'))
  : Typeω where
  field
    monotone : R ⊆r S → K R ⊆r K S
    extensive : R ⊆r K R
    closed : K (K R) ⊆r K R
    has-prop : is-prop-rel (K R)
```

Closure, monotonicity, and extensivity combine to give idempotence
of the closure operator.

```agda
  idempotent : K (K R) ≡ K R
  idempotent =
    prop-rel-ext has-prop has-prop
      closed
      (monotone extensive)
```

We can also derive an extension operator using the normal formulation
for monads.

```agda
  extend : ∀ {R S : Rel A A ℓ} → S ⊆r K R → K S ⊆r K R
  extend p kr = closed (monotone p kr)
```

We can leverage this to see that if $R \subseteq S \subseteq K R$, then
$K R = K S$.

```agda
  ⊆+⊆-clo→≡ : ∀ {R S : Rel A A ℓ} → R ⊆r S → S ⊆r K R → K R ≡ K S
  ⊆+⊆-clo→≡ p q =
    prop-rel-ext has-prop has-prop (monotone p) (extend q)
```
