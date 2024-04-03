<!--
```agda
open import Cat.Prelude

open import Data.Fin

import Data.Nat as Nat
```
-->

```agda
module Cat.Instances.Simplex where
```

<!--
```agda
open Precategory
```
-->

# The simplex category

The simplex category, $\Delta$, is generally introduced as the category
of non-empty finite ordinals and order-preserving maps. We will, for
convenience reasons, define it _skeletally_: Rather than taking actual
finite ordinals as objects, we will use the natural numbers as ordinals,
each natural standing for the isomorphism class of ordinals of that
cardinality.

```agda
record Δ-map (n m : Nat) : Type where
  field
    map       : Fin (suc n) → Fin (suc m)
    ascending : (x y : Fin (suc n)) → x ≤ y → map x ≤ map y
```

<!--
```agda
open Δ-map

unquoteDecl H-Level-Δ-map = declare-record-hlevel 2 H-Level-Δ-map (quote Δ-map)

Δ-map-path
  : ∀ {n m : Nat} {f g : Δ-map n m}
  → (∀ x → f .map x ≡ g .map x)
  → f ≡ g
Δ-map-path p i .map x = p x i
Δ-map-path {f = f} {g} p i .ascending x y w =
  is-prop→pathp (λ j → Nat.≤-is-prop {to-nat (p x j)} {to-nat (p y j)})
    (f .ascending x y w) (g .ascending x y w) i
```
-->

```agda
Δ : Precategory lzero lzero
Δ .Ob = Nat
Δ .Hom n m = Δ-map n m
Δ .Hom-set _ _ = hlevel 2

Δ .id .map x = x
Δ .id .ascending x y p = p

Δ ._∘_ f g .map x = f .map (g .map x)
Δ ._∘_ f g .ascending x y p = f .ascending _ _ (g .ascending _ _ p)

Δ .idr f = Δ-map-path λ x → refl
Δ .idl f = Δ-map-path λ x → refl
Δ .assoc f g h = Δ-map-path λ x → refl
```
