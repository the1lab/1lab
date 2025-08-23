<!--
```agda
open import Cat.Instances.Graphs
open import Cat.Prelude
```
-->

```agda
module Cat.Instances.Graphs.Lift where
```

# Lifting graphs

<!--
```agda
open Graph-hom
open Graph
private variable
  o o' ℓ ℓ' : Level
  G H : Graph o ℓ
```
-->

This page defines a technical construction: we can lift a [[graph]] to
have both its nodes and edges live in a higher universe level. This is
analogous to [lifting categories across universes].

[lifting categories across universes]: Cat.Instances.Lift.html

```agda
Liftᴳ : ∀ o' ℓ' → Graph o ℓ → Graph (o ⊔ o') (ℓ ⊔ ℓ')
Liftᴳ o' ℓ' G .Node                   = Lift o' (G .Node)
Liftᴳ o' ℓ' G .Edge (lift x) (lift y) = Lift ℓ' (G .Edge x y)
Liftᴳ o' ℓ' G .Node-set = hlevel 2
Liftᴳ o' ℓ' G .Edge-set = hlevel 2

lowerᴳ : Graph-hom (Liftᴳ o' ℓ' G) G
lowerᴳ .node = lower
lowerᴳ .edge = lower

liftᴳ : Graph-hom G (Liftᴳ o' ℓ' G)
liftᴳ .node = lift
liftᴳ .edge = lift
```
