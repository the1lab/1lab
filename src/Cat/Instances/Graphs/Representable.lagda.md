<!--
```agda
open import Cat.Instances.Graphs.Lift
open import Cat.Instances.Graphs
open import Cat.Prelude

open import Data.Bool.Base
```
-->

```agda
module Cat.Instances.Graphs.Representable where
```

<!--
```agda
open Graph-hom
open Graph
private variable
  o o' ℓ ℓ' : Level
  G H : Graph o ℓ
```
-->

# Representable graphs

We define the **representable** [[graphs]], those which correspond to
[[representable functors]] under the equivalence between the category of
graphs and presheaves over the [[parallel arrows]] diagram.

::: {.definition #node-graph}
The **node graph** is the [[graph]] with a single node and no edges.
:::

```agda
Nodeᴳ : Graph lzero lzero
Nodeᴳ .Node     = ⊤
Nodeᴳ .Edge _ _ = ⊥
Nodeᴳ .Node-set = hlevel 2
Nodeᴳ .Edge-set = hlevel 2
```

<!--
```agda
data Edgeᵉ : Bool → Bool → Type where
  inc : Edgeᵉ false true

instance
  H-Level-Edgeᵉ : ∀ {x y n} → H-Level (Edgeᵉ x y) (suc n)
  H-Level-Edgeᵉ = prop-instance λ where inc inc → refl
```
-->

::: {.definition #edge-graph}
The **edge graph** is the [[graph]] with a single edge, and the
necessary pair of nodes to support it.
:::

```agda
Edgeᴳ : Graph lzero lzero
Edgeᴳ .Node = Bool
Edgeᴳ .Edge = Edgeᵉ
Edgeᴳ .Node-set = hlevel 2
Edgeᴳ .Edge-set = hlevel 2
```

The edge graph *must* have a pair of nodes because our definition of
graphs defines edges only *over* the source and target; alternatively,
in a fibred presentation, it is because edges must have an image under
the source and target maps, and these can be distinct (and so must be in
a representing object). Thinking about the equivalence with presheaves,
these two nodes correspond to the two maps in the parallel arrows
diagram.

As the names imply, morphisms from these "shape" graphs correspond to
picking out the corresponding structure in some other graph: either a
node or an edge.

```agda
node→hom : G .Node → Graph-hom Nodeᴳ G
node→hom x .node tt = x
node→hom x .edge ()

edge→hom : ∀ {x y} → G .Edge x y → Graph-hom Edgeᴳ G
edge→hom {x = x} {y} e .node false = x
edge→hom {x = x} {y} e .node true  = y
edge→hom e .edge inc = e
```

## Monomorphisms of graphs

As an application of these graphs, we can show that [[monomorphisms]] of
graphs are componentwise [[embeddings]] of the node and edge [[sets]].
This will be useful in constructing the [[subgraph classifier]]. In both
cases, this is proved by evaluating the monomorphism at morphisms which
represent the nodes and edges we are comparing.

```agda
module _ {m : Graphs.Hom G H} (monic : Graphs.is-monic m) where
  is-monic→node-is-embedding : is-embedding (m .node)
  is-monic→node-is-embedding = injective→is-embedding! λ p → monic {c = Liftᴳ _ _ Nodeᴳ}
    record { node = _ ; edge = λ () }
    record { node = _ ; edge = λ () }
    (Graph-hom-path (λ _ → p) (λ ()))
    ·ₚ lift tt

  is-monic→edge-is-embedding : ∀ {x y} → is-embedding (m .edge {x} {y})
  is-monic→edge-is-embedding = injective→is-embedding! λ {x} {y} p →
    let
      a = monic {c = Liftᴳ _ _ Edgeᴳ} (edge→hom x ∘ᴳ lowerᴳ) (edge→hom y ∘ᴳ lowerᴳ) $ ext λ where
        .node true  → refl
        .node false → refl
        .edge (lift inc) → p

      px = ap (λ m → m .node (lift false)) a
      py = ap (λ m → m .node (lift true)) a

      b : subst₂ (G .Edge) px py x ≡ y
      b = from-pathp (ap (λ m → m .edge (lift inc)) a)
    in sym (transport-refl _)
     ∙ subst₂ (λ α β → subst₂ (G .Edge) α β x ≡ y) prop! prop! b
```
