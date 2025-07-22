<!--
```agda
open import Cat.Instances.Graphs.Limits
open import Cat.Diagram.Exponential
open import Cat.Instances.Graphs
open import Cat.Prelude

open Cartesian-closed
open is-exponential
open Exponential
open Graph-hom
open Graph
```
-->

```agda
module Cat.Instances.Graphs.Exponentials where
```

<!--
```agda
private variable
  o ℓ o' ℓ' : Level
  X Y Z : Graph o ℓ
```
-->

# Exponential graphs

The [[exponential objects]] $H^G$ in the category of [[graphs]] have a
particularly simple description: the nodes are arbitrary functions $N(G)
\to N(H)$ between the node-[[sets]], and an edge between $f$ and $g$ is
given by a family of edges $f(x) \to g(y)$ for each $e : x \to y$ in
$G$.

```agda
Graphs[_,_] : ∀ {o ℓ o' ℓ'} → Graph o ℓ → Graph o' ℓ' → Graph (o ⊔ o') (o ⊔ ℓ ⊔ ℓ')
Graphs[ G , H ] .Node     = ⌞ G ⌟ → ⌞ H ⌟
Graphs[ G , H ] .Edge f g = ∀ {x y} → G .Edge x y → H .Edge (f x) (g y)
Graphs[ G , H ] .Node-set = hlevel 2
Graphs[ G , H ] .Edge-set = hlevel 2
```

Since this is basically an unpacking of the type of graph homomorphisms,
it is easy to show that it satisfies the universal property of
exponentials: the evaluation and currying maps are as in $\Sets$.

```agda
Graphs-closed
  : ∀ {ℓ} → Cartesian-closed (Graphs ℓ ℓ) Graphs-products Graphs-terminal
Graphs-closed .has-exp A B .B^A = Graphs[ A , B ]

Graphs-closed .has-exp A B .ev = record where
  node (f , x) = f x
  edge (e , a) = e a

Graphs-closed .has-exp A B .has-is-exp .ƛ m = record where
  node a b = m .node (a , b)
  edge a b = m .edge (a , b)

Graphs-closed .has-exp A B .has-is-exp .commutes m = trivialᴳ!
Graphs-closed .has-exp A B .has-is-exp .unique m' x = ext record where
  node a b i = x i .node (a , b)
  edge a i b = x i .edge (a , b)
```
