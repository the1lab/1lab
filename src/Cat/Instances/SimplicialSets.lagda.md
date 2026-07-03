<!--
```agda
open import Cat.Instances.Presheaf.Exponentials
open import Cat.Instances.Presheaf.Limits
open import Cat.Functor.FullSubcategory
open import Cat.Diagram.Exponential
open import Cat.Instances.Simplex
open import Cat.Functor.Base
open import Cat.Functor.Hom
open import Cat.Cartesian
open import Cat.Prelude

open import Data.Fin

import Cat.Reasoning

open Precategory
open Functor
open Δ-map
open _=>_
```
-->

```agda
module Cat.Instances.SimplicialSets where
```

# Simplicial sets {defines="simplicial-set"}

A **simplicial set** is a presheaf on the [[simplex category]]
$\Delta$. Thinking of the object $[n] : \Delta$ as the abstract
$n$-simplex, a simplicial set $X$ is a system of sets $X_n$ of
"$n$-simplices in $X$" — plots of shape $\Delta^n$ — related by
restriction along all the [[coface|coface]] and
[[codegeneracy|codegeneracy]] maps.

```agda
sSet : Precategory (lsuc lzero) lzero
sSet = PSh lzero Δ
```

<!--
```agda
private module sSet = Cat.Reasoning sSet
```
-->

The representable simplicial sets are the **standard simplices**: by
the [[Yoneda lemma]], the $m$-simplices of $\Delta^n$ are exactly the
maps $[m] \to [n]$ in $\Delta$.

```agda
Δ[_] : Nat → ⌞ sSet ⌟
Δ[ n ] = よ₀ Δ n
```

Being a presheaf category, simplicial sets inherit all the structure
of a [[Grothendieck topos]]; in particular they are [[cartesian
closed]], so there is a simplicial set $\rm{Maps}(X, Y)$ of maps
between any two simplicial sets.

```agda
sSet-cartesian : Cartesian-category sSet
sSet-cartesian = PSh-cartesian lzero Δ

sSet-closed : Cartesian-closed sSet sSet-cartesian
sSet-closed = PSh-closed Δ
```

## Horns and the Kan condition {defines="horn kan-condition kan-complex"}

The $k$-th **horn** $\Lambda^n_k \mono \Delta^n$ is the boundary of
the $n$-simplex with the $k$-th face removed. An $m$-simplex of
$\Lambda^n_k$ is a map $f : [m] \to [n]$ which, together with the
vertex $k$, fails to cover $[n]$: some vertex $j \ne k$ is missed by
$f$ entirely. Since $\Delta$ is made of finite ordinals this is a
(decidable) proposition, and it is stable under precomposition, since
precomposing only shrinks the image.

```agda
is-horn : ∀ {m n} (k : Fin (suc n)) (f : Δ-map m n) → Type
is-horn {n = n} k f =
  ∃[ j ∈ Fin (suc n) ] ((¬ j ≡ k) × (∀ i → ¬ f .map i ≡ j))

is-horn-∘
  : ∀ {m m' n} (k : Fin (suc n)) (f : Δ-map m n) (g : Δ-map m' m)
  → is-horn k f → is-horn k (f ∘Δ g)
is-horn-∘ k f g = ∥-∥-map λ where
  (j , j≠k , miss) → j , j≠k , λ i → miss (g .map i)
```

The horn itself is the simplicial subset of $\Delta^n$ carved out by
this condition.

```agda
Λ[_,_] : (n : Nat) (k : Fin (suc n)) → ⌞ sSet ⌟
Λ[ n , k ] .F₀ m = el! (Σ[ f ∈ Δ-map m n ] is-horn k f)
Λ[ n , k ] .F₁ g (f , h) = f ∘Δ g , is-horn-∘ k f g h
Λ[ n , k ] .F-id = funext λ _ → Σ-prop-path! refl
Λ[ n , k ] .F-∘ f g = funext λ _ → Σ-prop-path! refl

horn-inclusion : ∀ n k → Λ[ n , k ] => Δ[ n ]
horn-inclusion n k .η m = fst
horn-inclusion n k .is-natural m m' g = refl
```

A simplicial set $X$ is **Kan** — is a **Kan complex** — when every
horn in $X$ admits a filler: every map $\Lambda^n_k \to X$ extends
along the horn inclusion to a full simplex $\Delta^n \to X$. This is
the geometric shape of *composition*: for example, a horn
$\Lambda^2_1 \to X$ is a pair of composable edges, and a filler
exhibits a composite together with the 2-simplex witnessing it.
Existence of fillers, with no chosen filling, is a proposition, so
"being Kan" is a *property* of a simplicial set.

```agda
is-kan : ⌞ sSet ⌟ → Type
is-kan X =
  ∀ {n} (k : Fin (suc n)) (α : Λ[ n , k ] => X)
  → ∃[ β ∈ (Δ[ n ] => X) ] (β sSet.∘ horn-inclusion n k ≡ α)

is-kan-is-prop : ∀ X → is-prop (is-kan X)
is-kan-is-prop X = hlevel 1
```

Kan complexes are the fibrant objects of the classical homotopy
theory of simplicial sets; they model $\infty$-groupoids, in which
every cell is invertible up to higher cells. The full subcategory
they span is the (1-categorical shadow of the) world where higher
gauge theory happens: gauge transformations are 1-simplices,
gauge-of-gauge transformations are 2-simplices, and so on.

```agda
Kan-complexes : Precategory (lsuc lzero) lzero
Kan-complexes = Restrict {C = sSet} is-kan
```
