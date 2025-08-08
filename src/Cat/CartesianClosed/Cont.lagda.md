<!--
```agda
open import Cat.Functor.Adjoint.Monad
open import Cat.Diagram.Exponential
open import Cat.Diagram.Monad
open import Cat.Functor.Adjoint.Hom
open import Cat.Functor.Adjoint
open import Cat.Cartesian
open import Cat.Prelude

import Cat.CartesianClosed.Solver as S
import Cat.Functor.Bifunctor as Bifunctor
import Cat.Reasoning
```
-->

```agda
module Cat.CartesianClosed.Cont
```

<!--
```agda
  {o ℓ} {C : Precategory o ℓ} (cart : Cartesian-category C)
  (cc : Cartesian-closed C cart)
  where

open Cartesian-category cart
open Cartesian-closed cc
open S cart cc
```
-->

# The continuation monad

We show that, in a [[Cartesian closed]] category $\cC$, for any object
$S$, the functor $[-,S] : \cC\op \to \cC$ is [[adjoint]] to itself on
the right--- meaning that its left adjoint is its opposite functor.

```agda
[-,_] : Ob → Functor (C ^op) C
[-,_] S = Bifunctor.Left ([-,-] C cart cc) S
```

The proof boils down to noticing that we have an isomorphism
$$\hom(X, [Y, S]) \simeq \hom(X \times Y, S) \simeq \hom(Y \times X, S) \simeq \hom(Y, [X, S])$$,
natural in all three variables, but we write a proof in components as
an application of the [solver for CCCs]. We define the adjunction
mapping first in terms of formal morphisms, and then obtain the actual
function $\hom(X, [Y,S]) \to \hom(Y, [X,S])$ as its denotation.

[solver for CCCs]: Cat.CartesianClosed.Solver.html

```agda
maps-into-self-adjoint : ∀ S → opFʳ [-, S ] ⊣ [-, S ]
maps-into-self-adjoint S = hom-iso→adjoints tr eqv nat where
  `tr : ∀ {x y} → Mor y (x `⇒ ` S) → Mor x (y `⇒ ` S)
  `tr f = `ƛ (`ev `∘ (f `∘ `π₂ `, `π₁))

  tr : ∀ {x y} → Hom y [ x , S ] → Hom x [ y , S ]
  tr {x} {y} f = ⟦ `tr {x = ` x} {y = ` y} (` f) ⟧ᵐ
```

<details>
<summary>The proofs that this function is invertible and that it is
natural in both $X$ and $Y$ are all applications of the solver. </summary>

```agda
  eqv : ∀ {x y} → is-equiv (tr {x} {y})
  eqv {x} {y} = is-iso→is-equiv record where
    from   = tr
    linv m = solve (`tr (`tr {x = ` x} {` y} (` m))) (` m) refl
    rinv m = solve (`tr (`tr {x = ` y} {` x} (` m))) (` m) refl

  abstract
    nat : hom-iso-natural {L = opFʳ [-, S ]} {R = [-, S ]} tr
    nat {a} {b} {c} {d} g h x =
      let
        `h : Mor (` c) (` d) ; `h = ` h
        `g : Mor (` b) (` a) ; `g = ` g
      in solve
        (`tr ((`ƛ (`id `∘ `ev `∘ (`π₁ `, `h `∘ `π₂)) `∘ ` x) `∘ `g))
        (`ƛ (`id `∘ `ev `∘ (`π₁ `, `g `∘ `π₂)) `∘ `tr (` x) `∘ `h)
        refl
```

</details>

Every adjunction generates a monad. We refer to the monad structure on
$[[-,S],S]$ as the ($S$-valued) **continuation monad**.


```agda
Continuation-monad : ∀ S → Monad-on ([-, S ] F∘ opFʳ [-, S ])
Continuation-monad S = Adjunction→Monad (maps-into-self-adjoint S)
```
