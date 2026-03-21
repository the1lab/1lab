<!--
```agda
open import Cat.Instances.Product
open import Cat.Displayed.Solver
open import Cat.Displayed.Fibre
open import Cat.Displayed.Base
open import Cat.Functor.Base
open import Cat.Prelude

import Cat.Displayed.Reasoning
import Cat.Functor.Bifunctor as Bi

open Make-bifunctor
open Functor
```
-->

```agda
module Cat.Functor.Hom.Displayed
  {o ℓ o' ℓ'} {ℬ : Precategory o ℓ} (ℰ : Displayed ℬ o' ℓ')
  where
```

<!--
```agda
open Precategory ℬ
open Cat.Displayed.Reasoning ℰ
```
-->

# Displayed Hom functors

Let $\cE$ be a [[displayed category]] over $\cB$. For every $u : x \to y$
in the base, we can obtain a bifunctor from $\cE_{x}\op \times \cE_{y}$
to $\Sets$, where $\cE_{x}$ denotes the [[fibre category]] of $\cE$ at $x$.
The action of $(f, h)$ on $g$ is given by $h \circ g \circ f$, just as
in the [non-displayed case].

[bifunctor]: Cat.Functor.Bifunctor.html
[non-displayed case]: Cat.Functor.Hom.html

```agda
Hom-over : ∀ {x y} → Hom x y → Bifunctor (Fibre ℰ x ^op) (Fibre ℰ y) (Sets ℓ')
Hom-over u = make-bifunctor λ where
  .F₀ a b  → el! (Hom[ u ] a b)
  .lmap f g → hom[ idr u ] (g ∘' f)
  .rmap f g → hom[ idl u ] (f ∘' g)
  .lmap-id → ext λ h → from-pathp[] (idr' _)
  .rmap-id → ext λ h → from-pathp[] (idl' _)
  .lmap-∘ f g → funext λ h →
    hom[] (h ∘' hom[] (g ∘' f)) ≡⟨ disp! ℰ ⟩
    hom[] (hom[] (h ∘' g) ∘' f) ∎
  .rmap-∘ f g → funext λ h →
    hom[] (hom[] (f ∘' g) ∘' h) ≡⟨ disp! ℰ ⟩
    hom[] (f ∘' hom[] (g ∘' h)) ∎
  .lrmap  f g → funext λ h →
    hom[] (hom[] (g ∘' h) ∘' f) ≡⟨ disp! ℰ ⟩
    hom[] (g ∘' hom[] (h ∘' f)) ∎
```

We can also define partially applied versions of this functor.

```agda
Hom-over-from : ∀ {x y} → Hom x y → Ob[ x ] → Functor (Fibre ℰ y) (Sets ℓ')
Hom-over-from u x' = Bi.Right (Hom-over u) x'

Hom-over-into : ∀ {x y} → Hom x y → Ob[ y ] → Functor (Fibre ℰ x ^op) (Sets ℓ')
Hom-over-into u y' = Bi.Left (Hom-over u) y'
```
