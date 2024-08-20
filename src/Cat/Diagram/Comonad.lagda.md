<!--
```agda
open import Cat.Functor.Adjoint
open import Cat.Functor.Base
open import Cat.Prelude

import Cat.Reasoning
```
-->

```agda
module Cat.Diagram.Comonad {o ℓ} (C : Precategory o ℓ) where
```

<!--
```agda
open Cat.Reasoning C

open Functor
open _=>_
```
-->

# Comonads

A **comonad on a category** $\cC$ is dual to a [monad] on $\cC$; instead
of a unit $\Id \To M$ and multiplication $(M \circ M) \To M$, we have
a counit $M \To \Id$ and comultiplication $M \To (M \circ M)$.

[monad]: Cat.Diagram.Monad.html

```agda
record Comonad : Type (o ⊔ ℓ) where
  field
    W : Functor C C
    counit : W => Id
    comult : W => (W F∘ W)
```

<!--
```agda
  module counit = _=>_ counit renaming (η to ε)
  module comult = _=>_ comult

  W₀ = W .F₀
  W₁ = W .F₁
  W-id = W .F-id
  W-∘ = W .F-∘
```
-->

We also have equations governing the counit and comultiplication.
Unsurprisingly, these are dual to the equations of a monad.

```agda
  field
    left-ident : ∀ {x} → W₁ (counit.ε x) ∘ comult.η x ≡ id
    right-ident : ∀ {x} → counit.ε (W₀ x) ∘ comult.η x ≡ id
    comult-assoc : ∀ {x} → W₁ (comult.η x) ∘ comult.η x ≡ comult.η (W₀ x) ∘ comult.η x
```

<!--
```agda
record is-comonad (W : Functor C C) (counit : W => Id) (comult : W => W F∘ W) : Type (o ⊔ ℓ) where
  no-eta-equality
  open Functor W renaming (F₀ to W₀; F₁ to W₁)
  open _=>_ counit renaming (η to ε) using ()
  open _=>_ comult renaming (η to δ) using ()
  field
    left-ident : ∀ {x} → W₁ (ε x) ∘ δ x ≡ id
    right-ident : ∀ {x} → ε (W₀ x) ∘ δ x ≡ id
    comult-assoc : ∀ {x} → W₁ (δ x) ∘ δ x ≡ δ (W₀ x) ∘ δ x
```
-->
