---
description: |
  Constant functors.
---
<!--
```agda
open import Cat.Instances.Shape.Terminal
open import Cat.Functor.Naturality
open import Cat.Functor.Compose
open import Cat.Functor.Base
open import Cat.Prelude

import Cat.Reasoning
import Cat.Functor.Reasoning
```
-->

```agda
module Cat.Functor.Constant where
```

# Constant functors {defines="constant-functor"}

A **constant functor** is a [[functor]] $F : \cC \to \cD$ that sends
every object of $\cC$ to a single object $d : \cD$, and every morphism
of $\cC$ to the identity morphism.

<!--
```agda
module _
  {o ℓ o' ℓ'}
  {C : Precategory o ℓ} {D : Precategory o' ℓ'}
  where
  private
    module C = Cat.Reasoning C
    module D = Cat.Reasoning D
  open Functor
  open _=>_
```
-->

Equivalently, constant functors $\cC \to \cD$ are
factorizations through the [[terminal category]]. We opt to take this
notion as primitive for ergonomic reasons: it is useful to only be able
to write constant functors in a single way.

```agda
  Const : D.Ob → Functor C D
  Const X = !Const X F∘ !F
```

Natural transformations between constant functors are given by a single
morphism, and natural isomorphisms by a single iso.

```agda
  constⁿ
    : {X Y : D.Ob}
    → D.Hom X Y
    → Const X => Const Y
  constⁿ f = !constⁿ f ◂ !F

  const-isoⁿ
    : {X Y : D.Ob}
    → X D.≅ Y
    → Const X ≅ⁿ Const Y
  const-isoⁿ f =
    iso→isoⁿ (λ _ → f) (λ f → D.id-comm-sym)
```

<!--
```agda
  -- Coherence lemmas for cones and cocones as natural transformations.
  to-coconeⁿ
    : ∀ {F : Functor C D} {K : Functor ⊤Cat D}
    → F => K F∘ !F
    → F => Const (K .F₀ tt)
  to-coconeⁿ {K = K} ψ .η = ψ .η
  to-coconeⁿ {K = K} ψ .is-natural x y f =
    ψ .is-natural x y f ∙ ap₂ D._∘_ (K .F-id) refl

  to-coneⁿ
    : ∀ {F : Functor C D} {K : Functor ⊤Cat D}
    → K F∘ !F => F
    → Const (K .F₀ tt) => F
  to-coneⁿ {K = K} ψ .η = ψ .η
  to-coneⁿ {K = K} ψ .is-natural x y f =
    ap₂ D._∘_ refl (sym (K .F-id)) ∙ ψ .is-natural x y f
```
-->


## Essentially constant functors {defines="essentially-constant-functor"}

A functor is **essentially constant** if it is (merely) isomorphic
to a constant functor.

```agda
  is-essentially-constant : Functor C D → Type _
  is-essentially-constant F = ∃[ X ∈ D.Ob ] (F ≅ⁿ Const X)
```

<!--
```agda
module _
  {ob ℓb oc ℓc od ℓd}
  {B : Precategory ob ℓb}
  {C : Precategory oc ℓc}
  {D : Precategory od ℓd}
  (F : Functor C D) (G : Functor B C)
  where
  private
    module D = Cat.Reasoning D
    module F = Cat.Functor.Reasoning F
    module G = Cat.Functor.Reasoning G

  open Isoⁿ
  open _=>_
```
-->

Essentially constant functors are closed under pre and postcomposition
by arbitrary functors.

```agda
  essentially-constant-∘l
    : is-essentially-constant F
    → is-essentially-constant (F F∘ G)
  essentially-constant-∘l =
    rec! λ d f →
      pure $ d ,
        iso→isoⁿ
          (λ b → isoⁿ→iso f (G.₀ b))
          (λ g → sym (f .to .is-natural _ _ (G.₁ g)))

  essentially-constant-∘r
    : is-essentially-constant G
    → is-essentially-constant (F F∘ G)
  essentially-constant-∘r =
    rec! λ c f →
      pure $ F.₀ c ,
        iso→isoⁿ
          (λ b → F-map-iso F (isoⁿ→iso f b))
          (λ g →
            ap₂ D._∘_ (sym (F.F-id)) refl
            ∙ F.weave (sym (f .to .is-natural _ _ g)))
```
