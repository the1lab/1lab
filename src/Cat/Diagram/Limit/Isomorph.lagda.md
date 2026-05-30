---
description: |
  Limits of one-object diagrams are isomorphs.
---

<!--
```agda
open import Cat.Instances.Shape.Terminal
open import Cat.Diagram.Limit.Base
open import Cat.Functor.Constant
open import Cat.Functor.Kan.Base
open import Cat.Functor.Base
open import Cat.Prelude

import Cat.Reasoning
```
-->

```agda
module Cat.Diagram.Limit.Isomorph where
```

<!--
```agda
module _ {o h} (C : Precategory o h)  where
  open Cat.Reasoning C

  open Functor
  open _=>_
```
-->

# Limits of one-object diagrams {defines="one-object-limit"}

We establish a correspondence between [[limits]] of the
[[one-object|terminal category]] diagram $A$ and *isomorphs* of $A$:
objects $B$ that are isomorphic to $A$. In more detail, a cone over
such a diagram is an object $B$ with a map $f : B \to A$, and such a
cone is limiting if and only if $f$ is [[invertible]].

```agda
  is-iso→is-limit
    : ∀ {A B : Functor ⊤Cat C} {eps : B F∘ !F => A}
    → is-invertible (eps .η tt)
    → is-ran !F A B eps
  is-iso→is-limit {A = A} {B} {eps} inv = to-is-limitp ml refl where
    module inv = is-invertible inv
    open make-is-limit

    ml : make-is-limit A (B .F₀ tt)
    ml .ψ = _
    ml .commutes _ = eliml (A .F-id)
    ml .universal eps' _ = inv.inv ∘ eps' tt
    ml .factors eps' _ = cancell inv.invl
    ml .unique eps' _ other com = sym (lswizzle (sym (com tt)) inv.invr)

  is-limit→is-iso
    : ∀ {A B : Functor ⊤Cat C} {eps : B F∘ !F => A}
    → is-ran !F A B eps
    → is-invertible (eps .η tt)
  is-limit→is-iso {A = A} {B} {eps} lim = inv where
    module lim = is-limit lim

    inv : is-invertible (eps .η tt)
    inv = make-invertible
      (lim.universal (λ _ → id) (λ _ → eliml (A .F-id)))
      (lim.factors _ _)
      (lim.unique₂ (λ _ → eps .η tt) (λ _ → eliml (A .F-id))
        (λ _ → cancell (lim.factors _ _)) λ _ → idr _)

  Isomorph→Limit : ∀ {A : Functor ⊤Cat C} → Σ[ B ∈ ⌞ C ⌟ ] B ≅ A .F₀ tt → Limit A
  Isomorph→Limit (A , i) = to-limit {K = !Const A} {eps = !constⁿ (i .to)}
    (is-iso→is-limit (iso→invertible i))

  Limit→Isomorph : ∀ {A} → Limit {C = C} (!Const A) → Σ[ B ∈ ⌞ C ⌟ ] B ≅ A
  Limit→Isomorph lim = lim.apex , invertible→iso _ (is-limit→is-iso lim.has-limit)
    where module lim = Limit lim
```

Since all functors preserve isomorphisms, this is a (fairly trivial)
example of an [[absolute limit]]. On the other hand, the functors that
[[reflect|reflected limit]] these limits are exactly the [[conservative]]
(i.e., isomorphism-reflecting) functors.

```agda
module _ {o h} (C : Precategory o h)  where
  isomorph-is-absolute-limit
    : ∀ {A B : Functor ⊤Cat C} {eps : B F∘ !F => A}
    → (ran : is-ran !F A B eps)
    → is-absolute-ran ran
  isomorph-is-absolute-limit ran H =
    is-iso→is-limit _ (F-map-invertible H (is-limit→is-iso _ ran))
```
