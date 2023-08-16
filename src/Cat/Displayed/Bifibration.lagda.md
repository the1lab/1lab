<!--
```agda
open import Cat.Functor.Adjoint.Hom
open import Cat.Instances.Functor
open import Cat.Displayed.Fibre
open import Cat.Functor.Adjoint
open import Cat.Displayed.Base
open import Cat.Prelude

import Cat.Displayed.Cocartesian.Indexing
import Cat.Displayed.Cartesian.Indexing
import Cat.Displayed.Cocartesian.Weak
import Cat.Displayed.Cartesian.Weak
import Cat.Displayed.Cocartesian
import Cat.Displayed.Cartesian
import Cat.Displayed.Reasoning
import Cat.Reasoning
```
-->

```agda
module Cat.Displayed.Bifibration
  {o ℓ o′ ℓ′} {ℬ : Precategory o ℓ} (ℰ : Displayed ℬ o′ ℓ′) where
```

<!--
```agda
open Cat.Displayed.Cocartesian ℰ
open Cat.Displayed.Cocartesian.Weak ℰ
open Cat.Displayed.Cartesian ℰ
open Cat.Displayed.Cartesian.Weak ℰ
open Cat.Displayed.Reasoning ℰ

open Precategory ℬ
open Displayed ℰ
```
-->


# Bifibrations

A [[displayed category]] $\cE \liesover \cB$ is a **bifibration** if is
it both a [[fibration|cartesian fibration]] and an opfibration. This
means that $\cE$ is equipped with both [reindexing] and [opreindexing]
functors, which allows us to both restrict and extend along morphisms $X
\to Y$ in the base.

Note that a bifibration is *not* the same as a "profunctor of categories";
these are called **two-sided fibrations**, and are a distinct concept.

[reindexing]: Cat.Displayed.Cartesian.Indexing.html
[opreindexing]: Cat.Displayed.Cocartesian.Indexing.html

<!--
[TODO: Reed M, 31/01/2023] Link to two-sided fibration
when that page is written.
-->


```agda
record is-bifibration : Type (o ⊔ ℓ ⊔ o′ ⊔ ℓ′) where
  field
    fibration : Cartesian-fibration
    opfibration : Cocartesian-fibration

  module fibration = Cartesian-fibration fibration
  module opfibration = Cocartesian-fibration opfibration
```

# Bifibrations and Adjoints

If $\cE$ is a bifibration, then its opreindexing functors are [[left
adjoints]] to its reindexing functors. To see this, note that we need to
construct a natural isomorphism between $\cE_{y}(u_{*}(-),-)$ and
$\cE_{x}(-,u^{*}(-))$. However, we have already shown that
$\cE_{y}(u_{*}(-),-)$ and $\cE_{x}(-,u^{*}(-))$ are both naturally
isomorphic to $\cE_{u}(-,-)$ (see `opfibration→hom-iso`{.Agda} and
`fibration→hom-iso`{.Agda}), so all we need to do is compose these
natural isomorphisms!

```agda
module _ (bifib : is-bifibration) where
  open is-bifibration bifib
  open Cat.Displayed.Cartesian.Indexing ℰ fibration
  open Cat.Displayed.Cocartesian.Indexing ℰ opfibration

  cobase-change⊣base-change
    : ∀ {x y} (f : Hom x y)
    → cobase-change f ⊣ base-change f
  cobase-change⊣base-change {x} {y} f =
    hom-natural-iso→adjoints $
      (opfibration→hom-iso opfibration f ni⁻¹) ni∘ fibration→hom-iso fibration f
```

In fact, if $\cE$ is a cartesian fibration where every reindexing
functor has a left adjoint, then $\cE$ is a bifibration!
To see this, note that we have a natural iso
$\cE_{u}(x',-) \simeq \cE_{x}(x', u^{*}(-))$ for every $u : x \to y$ in
the base. However, $u^{*}$ has a left adjoint $L_{u}$ for every $u$,
so we also have a natural isomorphism
$\cE_{x}(x', u^{*}(-)) \simeq \cE_{y}(L_{u}(x'),-)$. Composing these
yields a natural iso $\cE_{u}(x',-) \simeq \cE_{y}(L_{u}(x'),-)$, which
implies that $\cE$ is a weak opfibration due to
`hom-iso→weak-opfibration`{.Agda}.

Furthermore, $\cE$ is a fibration, which allows us to upgrade the
weak opfibration to an opfibration!

```agda
module _ (fib : Cartesian-fibration) where
  open Cartesian-fibration fib
  open Cat.Displayed.Cartesian.Indexing ℰ fib

  left-adjoint-base-change→opfibration
    : (L : ∀ {x y} → (f : Hom x y) → Functor (Fibre ℰ x) (Fibre ℰ y))
    → (∀ {x y} → (f : Hom x y) → (L f ⊣ base-change f))
    → Cocartesian-fibration
  left-adjoint-base-change→opfibration L adj =
    cartesian+weak-opfibration→opfibration fib $
    hom-iso→weak-opfibration L λ u →
      fibration→hom-iso-from fib u ni∘ (adjunct-hom-iso-from (adj u) _ ni⁻¹)
```

With some repackaging, we can see that this yields a bifibration.

```agda
  left-adjoint-base-change→bifibration
    : (L : ∀ {x y} → (f : Hom x y) → Functor (Fibre ℰ x) (Fibre ℰ y))
    → (∀ {x y} → (f : Hom x y) → (L f ⊣ base-change f))
    → is-bifibration
  left-adjoint-base-change→bifibration L adj .is-bifibration.fibration =
    fib
  left-adjoint-base-change→bifibration L adj .is-bifibration.opfibration =
    left-adjoint-base-change→opfibration L adj
```
