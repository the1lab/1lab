---
description: |
  We establish the theory of comonadic adjunctions, and define the
  comparison functor into the Eilenberg-Moore category for the induced
  comonad.
---
<!--
```agda
open import Cat.Functor.Equivalence.Properties
open import Cat.Instances.Coalgebras.Colimits
open import Cat.Functor.Adjoint.Comonad
open import Cat.Diagram.Colimit.Base
open import Cat.Instances.Coalgebras
open import Cat.Functor.Equivalence
open import Cat.Diagram.Comonad
open import Cat.Displayed.Total
open import Cat.Functor.Adjoint
open import Cat.Functor.Base
open import Cat.Prelude

import Cat.Functor.Reasoning
import Cat.Reasoning

open Total-hom
open Functor
open _=>_
```
-->

# Comonadic adjunctions {defines="comonadic-adjunction comonadic-functor comonadic"}

An adjunction $L \dashv R$ between functors $L : C \to D$ and $R : D \to
C$ is **comonadic** if the induced `comparison functor`{.Agda
ident=Comparison-CoEM} $C \to C^{L \circ R}$ (where the right-hand side is
the category of `Coalgebras`{.Agda} of the [[comonad of the
adjunction|comonad from an adjunction]]) is an equivalence of
categories. This dualises the theory of [[monadic adjunctions]].

```agda
module
  Cat.Functor.Adjoint.Comonadic
  {o₁ h₁ o₂ h₂ : _}
  {C : Precategory o₁ h₁}
  {D : Precategory o₂ h₂}
  {L : Functor C D} {R : Functor D C}
  (L⊣R : L ⊣ R)
  where
```

<!--
```agda
private
  module C = Cat.Reasoning C
  module D = Cat.Reasoning D
  module L = Cat.Functor.Reasoning L
  module R = Cat.Functor.Reasoning R
  module adj = _⊣_ L⊣R

L∘R : Comonad-on _
L∘R = Adjunction→Comonad L⊣R

open Comonad-on L∘R

_ = Coalgebra
```
-->

The composition of `L.₁`{.Agda} with the `adjunction unit`{.Agda
ident="adj.unit.η"} natural transformation gives `L`{.Agda} a
`Coalgebra`{.Agda} structure, thus extending `L` to a functor $C \to C^{L
\circ R}$.

```agda
Comparison-CoEM : Functor C (Coalgebras L∘R)
Comparison-CoEM .F₀ x = L.₀ x , alg where
  alg : Coalgebra-on L∘R (L.₀ x)
  alg .Coalgebra-on.ρ = L.₁ (adj.unit.η _)
  alg .Coalgebra-on.ρ-counit = adj.zig
  alg .Coalgebra-on.ρ-comult = L.weave (adj.unit.is-natural _ _ _)
```

<details>
<summary> Construction of the functorial action of `Comparison-CoEM`{.Agda} </summary>

```agda
Comparison-CoEM .F₁ x .hom = L.₁ x
Comparison-CoEM .F₁ x .preserves = L.weave (sym (adj.unit.is-natural _ _ _))
Comparison-CoEM .F-id    = ext L.F-id
Comparison-CoEM .F-∘ f g = ext (L.F-∘ _ _)
```
</details>

By construction, the composition of the comparison functor with the
forgetful functor is equal to $L$.

```agda
Forget∘Comparison≡L : πᶠ (Coalgebras-over L∘R) F∘ Comparison-CoEM ≡ L
Forget∘Comparison≡L = Functor-path (λ _ → refl) (λ _ → refl)
```

An adjunction is **comonadic** if `Comparison-CoEM`{.Agda} is an [[equivalence of
categories]], thus exhibiting $C$ as the category of $(L \circ R)$-coalgebras:

```agda
is-comonadic : Type _
is-comonadic = is-equivalence Comparison-CoEM
```

We also say that the left adjoint $L$ is a **comonadic functor**.

## Comonadic functors create colimits {defines="comonadic-functors-create-colimits"}

By the description of [[colimits in categories of coalgebras]],
the forgetful functor `πᶠ`{.Agda} [[creates colimits]]. Furthermore, if
the adjunction $L \dashv R$ is comonadic, then `Comparison-CoEM`{.Agda}
is an equivalence of categories, so it also creates colimits. Since this
property is closed under composition, comonadic functors creates colimits.

<!--
```agda
module _ (comonadic : is-comonadic) where
```
-->

```agda
  comonadic→creates-colimits
    : ∀ {oj ℓj} {J : Precategory oj ℓj} → creates-colimits-of J L
  comonadic→creates-colimits = subst (creates-colimits-of _) Forget∘Comparison≡L $
    F∘-creates-colimits (equivalence→creates-colimits comonadic)
      (Forget-CoEM-creates-colimits L∘R)
```
