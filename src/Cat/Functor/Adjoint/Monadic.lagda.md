---
description: |
  We establish the theory of monadic adjunctions, and define the
  comparison functor into the Eilenberg-Moore category for the induced
  monad.
---
<!--
```agda
open import Cat.Functor.Equivalence.Properties
open import Cat.Instances.Algebras.Limits
open import Cat.Functor.Adjoint.Monad
open import Cat.Functor.Equivalence
open import Cat.Diagram.Limit.Base
open import Cat.Displayed.Total
open import Cat.Functor.Adjoint
open import Cat.Diagram.Monad
open import Cat.Functor.Base
open import Cat.Prelude

import Cat.Functor.Reasoning
import Cat.Reasoning

open Total-hom
open Functor
open _=>_
```
-->

# Monadic adjunctions {defines="monadic-adjunction monadic-functor monadic"}

An adjunction $L \dashv R$ between functors $L : C \to D$ and $R : D \to
C$ is **monadic** if the induced `comparison functor`{.Agda
ident=Comparison-EM} $D \to C^{R \circ L}$ (where the right-hand side is
the `Eilenberg-Moore`{.Agda} category of the [monad of the
adjunction](Cat.Functor.Adjoint.Monad.html)) is an equivalence of
categories.

```agda
module
  Cat.Functor.Adjoint.Monadic
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

R∘L : Monad-on _
R∘L = Adjunction→Monad L⊣R

open Monad-on R∘L

_ = Algebra
```
-->

The composition of `R.₁`{.Agda} with the `adjunction counit`{.Agda
ident="adj.counit.ε"} natural transformation gives `R`{.Agda} an
`Algebra`{.Agda} structure, thus extending `R` to a functor $D \to C^{R
\circ L}$.

```agda
Comparison-EM : Functor D (Eilenberg-Moore R∘L)
Comparison-EM .F₀ x = R.₀ x , alg where
  alg : Algebra-on R∘L (R.₀ x)
  alg .Algebra-on.ν = R.₁ (adj.counit.ε _)
  alg .Algebra-on.ν-unit = adj.zag
  alg .Algebra-on.ν-mult = R.weave (sym $ adj.counit.is-natural _ _ _)
```

<details>
<summary> Construction of the functorial action of `Comparison-EM`{.Agda} </summary>

```agda
Comparison-EM .F₁ x .hom = R.₁ x
Comparison-EM .F₁ x .preserves = R.weave (sym (adj.counit.is-natural _ _ _))
Comparison-EM .F-id    = ext R.F-id
Comparison-EM .F-∘ f g = ext (R.F-∘ _ _)
```
</details>

By construction, the composition of the comparison functor with the
forgetful functor is equal to $R$.

```agda
Forget∘Comparison≡R : Forget-EM F∘ Comparison-EM ≡ R
Forget∘Comparison≡R = Functor-path (λ _ → refl) (λ _ → refl)
```

To summarise, we have the following triangle:

~~~ {.quiver}
\[\begin{tikzcd}
  D && C \\
  \\
  {C^{R \circ L}}
  \arrow[""{name=0, anchor=center, inner sep=0}, "R"', shift right=2, from=1-1, to=1-3]
  \arrow["{\mathrm{Comparison}}"', from=1-1, to=3-1]
  \arrow[""{name=1, anchor=center, inner sep=0}, "L"', shift right=2, from=1-3, to=1-1]
  \arrow[""{name=2, anchor=center, inner sep=0}, "F"', shift left, from=1-3, to=3-1]
  \arrow[""{name=3, anchor=center, inner sep=0}, "U"', shift right=5, from=3-1, to=1-3]
  \arrow["\dashv"{anchor=center, rotate=-90}, draw=none, from=1, to=0]
  \arrow["\dashv"{anchor=center, rotate=-45}, draw=none, from=2, to=3]
\end{tikzcd}\]
~~~

An adjunction is **monadic** if `Comparison-EM`{.Agda} is an [[equivalence of
categories]], thus exhibiting $C$ as the category of $(R \circ L)$-algebras:

```agda
is-monadic : Type _
is-monadic = is-equivalence Comparison-EM
```

We also say that the right adjoint $R$ is a **monadic functor**.

## Monadic functors create limits {defines="monadic-functors-create-limits"}

By the description of [[limits in categories of algebras]],
`Forget-EM`{.Agda} [[creates limits]]. Furthermore, if the adjunction
$L \dashv R$ is monadic, then `Comparison-EM`{.Agda} is an equivalence
of categories, so it also creates limits. Since this property is closed
under composition, monadic functors creates limits.

<!--
```agda
module _ (monadic : is-monadic) where
```
-->

```agda
  monadic→creates-limits
    : ∀ {oj ℓj} {J : Precategory oj ℓj} → creates-limits-of J R
  monadic→creates-limits = subst (creates-limits-of _) Forget∘Comparison≡R $
    F∘-creates-limits (equivalence→creates-limits monadic)
      (Forget-EM-creates-limits R∘L)
```
