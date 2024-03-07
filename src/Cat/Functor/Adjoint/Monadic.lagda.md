---
description: |
  We establish the theory of monadic adjunctions, and define the
  comparison functor into the Eilenberg-Moore category for the induced
  monad.
---
<!--
```agda
open import Cat.Functor.Adjoint.Monad
open import Cat.Functor.Equivalence
open import Cat.Functor.Adjoint
open import Cat.Diagram.Monad
open import Cat.Prelude

open Functor
open _=>_
```
-->

# Monadic adjunctions {defines="monadic-adjunction monadic-functor monadic"}

An adjunction $F \dashv G$ between functors $F : C \to D$ and $G : D \to
C$ is _monadic_ if the induced `comparison functor`{.Agda
ident=Comparison} $D \to C^{R \circ L}$ (where the right-hand side is
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
  module C = Precategory C
  module D = Precategory D
  module L = Functor L
  module R = Functor R
  module adj = _⊣_ L⊣R

L∘R : Monad C
L∘R = Adjunction→Monad L⊣R

open Monad L∘R
```
-->

The composition of `R.₁`{.Agda} with the `adjunction counit`{.Agda
ident="adj.counit.ε"} natural transformation gives `R`{.Agda} an
`Algebra`{.Agda} structure, thus extending `R` to a functor $D \to C^{L
\circ R}$.

```agda
Comparison : Functor D (Eilenberg-Moore C L∘R)
Comparison .F₀ x = R.₀ x , alg where
  alg : Algebra-on C L∘R (R.₀ x)
  alg .Algebra-on.ν = R.₁ (adj.counit.ε _)
  alg .Algebra-on.ν-unit = adj.zag
  alg .Algebra-on.ν-mult =
    R.₁ (adj.counit.ε _) C.∘ M₁ (R.₁ (adj.counit.ε _))        ≡⟨ sym (R.F-∘ _ _) ⟩
    R.₁ (adj.counit.ε _ D.∘ L.₁ (R.₁ (adj.counit.ε _)))       ≡⟨ ap R.₁ (adj.counit.is-natural _ _ _) ⟩
    R.₁ (adj.counit.ε x D.∘ adj.counit.ε (L.₀ (R.₀ x)))       ≡⟨ R.F-∘ _ _ ⟩
    R.₁ (adj.counit.ε x) C.∘ R.₁ (adj.counit.ε (L.₀ (R.₀ x))) ∎
```

<details>
<summary> Construction of the functorial action of `Comparison`{.Agda} </summary>

```agda
Comparison .F₁ x = hom where
  open Algebra-hom
  hom : Algebra-hom C _ _ _
  hom .morphism = R.₁ x
  hom .commutes =
    R.₁ x C.∘ R.₁ (adj.counit.ε _)        ≡⟨ sym (R.F-∘ _ _) ⟩
    R.₁ (x D.∘ adj.counit.ε _)            ≡⟨ ap R.₁ (sym (adj.counit.is-natural _ _ _)) ⟩
    R.₁ (adj.counit.ε _ D.∘ L.₁ (R.₁ x))  ≡⟨ R.F-∘ _ _ ⟩
    R.₁ (adj.counit.ε _) C.∘ M₁ (R.₁ x)   ∎
Comparison .F-id    = ext R.F-id
Comparison .F-∘ f g = ext (R.F-∘ _ _)
```
</details>

An adjunction is _monadic_ if `Comparison`{.Agda} is an [equivalence of
categories], thus exhibiting $C$ as the category of $R\circ L$-algebras:

[equivalence of categories]: Cat.Functor.Equivalence.html

```agda
is-monadic : Type _
is-monadic = is-equivalence Comparison
```

<!--
```agda
_ = Algebra
```
-->
