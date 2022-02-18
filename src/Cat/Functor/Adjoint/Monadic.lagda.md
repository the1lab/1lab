```agda
open import Cat.Functor.Adjoint.Monad
open import Cat.Functor.Adjoint.Monad
open import Cat.Functor.Adjoint
open import Cat.Prelude
open import Cat.Monad

open Functor
open _=>_
```

# Monadic Adjunctions

An adjunction $F \dashv G$ between functors $F : C \to D$ and $G : D \to
C$ is _monadic_ if the induced `comparison functor`{.Agda
ident=Comparison} $D \to C^{R \circ L}$ (where the right-hand side is
the `Eilenberg-Moore`{.Agda} category of the [monad of the
adjunction](Cat.Functor.Adjoint.Monad.html)) is an equivalence of
categories.

```
module
  Cat.Functor.Adjoint.Monadic
  {o₁ h₁ o₂ h₂ : _}
  {C : Precategory o₁ h₁}
  {D : Precategory o₂ h₂}
  {L : Functor C D} {R : Functor D C}
  (L⊣R : L ⊣ R)
  where

private
  module C = Precategory C
  module D = Precategory D
  module L = Functor L
  module R = Functor R
  module adj = _⊣_ L⊣R

L∘R : Monad
L∘R = Adjunction→Monad L⊣R

open Monad L∘R
```

The composition of `R.₁`{.Agda} with the `adjunction counit`{.Agda
ident="adj.counit.η"} natural transformation gives `R`{.Agda} a
`Algebra`{.Agda ident="Algebra"} structure, thus extending `R` to a
functor $D \to C^{L \circ R}$.

```
Comparison : Functor D (Eilenberg-Moore L∘R)
F₀ Comparison x = R.₀ x ,
  record
    { ν      = R.₁ (adj.counit.ε _)
    ; ν-mult =
      R.₁ (adj.counit.ε _) C.∘ M₁ (R.₁ (adj.counit.ε _))        ≡⟨ sym (R.F-∘ _ _) ⟩
      R.₁ (adj.counit.ε _ D.∘ L.₁ (R.₁ (adj.counit.ε _)))       ≡⟨ ap R.₁ (adj.counit.is-natural _ _ _) ⟩
      R.₁ (adj.counit.ε x D.∘ adj.counit.ε (L.₀ (R.₀ x)))       ≡⟨ R.F-∘ _ _ ⟩
      R.₁ (adj.counit.ε x) C.∘ R.₁ (adj.counit.ε (L.₀ (R.₀ x))) ∎
    ; ν-unit = adj.zag
    }
```

<details>
<summary> Construction of the functorial action of `Comparison`{.Agda} </summary>
```
F₁ Comparison x =
  record
    { morphism = R.₁ x
    ; commutes =
      R.₁ x C.∘ R.₁ (adj.counit.ε _)        ≡⟨ sym (R.F-∘ _ _) ⟩
      R.₁ (x D.∘ adj.counit.ε _)            ≡⟨ ap R.₁ (sym (adj.counit.is-natural _ _ _)) ⟩
      R.₁ (adj.counit.ε _ D.∘ L.₁ (R.₁ x))  ≡⟨ R.F-∘ _ _ ⟩
      R.₁ (adj.counit.ε _) C.∘ M₁ (R.₁ x)   ∎
    }
F-id Comparison = AlgebraHom-path R.F-id
F-∘ Comparison f g = AlgebraHom-path (R.F-∘ _ _)
```
</details>

An adjunction is _monadic_ if `Comparison`{.Agda} is an `equivalence of
categories`{.Agda ident="is-Equiv"}.

<!--
```agda
_ = Algebra
```
-->
