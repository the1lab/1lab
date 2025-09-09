<!--
```agda
open import Cat.Functor.Adjoint.Reflective
open import Cat.Functor.Adjoint.Compose
open import Cat.Functor.Adjoint.Hom
open import Cat.Functor.Hom.Yoneda
open import Cat.Functor.Naturality
open import Cat.Functor.Adjoint
open import Cat.Functor.Compose
open import Cat.Functor.Base
open import Cat.Functor.Hom
open import Cat.Prelude
open import Cat.Total

import Cat.Functor.Reasoning.FullyFaithful as FFr
import Cat.Functor.Reasoning as Fr
import Cat.Reasoning as Cr
```
-->

```agda
module Cat.Total.Instances.Reflective {o o' ℓ}
  {A : Precategory o ℓ} {C : Precategory o' ℓ}
  {L : Functor A C} {ι : Functor C A}
  (adj : L ⊣ ι) (reflective : is-reflective adj) (B-total : is-total A) where
```
<!--
```agda
open is-total
private
  open module C = Cr C
  module A = Cr A
  module ι =  FFr ι reflective
  module L =  Fr L
  open module B-total = is-total B-total renaming (さ to さB)
```
-->

# Subcategories of total categories

Any [[reflective subcategory]] of a [[total category]] is total.

In particular, the functor $\cA(ι-,ι-):\cC\to\psh(\cC)$ is equal to
yoneda, as $\iota$ is fully faithful.

```agda
  ι' : Functor C (PSh ℓ C)
  ι' = (precompose ι.op F∘ よ A) F∘ ι

  ni : ι' ≅ⁿ よ C
  ni = to-natural-iso record
    { eta = λ _ → NT (λ y p → ι.from p)
            λ _ _ f → ext λ g → ι.from-∘ ∙ (refl⟩∘⟨ ι.η _)
    ; inv = λ _ → yo _ (ι.F₁ id)
    ; eta∘inv = λ _ → ext λ _ f → ap ι.from (ι.eliml refl) ∙ ι.η f
    ; inv∘eta = λ _ → ext λ _ _ → ι.eliml refl ∙ ι.ε _
    ; natural = λ _ _ _ → ext λ _ _ → ι.pouncer refl }
```

Furthermore, it has a has a left adjoint $L(\sa(-\circ L))$ given by
composition of our reflector and the left adjoint to yoneda for $A$.

```agda
  L' : Functor (PSh ℓ C) C
  L' = L F∘ (さB F∘ precompose L.op)

  L'⊣ι' : L' ⊣ ι'
  L'⊣ι' = LF⊣GR (LF⊣GR (precomposite-adjunction (opposite-adjunction adj)) B-total.has-よ-adj) adj

reflective-total→is-total : is-total C
reflective-total→is-total .さ = L'
reflective-total→is-total .has-よ-adj = adjoint-natural-isor ni L'⊣ι'
```
