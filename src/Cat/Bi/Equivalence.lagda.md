<!--
```agda
open import Cat.Bi.Diagram.Adjunction
open import Cat.Functor.Equivalence hiding (Equivalence) renaming (is-equivalence to is-equivalenceᶜ)
open import Cat.Functor.Naturality
open import Cat.Functor.Adjoint renaming (_⊣_ to _⊣ᶜ_)
open import Cat.Bi.Base
open import Cat.Prelude

import Cat.Bi.Reasoning as Br
import Cat.Reasoning as Cr
```
-->

```agda
module Cat.Bi.Equivalence where
```

<!--
```agda
private variable
  o o' h h' ℓ ℓ' : Level
  B C : Prebicategory o h ℓ

module _ (C : Prebicategory o h ℓ) where
  open Prebicategory C
  private
    module C  = Br C
    module CH = C.Hom
```
-->

# Equivalences in a bicategory

In any precategory, [[isomorphism]] acts as an internal proxy for
"sameness" of objects.[^1]  However, in a bicategory, isomorphism is
usually too strict a notion, in the sense that requiring that a 1-cell
$f : A \to B$ has an inverse $f\inv : B \to A$ such that $f f\inv = \id$
(and $f\inv f = \id$) is too strong, excluding cases where e.g., $f
f\inv$ essentially acts like the identity despite not being equal to it.
Instead, following the bicategorical ethos, we should require that these
identities hold only up to 2-cell isomorphism.

In addition, we want the specified 2-cell isomorphisms to be compatible
with the coherence data of the bicategory.  Considering our prototypical
bicategory $\Cat$, we recall that an [[equivalence of categories]] is
given by a pair of functors $F,G$ with natural isomorphisms $\eta : \Id
\To G F$ and $\epsilon : F G \To \Id$, such that $\eta$ and $\epsilon$
satisfy the triangle identities of an [[adjunction]].[^2]  Generalizing
this, we get the definition of **equivalence** in a bicategory.

[^1]: In a [[univalent category]], this intuition is also technically precise.
[^2]:
    As [we have shown](Cat.Functor.Equivalence.Path.html), this notion
    also characterizes paths between univalent categories.

```agda
  record is-equivalence {A B} (f : A ↦ B) : Type (h ⊔ ℓ) where
    open Adjointᵇ C
    field
      inv : B ↦ A
      inv-adjoint : f ⊣ inv

    open _⊣_ inv-adjoint public

    field
      unit-iso   : CH.is-invertible η
      counit-iso : CH.is-invertible ε
```

In words, a 1-cell $f : A \to B$ in $\bicat{C}$ is an equivalence if
there is a 1-cell $f\inv : B \to A$ in the opposite direction such that
$f\inv$ is an inverse to $f$ up to chosen 2-cell isomorphisms satisfying
the triangle equalities of an [adjunction in] $\bicat{C}$.

[adjunction in]: Cat.Bi.Diagram.Adjunction.html

<!--
```agda
  record Equivalence A B : Type (h ⊔ ℓ) where
    field
      to : A ↦ B
      to-equiv : is-equivalence to
```
-->

## Pseudonatural equivalences

<!--
```agda
open Pseudonatural
```
-->

We can use the notion of equivalence to relate lax functors between
bicategories, similarly to how [[natural isomorphisms]] relate functors
between categories.

If $F$ and $G$ are lax functors $\bicat{B} \to \bicat{C}$, we define a
**pseudonatural equivalence** to be a pseudonatural transformation $F
\To G$ which is a componentwise equivalence.

```agda
is-equivalenceᵖ : {F G : Lax-functor B C} → F =>ₚ G → Type _
is-equivalenceᵖ {C = C} α = ∀ X → is-equivalence C (α .σ X)
```

<!--
TODO: Show that this definition coincides with an equivalence in the
pseudofunctor category.
-->

<!--
```agda
record Equivalenceᵖ
  {o h ℓ o' h' ℓ'} {B : Prebicategory o h ℓ} {C : Prebicategory o' h' ℓ'}
  (F : Lax-functor B C) (G : Lax-functor B C) : Type (o ⊔ h ⊔ ℓ ⊔ h' ⊔ ℓ')
  where
  field
    to : F =>ₚ G
    to-equiv : is-equivalenceᵖ to
```
-->

## Equivalences in $\Cat$

We quickly verify that a bicategorical equivalence in $\Cat$ is
logically equivalent to an [[equivalence of categories]].

<!--
```agda
module _ {C : Precategory o h} {D : Precategory o h} {F : Functor C D} where
```
-->

```agda
  is-equivalenceᶜ→is-equivalence : is-equivalenceᶜ F → is-equivalence (Cat o h) F
  is-equivalenceᶜ→is-equivalence eqv .is-equivalence.inv = is-equivalenceᶜ.F⁻¹ eqv
  is-equivalenceᶜ→is-equivalence eqv .is-equivalence.inv-adjoint =
    adjointᶜ→adjoint (is-equivalenceᶜ.F⊣F⁻¹ eqv)
  is-equivalenceᶜ→is-equivalence eqv .is-equivalence.unit-iso =
    invertible→invertibleⁿ
      (is-equivalenceᶜ.F⊣F⁻¹ eqv ._⊣ᶜ_.unit) (is-equivalenceᶜ.unit-iso eqv)
  is-equivalenceᶜ→is-equivalence eqv .is-equivalence.counit-iso =
    invertible→invertibleⁿ
      (is-equivalenceᶜ.F⊣F⁻¹ eqv ._⊣ᶜ_.counit) (is-equivalenceᶜ.counit-iso eqv)

  is-equivalence→is-equivalenceᶜ : is-equivalence (Cat o h) F → is-equivalenceᶜ F
  is-equivalence→is-equivalenceᶜ eqv .is-equivalenceᶜ.F⁻¹   = is-equivalence.inv eqv
  is-equivalence→is-equivalenceᶜ eqv .is-equivalenceᶜ.F⊣F⁻¹ =
    adjoint→adjointᶜ (is-equivalence.inv-adjoint eqv)
  is-equivalence→is-equivalenceᶜ eqv .is-equivalenceᶜ.has-is-equivalence =
    record where
      unit-iso   = is-invertibleⁿ→is-invertible (is-equivalence.unit-iso eqv)
      counit-iso = is-invertibleⁿ→is-invertible (is-equivalence.counit-iso eqv)
```
