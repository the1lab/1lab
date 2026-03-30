open import Cat.Functor.Equivalence hiding (Equivalence) renaming (is-equivalence to is-equivalenceᶜ)
open import Cat.Functor.Naturality
open import Cat.Functor.Adjoint renaming (_⊣_ to _⊣ᶜ_)
open import Cat.Bi.Adjoint
open import Cat.Bi.Base
open import Cat.Prelude

import Cat.Bi.Reasoning as Br
import Cat.Reasoning as Cr

module Cat.Bi.Equivalence where

private variable
  o o' h h' ℓ ℓ' : Level
  B C : Prebicategory o h ℓ

module _ (C : Prebicategory o h ℓ) where
  open Prebicategory C
  private
    module C  = Br C
    module CH = C.Hom

  record is-equivalence {A B} (f : A ↦ B) : Type (h ⊔ ℓ) where
    open Adjoint C
    field
      inv : B ↦ A
      inv-adjoint : f ⊣ inv

    open _⊣_ inv-adjoint public

    field
      unit-iso   : CH.is-invertible η
      counit-iso : CH.is-invertible ε

  record Equivalence A B : Type (h ⊔ ℓ) where
    field
      to : A ↦ B
      to-equiv : is-equivalence to

open Pseudonatural

is-equivalenceᵖ : {F G : Lax-functor B C} → F =>ₚ G → Type _
is-equivalenceᵖ {C = C} α = ∀ X → is-equivalence C (α .σ X)

record Equivalenceᵖ
  {o h ℓ o' h' ℓ'} {B : Prebicategory o h ℓ} {C : Prebicategory o' h' ℓ'}
  (F : Lax-functor B C) (G : Lax-functor B C) : Type (o ⊔ h ⊔ ℓ ⊔ h' ⊔ ℓ')
  where
  field
    to : F =>ₚ G
    to-equiv : is-equivalenceᵖ to

module _ {C : Precategory o h} {D : Precategory o h} {F : Functor C D} where

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
  is-equivalence→is-equivalenceᶜ eqv .is-equivalenceᶜ.unit-iso =
    is-invertibleⁿ→is-invertible (is-equivalence.unit-iso eqv)
  is-equivalence→is-equivalenceᶜ eqv .is-equivalenceᶜ.counit-iso =
    is-invertibleⁿ→is-invertible (is-equivalence.counit-iso eqv)

