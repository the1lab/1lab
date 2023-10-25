<!--
```agda
open import Cat.Prelude
open import Cat.Functor.Adjoint
```
-->

```agda
module IsbellDuality.IsbellDuality where

open import Cat.Functor.Base
open import Cat.Functor.Kan.Nerve
open import Cat.Functor.Hom

CoPSh : ∀ κ {o ℓ} → Precategory o ℓ → Precategory _ _
CoPSh κ C = Cat[ C , Sets κ ] ^op

module _ {o κ} (C : Precategory o κ) where
  -- coyoneda embedding
  z : Functor C (CoPSh κ C)
  z = Functor.op (よ (C ^op))

open import Cat.Diagram.Colimit.Base
open import Cat.Diagram.Limit.Base

module _ {o}{l}{x} {y} {C : Precategory o l} where


  open import Cat.Diagram.Duals

  is-complete-is-cocomplete-op : is-complete x y C ->  is-cocomplete x y (C ^op)
  is-complete-is-cocomplete-op isCompl F = Co-limit→Colimit _ (isCompl _)

module _ {o ℓ} (C : Precategory o ℓ) where

  open import Cat.Instances.Functor.Limits
  open import Cat.Instances.Sets.Complete
  
  CoPSh-cocomplete : ∀ κ → is-cocomplete κ κ (CoPSh κ C)
  CoPSh-cocomplete κ = is-complete-is-cocomplete-op {C = Cat[ C , Sets κ ]} (Functor-cat-is-complete (Sets-is-complete {o = κ}))

Spec : ∀ κ (C : Precategory κ κ) → Functor (CoPSh κ C) (PSh κ C)
Spec κ C = Nerve (z _)

-- agda refused to figure out implicits quickly so we help it
IsbellDuality : ∀ κ  {C : Precategory κ κ} -> _ ⊣ Spec _ C
IsbellDuality κ {C} = Realisation⊣Nerve {C = C} {D = CoPSh κ C} (z C) (CoPSh-cocomplete _ _)
```
