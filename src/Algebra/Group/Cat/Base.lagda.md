<!--
```agda
open import Algebra.Prelude
open import Algebra.Group

open import Cat.Displayed.Univalence.Thin
open import Cat.Functor.Properties
open import Cat.Prelude
```
-->

```agda
module Algebra.Group.Cat.Base where
```

<!--
```agda
private variable
  ℓ : Level
open Cat.Displayed.Univalence.Thin public
open Functor
import Cat.Reasoning as CR
```
-->

# The category of groups

The category of groups, as the name implies, has its objects the
`Groups`{.Agda ident=Group}, with the morphisms between them the `group
homomorphisms`{.Agda ident=is-group-hom}.

```agda
open Group-on
open is-group-hom

Group-structure : ∀ ℓ → Thin-structure ℓ Group-on
Group-structure ℓ .is-hom f G G' = el! (is-group-hom G G' f)

Group-structure ℓ .id-is-hom        .pres-⋆ x y = refl
Group-structure ℓ .∘-is-hom f g α β .pres-⋆ x y =
  ap f (β .pres-⋆ x y) ∙ α .pres-⋆ _ _

Group-structure ℓ .id-hom-unique {s = s} {t = t} α β i =
  record
    { _⋆_          = λ x y → α .pres-⋆ x y i
    ; has-is-group =
      is-prop→pathp (λ i → is-group-is-prop {_*_ = λ x y → α .pres-⋆ x y i})
        (s .has-is-group)
        (t .has-is-group)
        i
    }

Groups : ∀ ℓ → Precategory (lsuc ℓ) ℓ
Groups ℓ = Structured-objects (Group-structure ℓ)

Groups-is-category : ∀ {ℓ} → is-category (Groups ℓ)
Groups-is-category = Structured-objects-is-category (Group-structure _)

instance
  Groups-equational : ∀ {ℓ} → is-equational (Group-structure ℓ)
  Groups-equational .is-equational.invert-id-hom x .pres-⋆ a b = sym (x .pres-⋆ a b)

module Groups {ℓ} = Cat (Groups ℓ)

Group : ∀ ℓ → Type (lsuc ℓ)
Group _ = Groups.Ob

to-group : ∀ {ℓ} {A : Type ℓ} → make-group A → Group ℓ
to-group {A = A} mg = el A (mg .make-group.group-is-set) , (to-group-on mg)
```

## The underlying set

The category of groups admits a `faithful`{.Agda ident=is-faithful}
functor into the category of sets, written $U : \rm{Groups} \to
\Sets$, which projects out the underlying set of the group. Faithfulness
of this functor says, in more specific words, that equality of group
homomorphisms can be tested by comparing the underlying morphisms of
sets.

```agda
Forget : Functor (Groups ℓ) (Sets ℓ)
Forget = Forget-structure (Group-structure _)

Forget-is-faithful : is-faithful (Forget {ℓ})
Forget-is-faithful = Structured-hom-path (Group-structure _)
```
