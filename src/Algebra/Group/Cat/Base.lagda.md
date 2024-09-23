<!--
```agda
open import Algebra.Semigroup using (is-semigroup)
open import Algebra.Monoid using (is-monoid)
open import Algebra.Group
open import Algebra.Magma using (is-magma)

open import Cat.Displayed.Univalence.Thin
open import Cat.Functor.Properties
open import Cat.Prelude

import Cat.Reasoning as Cat
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

# The category of groups {defines="category-of-groups"}

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

<!--
```agda
LiftGroup : ∀ {ℓ} ℓ' → Group ℓ → Group (ℓ ⊔ ℓ')
LiftGroup {ℓ} ℓ' G = G' where
  module G = Group-on (G .snd)
  open is-group
  open is-monoid
  open is-semigroup
  open is-magma

  G' : Group (ℓ ⊔ ℓ')
  G' .fst = el! (Lift ℓ' ⌞ G ⌟)
  G' .snd ._⋆_ (lift x) (lift y) = lift (x G.⋆ y)
  G' .snd .has-is-group .unit = lift G.unit
  G' .snd .has-is-group .inverse (lift x) = lift (G.inverse x)
  G' .snd .has-is-group .has-is-monoid .has-is-semigroup .has-is-magma .has-is-set = hlevel 2
  G' .snd .has-is-group .has-is-monoid .has-is-semigroup .associative = ap lift G.associative
  G' .snd .has-is-group .has-is-monoid .idl = ap lift G.idl
  G' .snd .has-is-group .has-is-monoid .idr = ap lift G.idr
  G' .snd .has-is-group .inversel = ap lift G.inversel
  G' .snd .has-is-group .inverser = ap lift G.inverser

G→LiftG : ∀ {ℓ} (G : Group ℓ) → Groups.Hom G (LiftGroup lzero G)
G→LiftG G .hom = lift
G→LiftG G .preserves .pres-⋆ _ _ = refl
```
-->

## The underlying set

The category of groups admits a `faithful`{.Agda ident=is-faithful}
functor into the category of sets, written $U : \rm{Groups} \to
\Sets$, which projects out the underlying set of the group. Faithfulness
of this functor says, in more specific words, that equality of group
homomorphisms can be tested by comparing the underlying morphisms of
sets.

```agda
Grp↪Sets : Functor (Groups ℓ) (Sets ℓ)
Grp↪Sets = Forget-structure (Group-structure _)

Grp↪Sets-is-faithful : is-faithful (Grp↪Sets {ℓ})
Grp↪Sets-is-faithful = Structured-hom-path (Group-structure _)
```
