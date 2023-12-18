<!--
```agda
open import Cat.Prelude
```
-->

```agda
module Cat.Diagram.Zero {o h} (C : Precategory o h) where

open import Cat.Diagram.Initial C
open import Cat.Diagram.Terminal C
```

<!--
```agda
open import Cat.Reasoning C
```
-->

# Zero objects

In some categories, `Initial`{.Agda} and `Terminal`{.Agda} objects
coincide. When this occurs, we call the object a **zero object**.

```agda
record is-zero (ob : Ob) : Type (o ⊔ h) where
  field
    has-is-initial  : is-initial ob
    has-is-terminal : is-terminal ob

record Zero : Type (o ⊔ h) where
  field
    ∅       : Ob
    has-is-zero : is-zero ∅

  open is-zero has-is-zero public

  terminal : Terminal
  terminal = record { top = ∅ ; has⊤ = has-is-terminal }

  initial : Initial
  initial = record { bot = ∅ ; has⊥ = has-is-initial }

  open Terminal terminal public hiding (top)
  open Initial initial public hiding (bot)
```

A curious fact about zero objects is that their existence implies that
every hom set is inhabited!

```agda
  zero→ : ∀ {x y} → Hom x y
  zero→ = ¡ ∘ !

  zero-∘l : ∀ {x y z} → (f : Hom y z) → f ∘ zero→ {x} {y} ≡ zero→
  zero-∘l f = pulll (sym (¡-unique (f ∘ ¡)))

  zero-∘r : ∀ {x y z} → (f : Hom x y) → zero→ {y} {z} ∘ f ≡ zero→
  zero-∘r f = pullr (sym (!-unique (! ∘ f)))

  zero-comm : ∀ {x y z} → (f : Hom y z) → (g : Hom x y) → f ∘ zero→  ≡ zero→ ∘ g
  zero-comm f g = zero-∘l f ∙ sym (zero-∘r g)

  zero-comm-sym : ∀ {x y z} → (f : Hom y z) → (g : Hom x y) → zero→ ∘ f  ≡ g ∘ zero→
  zero-comm-sym f g = zero-∘r f ∙ sym (zero-∘l g)
```

## Intuition

<!-- [TODO: Reed M, 15/02/2022]  Link to the category of groups -->

Most categories that have zero objects have enough structure to rule out
*totally* trivial structures like the empty set, but not enough
structure to cause the initial and [[terminal objects]] to "separate".
The canonical example here is the category of groups: the unit rules out
a completely trivial group, yet there's nothing else that would require
the initial object to have any more structure.

Another point of interest is that any category with zero objects is
canonically enriched in pointed sets: the `zero→`{.Agda} morphism from
earlier acts as the designated basepoint for each of the hom sets.
