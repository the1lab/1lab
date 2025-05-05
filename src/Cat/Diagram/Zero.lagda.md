<!--
```agda
open import Cat.Diagram.Terminal
open import Cat.Diagram.Initial
open import Cat.Prelude

import Cat.Reasoning
```
-->

```agda
module Cat.Diagram.Zero where

```

<!--
```agda
module _ {o h} (C : Precategory o h) where
  open Cat.Reasoning C
```
-->

# Zero objects {defines="zero-object"}

::: {.popup .keep}
In some categories, [[initial]] and [[terminal]] objects
coincide. When this occurs, we call the object a **zero object**.
:::

```agda
  record is-zero (ob : Ob) : Type (o ⊔ h) where
    field
      has-is-initial  : is-initial C ob
      has-is-terminal : is-terminal C ob

  record Zero : Type (o ⊔ h) where
    field
      ∅       : Ob
      has-is-zero : is-zero ∅

    open is-zero has-is-zero public

    terminal : Terminal C
    terminal = record { top = ∅ ; has⊤ = has-is-terminal }

    initial : Initial C
    initial = record { bot = ∅ ; has⊥ = has-is-initial }

    open Terminal terminal public hiding (top)
    open Initial initial public hiding (bot)
```

::: {.definition #zero-morphism}
If $\cC$ has a [[zero object]] $\emptyset$, then every $\hom$-set
$\cC(x, y)$ is [[pointed]], by the composite $$x \xto{!} \emptyset
\xto{¡} y$$; we refer to a map which factors through a zero object as a
**zero morphism**.
:::

```agda
    zero→ : ∀ {x y} → Hom x y
    zero→ = ¡ ∘ !

    zero-∘l : ∀ {x y z} → (f : Hom y z) → f ∘ zero→ {x} {y} ≡ zero→
    zero-∘l f = pulll (sym (¡-unique (f ∘ ¡)))

    zero-∘r : ∀ {x y z} → (f : Hom x y) → zero→ {y} {z} ∘ f ≡ zero→
    zero-∘r f = pullr (sym (!-unique (! ∘ f)))

    zero-comm : ∀ {x y z} → (f : Hom y z) → (g : Hom x y) → f ∘ zero→ ≡ zero→ ∘ g
    zero-comm f g = zero-∘l f ∙ sym (zero-∘r g)

    zero-comm-sym : ∀ {x y z} → (f : Hom y z) → (g : Hom x y) → zero→ ∘ f ≡ g ∘ zero→
    zero-comm-sym f g = zero-∘r f ∙ sym (zero-∘l g)
```

In the presence of a zero object, zero morphisms are unique with the
property of being *constant*, in the sense that $0 \circ f = 0 \circ g$
for any parallel pair $f, g : x \to y$. (By duality, they are also
unique with the property of being *coconstant*.)

```agda
    zero-unique
      : ∀ {x y} {z : Hom x y}
      → (∀ {w} (f g : Hom w x) → z ∘ f ≡ z ∘ g)
      → z ≡ zero→
    zero-unique const = sym (idr _) ∙ const _ zero→ ∙ zero-∘l _
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

<!--
```agda
module _ {o h} {C : Precategory o h} where
  open Cat.Reasoning C
  private unquoteDecl is-zero-eqv = declare-record-iso is-zero-eqv (quote is-zero)
  private unquoteDecl zero-eqv = declare-record-iso zero-eqv (quote Zero)

  is-zero-is-prop : ∀ {x} → is-prop (is-zero C x)
  is-zero-is-prop = Iso→is-hlevel 1 is-zero-eqv (hlevel 1)

  instance
    HLevel-is-zero : ∀ {x} {n} → H-Level (is-zero C x) (1 + n)
    HLevel-is-zero = prop-instance is-zero-is-prop

  instance
    Extensional-Zero
      : ∀ {ℓr}
      → ⦃ sa : Extensional Ob ℓr ⦄
      → Extensional (Zero C) ℓr
    Extensional-Zero ⦃ sa ⦄ =
      embedding→extensional
        (Iso→Embedding zero-eqv ∙emb (fst , Subset-proj-embedding (λ _ → hlevel 1)))
        sa
```
-->
