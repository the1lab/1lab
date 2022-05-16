```agda
open import Cat.Diagram.Coproduct.Indexed
open import Cat.Diagram.Colimit.Base
open import Cat.Instances.Discrete
open import Cat.Instances.Product
open import Cat.Prelude

import Cat.Reasoning

module Cat.Diagram.Coproduct.Copower where
```

# Copowers

Let $\ca{C}$ be a category admitting [$\kappa$-small] [indexed
coproducts], for example a $\kappa$-[cocomplete] category. In the same
way that (in ordinary arithmetic) the iterated product of a bunch of
copies of the same factor

[$\kappa$-small]: 1Lab.intro.html#universes-and-size-issues
[indexed coproducts]: Cat.Diagram.Coproduct.Indexed.html
[cocomplete]: Cat.Diagram.Colimit.Base.html#cocompleteness

$$
\underbrace{a \times a \times \dots \times a}_{n}
$$

is called a "power", we refer to the coproduct $\coprod_{X} A$ of many
copies of an object $X$ indexed by a $\kappa$-small set $X$ as the
**copower** of $A$ by $X$, and alternatively denote it $X \otimes A$. If
$\ca{C}$ does indeed admit coproducts indexed by _any_ $\kappa$-small
set, then the copowering construction extends to a functor $\sets_\kappa
\times \ca{C} \to \ca{C}$.

The notion of copowering gives us slick terminology for a category which
admits all $\kappa$-small coproducts, but not necessarily all
$\kappa$-small [colimits]: Such a category is precisely one copowered
over $\sets_\kappa$.

[colimits]: Cat.Diagram.Colimit.Base.html

<!--
```agda
module
  _ {o ℓ} {C : Precategory o ℓ}
  (coprods : (S : Set ℓ) (F : ∣ S ∣ → Precategory.Ob C) → Indexed-coproduct C F)
  where

  open Functor
  open is-indexed-coproduct
  open Indexed-coproduct
  open Cat.Reasoning C
```
-->

```agda
  _⊗_ : Set ℓ → Ob → Ob
  X ⊗ A = coprods X (λ _ → A) .ΣF
```

The action of the copowering functor is given by simultaneously changing
the indexing along a function of sets $f : X \to Y$ and changing the
underlying object by a morphism $g : A \to B$. This is functorial by the
uniqueness properties of colimiting maps.

```agda
  Copowering : Functor (Sets ℓ ×ᶜ C) C
  Copowering .F₀ (X , A) = X ⊗ A
  Copowering .F₁ {X , A} {Y , B} (idx , obj) =
    coprods X (λ _ → A) .match λ i → coprods Y (λ _ → B) .ι (idx i) ∘ obj
  Copowering .F-id {X , A} = sym $
    coprods X (λ _ → A) .unique _ λ i → sym id-comm
  Copowering .F-∘ {X , A} f g = sym $
    coprods X (λ _ → A) .unique _ λ i →
      pullr (coprods _ _ .commute) ∙ extendl (coprods _ _ .commute)

cocomplete→copowering
  : ∀ {o ℓ} {C : Precategory o ℓ}
  → is-cocomplete ℓ ℓ C → Functor (Sets ℓ ×ᶜ C) C
cocomplete→copowering colim = Copowering λ S F →
  Colimit→IC _ (is-hlevel-suc 2 (S .is-tr)) (Disc-adjunct F) (colim _)
```
