<!--
```agda
open import Cat.Diagram.Colimit.Coproduct
open import Cat.Diagram.Coproduct.Indexed
open import Cat.Diagram.Colimit.Base
open import Cat.Functor.Adjoint.Hom
open import Cat.Functor.Naturality
open import Cat.Instances.Discrete
open import Cat.Instances.Product
open import Cat.Diagram.Terminal
open import Cat.Functor.Adjoint
open import Cat.Instances.Sets
open import Cat.Functor.Hom
open import Cat.Prelude

import Cat.Reasoning
```
-->

```agda
module Cat.Diagram.Coproduct.Copower where
```

# Copowers {defines="copower copowered"}

Let $\cC$ be a category admitting [$\kappa$-small] [indexed
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
$\cC$ does indeed admit coproducts indexed by _any_ $\kappa$-small
set, then the copowering construction extends to a functor $\Sets_\kappa
\times \cC \to \cC$.

The notion of copowering gives us slick terminology for a category which
admits all $\kappa$-small coproducts, but not necessarily all
$\kappa$-small [colimits]: Such a category is precisely one copowered
over $\Sets_\kappa$.

[colimits]: Cat.Diagram.Colimit.Base.html

<!--
```agda
module Copowers
  {o ℓ} {C : Precategory o ℓ}
  (coprods : (S : Set ℓ) → has-coproducts-indexed-by C ∣ S ∣)
  where

  open Indexed-coproduct
  open Cat.Reasoning C
  open Functor
```
-->

```agda
  _⊗_ : Set ℓ → Ob → Ob
  X ⊗ A = coprods X (λ _ → A) .ΣF
```

Copowers satisfy a universal property: $X \otimes A$ is a [[representing object]]
for the functor that takes an object $B$ to the $X$th power of the set of morphisms
from $A$ to $B$; in other words, we have a natural isomorphism
$\hom_\cC(X \otimes A, -) \cong \hom_{\Sets}(X, \hom_\cC(A, -))$.

```agda
  copower-hom-iso
    : ∀ {X A}
    → Hom-from C (X ⊗ A) ≅ⁿ Hom-from (Sets ℓ) X F∘ Hom-from C A
  copower-hom-iso {X} {A} = iso→isoⁿ
    (λ _ → equiv→iso (hom-iso (coprods X (λ _ → A))))
    (λ _ → ext λ _ _ → assoc _ _ _)
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
    coprods X (λ _ → A) .unique _ λ i → pullr (coprods _ _ .commute) ∙ extendl (coprods _ _ .commute)
```

```agda
  ∐! : (Idx : Type ℓ) ⦃ hl : H-Level Idx 2 ⦄ (F : Idx → Ob) → Ob
  ∐! Idx F = ΣF (coprods (el! Idx) F)

  module ∐! (Idx : Type ℓ) ⦃ hl : H-Level Idx 2 ⦄ (F : Idx → Ob) =
    Indexed-coproduct (coprods (el! Idx) F)

  _⊗!_ : (Idx : Type ℓ) ⦃ hl : H-Level Idx 2 ⦄ → Ob → Ob
  I ⊗! X = el! I ⊗ X

  module ⊗! (Idx : Type ℓ) ⦃ hl : H-Level Idx 2 ⦄ (X : Ob) =
    Indexed-coproduct (coprods (el! Idx) (λ _ → X))
```


<!--
```agda
cocomplete→copowering
  : ∀ {o ℓ} {C : Precategory o ℓ}
  → is-cocomplete ℓ ℓ C → Functor (Sets ℓ ×ᶜ C) C
cocomplete→copowering colim = Copowers.Copowering λ S F → Colimit→IC _ F (colim _)
```
-->

## Constant objects

If $\cC$ has a terminal object $\star$, then the copower $S \times
\star$ is referred to as the **constant object** on $S$. By simplifying
the universal property of the copower, we obtain that constant objects
assemble into a functor left adjoint to $\cC(\star,-)$.^[This right
adjoint is often called the **global sections functor**.]

<!--
```agda
module Consts
  {o ℓ} {C : Precategory o ℓ}
  (term : Terminal C)
  (coprods : (S : Set ℓ) → has-coproducts-indexed-by C ∣ S ∣)
  where

  open Indexed-coproduct
  open Cat.Reasoning C
  open Copowers coprods
  open Functor

  open Terminal term renaming (top to *C)
```
-->

```agda
  Constant-objects : Functor (Sets ℓ) C
  Constant-objects .F₀ S = S ⊗ *C
  Constant-objects .F₁ f = coprods _ _ .match λ i → coprods _ _ .ι (f i)
  Constant-objects .F-id = sym $ coprods _ _ .unique _ λ i → idl _
  Constant-objects .F-∘ f g = sym $ coprods _ _ .unique _ λ i →
    pullr (coprods _ _ .commute) ∙ coprods _ _ .commute

  Const⊣Γ : Constant-objects ⊣ Hom-from _ *C
  Const⊣Γ = hom-iso→adjoints
    (λ f x → f ∘ coprods _ _ .ι x)
    (is-iso→is-equiv (iso
      (λ h → coprods _ _ .match h)
      (λ h → ext λ i → coprods _ _ .commute)
      (λ x → sym (coprods _ _ .unique _ λ i → refl))))
    (λ g h x → ext λ y → pullr (pullr (coprods _ _ .commute)))
```
