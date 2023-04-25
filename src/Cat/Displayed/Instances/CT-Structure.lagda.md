<!--
```agda
open import Cat.Displayed.Cartesian.Discrete
open import Cat.Diagram.Product.Solver
open import Cat.Displayed.Cartesian
open import Cat.Displayed.Functor
open import Cat.Diagram.Product
open import Cat.Displayed.Base
open import Cat.Prelude

import Cat.Displayed.Instances.Simple as Simple
import Cat.Reasoning
```
-->

```agda
module Cat.Displayed.Instances.CT-Structure
  {o ℓ} (B : Precategory o ℓ)
  (has-prods : ∀ X Y → Product B X Y)
  where

open Precategory B
open Binary-products B has-prods
open Simple B has-prods
```

# CT Structures

CT-Structures are a refinement of [simple fibrations], which allow us
to model type theories where the contexts aren't necessarily
representable as types. This is done by defining a `CT-Structure`{.Agda}
(short for Context and Type Structure) on our category of contexts,
which allows us to distinguish certain contexts as denoting types
(for instance, singleton contexts, or possibly the empty context if we
have unit types). A CT-structure is quite simple, consisting of only
a predicate on contexts meant to denote which ones are types, along
with the restriction that there is at least one type, to prevent
the entire structure from becoming degenerate.

[simple fibrations]: Cat.Displayed.Instances.Simple.html
[simple fibration]: Cat.Displayed.Instances.Simple.html

```agda
record CT-Structure (s : Level) : Type (o ⊔ lsuc s) where
  field
    is-tp : Ob → Prop s
    ∃-tp : ∃[ tp ∈ Ob ] (∣ is-tp tp ∣)

open CT-Structure
```

We can construct a displayed category over our category of contexts in
much the same manner as the [simple fibration]; the only difference
is that we restrict the displayed object to objects that the
CT-structure distinguishes as types.


```agda
simple-ct : ∀ {s} → CT-Structure s → Displayed B (o ⊔ s) ℓ
simple-ct ct .Displayed.Ob[_] Γ = Σ[ X ∈ Ob ] ∣ is-tp ct X ∣
simple-ct ct .Displayed.Hom[_] {Γ} {Δ} u X Y = Hom (Γ ⊗₀ X .fst) (Y .fst)
simple-ct ct .Displayed.Hom[_]-set {Γ} {Δ} u X Y = Hom-set (Γ ⊗₀ X .fst) (Y .fst)
simple-ct ct .Displayed.id′ = π₂
simple-ct ct .Displayed._∘′_ {f = u} {g = v} f g = f ∘ ⟨ v ∘ π₁ , g ⟩
simple-ct ct .Displayed.idr′ {f = u} f =
  f ∘ ⟨ (id ∘ π₁) , π₂ ⟩ ≡⟨ products! B has-prods ⟩
  f                      ∎
simple-ct ct .Displayed.idl′ {f = u} f =
  π₂ ∘ ⟨ u ∘ π₁ , f ⟩ ≡⟨ products! B has-prods ⟩
  f                   ∎
simple-ct ct .Displayed.assoc′ {f = u} {g = v} {h = w} f g h =
  f ∘ ⟨ (v ∘ w) ∘ π₁ , g ∘ ⟨ w ∘ π₁ , h ⟩ ⟩ ≡⟨ products! B has-prods ⟩
  (f ∘ ⟨ v ∘ π₁ , g ⟩) ∘ ⟨ w ∘ π₁ , h ⟩     ∎
```

# Fibration Structure

Much like the simple fibration, the simple fibration associated to a
CT-structure also deserves its name.

```agda
open Cartesian-fibration
open Cartesian-lift
open is-cartesian

simple-ct-fibration : ∀ {s} (ct : CT-Structure s) → Cartesian-fibration (simple-ct ct)
simple-ct-fibration ct .has-lift u Y .x′ = Y
simple-ct-fibration ct .has-lift u Y .lifting = π₂
simple-ct-fibration ct .has-lift u Y .cartesian .universal _ h = h
simple-ct-fibration ct .has-lift u Y .cartesian .commutes g h = π₂∘⟨⟩
simple-ct-fibration ct .has-lift u Y .cartesian .unique {m = g} {h′ = h} h' p =
  h'                   ≡˘⟨ π₂∘⟨⟩ ⟩
  π₂ ∘ ⟨ g ∘ π₁ , h' ⟩ ≡⟨ p ⟩
  h ∎
```

# Embeddings

There is an evident embedding of the simple fibration associated with a
CT-structure into the simple fibration.

```agda
simple-ct→simple
  : ∀ {s} → (ct : CT-Structure s)
  → Displayed-functor (simple-ct ct) simple Id
simple-ct→simple ct .Displayed-functor.F₀′ = fst
simple-ct→simple ct .Displayed-functor.F₁′ f = f
simple-ct→simple ct .Displayed-functor.F-id′ = refl
simple-ct→simple ct .Displayed-functor.F-∘′ = refl
```

Furthermore, if $\cB$ is inhabited, then we can construct a
CT-Structure that considers every context a type.

<!--
  [TODO: Reed M, 18/10/2022]
  When we have displayed adjoints, show that this gives an adjunction.
-->

```agda
all-types : Ob → CT-Structure lzero
all-types X .is-tp _ = el ⊤ (hlevel 1)
all-types X .∃-tp = inc (X , tt)

simple→simple-ct : ∀ {X} → Displayed-functor simple (simple-ct (all-types X)) Id
simple→simple-ct .Displayed-functor.F₀′ X = X , tt
simple→simple-ct .Displayed-functor.F₁′ f = f
simple→simple-ct .Displayed-functor.F-id′ = refl
simple→simple-ct .Displayed-functor.F-∘′ = refl
```
