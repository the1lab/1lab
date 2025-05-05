<!--
```agda
open import Cat.Prelude

import Cat.Morphism
```
-->

```agda
module Cat.Diagram.Initial where
```

<!--
```agda
module _ {o h} (C : Precategory o h) where
  open Cat.Morphism C
```
-->

# Initial objects {defines="initial-object initial"}

::: {.popup .keep}
An object $\bot$ of a category $\mathcal{C}$ is said to be **initial**
if there exists a _unique_ map from $\bot$ to any other object:

```agda
  is-initial : Ob → Type _
  is-initial ob = ∀ x → is-contr (Hom ob x)
```
:::

```agda
  record Initial : Type (o ⊔ h) where
    field
      bot  : Ob
      has⊥ : is-initial bot
```

We refer to the centre of contraction as `¡`{.Agda}. Since it inhabits a
contractible type, it is unique.

```agda
    ¡ : ∀ {x} → Hom bot x
    ¡ = has⊥ _ .centre

    ¡-unique : ∀ {x} (h : Hom bot x) → ¡ ≡ h
    ¡-unique = has⊥ _ .paths

    ¡-unique₂ : ∀ {x} (f g : Hom bot x) → f ≡ g
    ¡-unique₂ = is-contr→is-prop (has⊥ _)

  open Initial
```

## Intuition

The intuition here is that we ought to think about an initial object as
having "the least amount of structure possible", insofar that it can be
mapped _into_ any other object. For the category of `Sets`{.Agda}, this
is the empty set; there is no required structure beyond "being a set",
so the empty set sufficies.

<!--
[TODO: Reed M, 15/02/2022] Link to the categories in question
(once the exist!)
-->

In more structured categories, the situation becomes a bit more
interesting. Once our category has enough structure that we can't build
maps from a totally trivial thing, the initial object begins to behave
like a notion of **Syntax** for our category.  The idea here is that we
have a _unique_ means of interpreting our syntax into any other object,
which is exhibited by the universal map `¡`{.Agda}

## Uniqueness

One important fact about initial objects is that they are **unique** up
to isomorphism:

```agda
  ⊥-unique : (i i' : Initial) → bot i ≅ bot i'
  ⊥-unique i i' = make-iso (¡ i) (¡ i') (¡-unique₂ i' _ _) (¡-unique₂ i _ _)
```

Additionally, if $C$ is a category, then the space of initial objects is
a proposition:

```agda
  ⊥-is-prop : is-category C → is-prop Initial
  ⊥-is-prop ccat x1 x2 i .bot =
    Univalent.iso→path ccat (⊥-unique x1 x2) i

  ⊥-is-prop ccat x1 x2 i .has⊥ ob =
    is-prop→pathp
      (λ i → is-contr-is-prop
        {A = Hom (Univalent.iso→path ccat (⊥-unique x1 x2) i) _})
      (x1 .has⊥ ob) (x2 .has⊥ ob) i
```

## Strictness {defines="strict-initial-object"}

::: {.popup .keep}
An [[initial object]] $\bot$ is said to be **strict** if every morphism
$f : X \to \bot$ into it is [[invertible]].

This generalises to an arbitrary $\cC$ the observation that if one can
write a function of [[sets]] $X \to \emptyset$ then $X$ must itself be
empty.
:::

This is an instance of the more general notion of [van Kampen colimits].

[van Kampen colimits]: https://ncatlab.org/nlab/show/van+Kampen+colimit

```agda
  is-strict-initial : Initial → Type _
  is-strict-initial i = ∀ x → (f : Hom x (i .bot)) → is-invertible f

  record Strict-initial : Type (o ⊔ h) where
    field
      initial : Initial
      has-is-strict : is-strict-initial initial
```

Strictness is a property of, not structure on, an initial object.

```agda
  is-strict-initial-is-prop : ∀ i → is-prop (is-strict-initial i)
  is-strict-initial-is-prop i = hlevel 1
```

As maps out of initial objects are unique, it suffices to show that
every map $\text{!`} \circ f = \id$ for every $f : X \to \bot$ to establish that $\bot$ is a
strict initial object.

```agda
  make-is-strict-initial
    : (i : Initial)
    → (∀ x → (f : Hom x (i .bot)) → (¡ i) ∘ f ≡ id)
    → is-strict-initial i
  make-is-strict-initial i p x f =
    make-invertible (¡ i) (¡-unique₂ i (f ∘ ¡ i) id) (p x f)
```

<!--
```agda
module _ {o h} {C : Precategory o h} where
  open Cat.Morphism C
  private unquoteDecl eqv = declare-record-iso eqv (quote Initial)

  instance
    Extensional-Initial
      : ∀ {ℓr}
      → ⦃ sa : Extensional Ob ℓr ⦄
      → Extensional (Initial C) ℓr
    Extensional-Initial ⦃ sa ⦄ =
      embedding→extensional
        (Iso→Embedding eqv ∙emb (fst , Subset-proj-embedding λ _ → hlevel 1))
        sa
```
-->
