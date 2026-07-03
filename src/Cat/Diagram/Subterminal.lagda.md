<!--
```agda
open import Cat.Diagram.Terminal
open import Cat.Diagram.Product
open import Cat.Prelude

import Cat.Reasoning

open Product
```
-->

```agda
module Cat.Diagram.Subterminal where
```

# Subterminal objects {defines="subterminal-object subterminal"}

<!--
```agda
module _ {o ℓ} (C : Precategory o ℓ) where
  open Cat.Reasoning C
```
-->

An object $P$ of a category $\cC$ is **subterminal** if there is at most
one map from every other object into $P$: that is, if the set
$\hom(X, P)$ is a [[proposition]] for all $X$.

```agda
  is-subterminal : Ob → Type _
  is-subterminal P = ∀ X → is-prop (Hom X P)
```

This is weaker than being a [[terminal object]] $\top$, whose defining
property is that the $\hom$-sets into $\top$ are *contractible*.
In particular, every terminal object is subterminal.

```agda
  terminal→subterminal : ∀ {T} → is-terminal C T → is-subterminal T
  terminal→subterminal term X = is-terminal.!-unique₂ term
```

Subterminal objects can be thought of as the interpretations of *truth
values*, or propositions, in the internal logic of $\cC$. To make this a
bit more precise, note that, in a category with a [[terminal object]] $\top$,
an object $P$ is subterminal if and only if the unique map $P \to \top$
is [[monic]] (hence if $P$ is a [[subobject]] of $\top$).
In other words, if $\cC$ has a [[subobject classifier]] $\Omega$, then
subterminal objects are classified by maps $\top \to \Omega$.

```agda
  module _ (top : Terminal C) where
    open Terminal top

    is-sub-terminal : Ob → Type _
    is-sub-terminal P = is-monic (! {x = P})

    subterminal≃sub-terminal : ∀ P → is-subterminal P ≃ is-sub-terminal P
    subterminal≃sub-terminal P = prop-ext!
      (λ h f g _ → h _ f g)
      (λ h X x y → h x y (!-unique₂ _ _))
```

Subterminal objects also have various equivalent characterisations in
terms of [[products]]. To start with, $P$ is subterminal if and only if
the following diagram is a [[product]] diagram:

~~~{.quiver}
\[\begin{tikzcd}
  P & P & P
  \arrow["{\mathrm{id}}"', from=1-2, to=1-1]
  \arrow["{\mathrm{id}}", from=1-2, to=1-3]
\end{tikzcd}\]
~~~

```agda
  is-subterminal₁ : Ob → Type _
  is-subterminal₁ P = is-product C (id {x = P}) (id {x = P})
```

Furthermore, $P$ is subterminal if and only if there is *some* product
$P \times P$ such that the two projections $P \times P \to P$ are equal,
or equivalently such that the diagonal map $P \to P \times P$ is
[[invertible]].
Intuitively, these conditions all say that $P$ "squares to itself
^[Another way to say this is that, in a [[cartesian monoidal category]],
an object $P$ is subterminal if and only if the unique comonoid structure
on it is idempotent, but this borders on the ridiculous.]", which is
something we expect of propositions.

```agda
  is-subterminal₂ : Ob → Type _
  is-subterminal₂ P = ∃[ p ∈ Product C P P ] p .π₁ ≡ p .π₂

  is-subterminal₃ : Ob → Type _
  is-subterminal₃ P = ∃[ p ∈ Product C P P ] is-invertible (p .⟨_,_⟩ id id)
```

<details>
<summary>Proving these equivalences is a succession of elementary
exercises, so we leave them hidden in this `<details>` tag.</summary>

```agda
  module _ (P : Ob) where
    is-subterminal₀→₁ : is-subterminal P → is-subterminal₁ P
    is-subterminal₀→₁ h .is-product.⟨_,_⟩ f g = f
    is-subterminal₀→₁ h .is-product.π₁∘⟨⟩ = idl _
    is-subterminal₀→₁ h .is-product.π₂∘⟨⟩ = idl _ ∙ h _ _ _
    is-subterminal₀→₁ h .is-product.unique a b = sym (idl _) ∙ a

    is-subterminal₁→₀ : is-subterminal₁ P → is-subterminal P
    is-subterminal₁→₀ h X f g = sym (h .is-product.π₁∘⟨⟩) ∙ h .is-product.π₂∘⟨⟩

    is-subterminal₁→₂ : is-subterminal₁ P → is-subterminal₂ P
    is-subterminal₁→₂ h = inc (p , refl)
      where
        p : Product C P P
        p .apex = P
        p .π₁ = id
        p .π₂ = id
        p .has-is-product = h

    is-subterminal₂→₀ : is-subterminal₂ P → is-subterminal P
    is-subterminal₂→₀ = rec! λ p h X f g →
      sym (p .π₁∘⟨⟩) ∙∙ h ⟩∘⟨refl ∙∙ p .π₂∘⟨⟩

    is-subterminal₁→₃ : is-subterminal₁ P → is-subterminal₃ P
    is-subterminal₁→₃ h = inc (p , subst is-invertible eq id-invertible)
      where
        p : Product C P P
        p .apex = P
        p .π₁ = id
        p .π₂ = id
        p .has-is-product = h

        eq : id ≡ h .is-product.⟨_,_⟩ id id
        eq = h .is-product.unique (idl _) (idl _)

    is-subterminal₃→₁ : is-subterminal₃ P → is-subterminal₁ P
    is-subterminal₃→₁ = rec! λ p h →
      is-product-iso-apex h (p .π₁∘⟨⟩) (p .π₂∘⟨⟩) (p .has-is-product)
```
</details>
