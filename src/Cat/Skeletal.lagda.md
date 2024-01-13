<!--
```agda
open import Cat.Instances.Discrete
open import Cat.Prelude
open import Cat.Strict

import Cat.Reasoning

open Cat.Reasoning using (Isomorphism ; id-iso)
open Precategory using (Ob)
```
-->

```agda
module Cat.Skeletal where
```

# Skeletal precategories

A precategory $\cC$ is **skeletal** if objects having _the property of
being isomorphic_ are identical. The clunky rephrasing is proposital: if
we had merely said "isomorphic objects are identical", then skeletality
sounds too much like [[univalence|univalent categories]], from which it
is distinct. Instead, skeletality is defined as (equivalent to) the
existence of a map

$$
\| a \cong b \| \to a \equiv b\text{,}
$$

which we can more concisely summarise as "$(\| - \cong - \|, \| \id \|)$
is an [[identity system]]".

[identity system]: 1Lab.Path.IdentitySystem.html

```agda
is-skeletal : ∀ {o ℓ} → Precategory o ℓ → Type (o ⊔ ℓ)
is-skeletal C =
  is-identity-system (λ x y → ∥ Isomorphism C x y ∥) (λ x → inc (id-iso C))

path-from-has-iso→is-skeletal
  : ∀ {o ℓ} (C : Precategory o ℓ)
  → (∀ {a b} → ∥ Isomorphism C a b ∥ → a ≡ b)
  → is-skeletal C
path-from-has-iso→is-skeletal C sk = set-identity-system (λ _ _ → squash) sk
```

Skeletality is much rarer than [[univalence|univalent categories]] in
practice, and univalence is the more useful condition, since it allows
facts about isomorphism to transfer to identity^[Indeed, it also allows
general facts about identity to transfer to isomorphism!]. Skeletality,
in our sense, serves as a point of comparison for _other_ properties: if
a property implies skeletality, we can safely regard it as unnatural.

<!--
```agda
module _ {o ℓ} (C : Precategory o ℓ) where
```
-->

One of the reasons skeletality is unnatural is it implies the category
is [strict].

[strict]: Cat.Strict.html

```agda
  skeletal→strict : is-skeletal C → is-strict C
  skeletal→strict skel = identity-system→hlevel 1 skel (λ _ _ → squash)
```

Furthermore, skeletality does *not* imply univalence, as objects in
$\cC$ may have non-trivial automorphisms. The [walking involution] is
the simplest example of a non-univalent, skeletal precategory. In
general, we prefer to work with [gaunt], not skeletal, categories.

[walking involution]: Cat.Instances.Shape.Involution.html
[gaunt]: Cat.Gaunt.html
