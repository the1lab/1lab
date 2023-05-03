<!--
```agda
open import 1Lab.Path.IdentitySystem.Strict

open import Cat.Strict
open import Cat.Skeletal
open import Cat.Univalent
open import Cat.Prelude

import Cat.Reasoning
```
-->

```agda
module Cat.Gaunt where
```

# Gaunt Categories

A precategory $\cC$ is **gaunt** if the only isomorphism are the identity
morphisms. Another way of saying this is that the precategory is both
[univalent] and [strict].

[univalent]: Cat.Univalent.html
[strict]: Cat.Strict.html

```agda
record is-gaunt {o ℓ} (C : Precategory o ℓ) : Type (o ⊔ ℓ) where
  field
    has-category : is-category C
    has-strict : is-strict C

  open Univalent.path→iso has-category public
  open StrictIds has-category has-strict renaming (K to K-iso) public
```

As one would expect, being gaunt is property of a category.

```agda
is-gaunt-is-prop
  : ∀ {o ℓ} {C : Precategory o ℓ}
  → is-prop (is-gaunt C)
is-gaunt-is-prop p q = worker where
  open is-gaunt

  worker : p ≡ q
  worker i .has-category =
    is-identity-system-is-prop (p .has-category) (q .has-category) i
  worker i .has-strict = is-hlevel-is-prop 2 (p .has-strict) (q .has-strict) i
```

If $\cC$ is gaunt, then the type of isomorphisms is a proposition.
This follows from some general facts about [strict identity systems].

[strict identity systems]: 1Lab.Path.IdentitySystem.Strict.html

```agda
module _ {o ℓ} {C : Precategory o ℓ} (gaunt : is-gaunt C) where
  open is-gaunt gaunt
  open Cat.Reasoning C

  iso-is-prop : ∀ {x y} → is-prop (x ≅ y)
  iso-is-prop = hlevel!
```

This implies that gaunt categories are [skeletal], as we can untruncate
isomorphisms.

[skeletal]: Cat.Skeletal.html

```agda
  gaunt→skeletal : is-skeletal C
  gaunt→skeletal .to-path = ∥-∥-rec (has-strict _ _) iso→path
  gaunt→skeletal .to-path-over ∥f∥ = is-prop→pathp (λ _ → squash) (inc id-iso) ∥f∥
```

Furthermore, if a category is skeletal and univalent, it is gaunt.

```agda
skeletal+univalent→gaunt
  : ∀ {o ℓ} {C : Precategory o ℓ}
  → is-skeletal C
  → is-category C
  → is-gaunt C
skeletal+univalent→gaunt skel cat .is-gaunt.has-category = cat
skeletal+univalent→gaunt skel cat .is-gaunt.has-strict = skeletal→strict _ skel
```

This implies that gaunt categories are **precisely** the skeletal
univalent categories.

```agda
skeletal+univalent≃gaunt
  : ∀ {o ℓ} {C : Precategory o ℓ}
  → (is-skeletal C × is-category C) ≃ is-gaunt C
skeletal+univalent≃gaunt =
  prop-ext
    (×-is-hlevel 1 is-identity-system-is-prop is-identity-system-is-prop)
    is-gaunt-is-prop
    (λ { (skel , cat) → skeletal+univalent→gaunt skel cat })
    (λ gaunt → (gaunt→skeletal gaunt) , has-category gaunt)
  where open is-gaunt
```
