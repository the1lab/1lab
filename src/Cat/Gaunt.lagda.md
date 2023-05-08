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

# Gaunt (pre)categories

A precategory $\cC$ is **gaunt** if it is [univalent] and [strict]: its
type of objects $\rm{Ob}(\cC)$ is a set, and identity in $\rm{Ob}$ is
equivalent to isomorphism in $\cC$. This is a truncation condition on
the isomorphisms $a \cong b : \cC$, which must all be trivial.

[univalent]: Cat.Univalent.html
[strict]: Cat.Strict.html

```agda
record is-gaunt {o ℓ} (C : Precategory o ℓ) : Type (o ⊔ ℓ) where
  field
    has-category : is-category C
    has-strict : is-strict C

  open Univalent.path→iso has-category hiding (hlevel) public
  open StrictIds has-category has-strict renaming (K to K-iso) public
```

<!--
```agda
unquoteDecl eqv = declare-record-iso eqv (quote is-gaunt)

is-gaunt-is-prop
  : ∀ {o ℓ} {C : Precategory o ℓ}
  → is-prop (is-gaunt C)
is-gaunt-is-prop =
  Iso→is-hlevel 1 eqv (Σ-is-hlevel 1 hlevel! (λ _ → is-hlevel-is-prop 2))

instance
  H-Level-is-gaunt
    : ∀ {o ℓ} {C : Precategory o ℓ} {n}
    → H-Level (is-gaunt C) (suc n)
  H-Level-is-gaunt = prop-instance is-gaunt-is-prop
```
-->

As one would expect, being gaunt is property of a category.

```agda
module _ {o ℓ} {C : Precategory o ℓ} (gaunt : is-gaunt C) where
  open is-gaunt gaunt
  open Cat.Reasoning C

  iso-is-prop : ∀ {x y} → is-prop (x ≅ y)
  iso-is-prop = hlevel!
```

This implies that gaunt categories are [skeletal]: Since there is at
most one isomorphism $a \cong b$, then given $\| a \cong b \|$, we can
apply _unique choice_ to retrieve the underlying map.

[skeletal]: Cat.Skeletal.html

```agda
  gaunt→skeletal : is-skeletal C
  gaunt→skeletal = set-identity-system (λ _ _ → squash) $
    ∥-∥-rec (has-strict _ _) (has-category .to-path)
```

Furthermore, if a category is skeletal and univalent, it is gaunt.

```agda
skeletal-category→is-gaunt
  : ∀ {o ℓ} {C : Precategory o ℓ}
  → is-skeletal C
  → is-category C
  → is-gaunt C
skeletal-category→is-gaunt skel cat .is-gaunt.has-category = cat
skeletal-category→is-gaunt skel cat .is-gaunt.has-strict = skeletal→strict _ skel
```

This implies that gaunt categories are **precisely** the skeletal
univalent categories.

```agda
skeletal-category≃gaunt
  : ∀ {o ℓ} {C : Precategory o ℓ}
  → (is-skeletal C × is-category C) ≃ is-gaunt C
skeletal-category≃gaunt = prop-ext (hlevel 1) (hlevel 1)
    (λ { (skel , cat) → skeletal-category→is-gaunt skel cat })
    (λ gaunt → gaunt→skeletal gaunt , has-category gaunt)
  where open is-gaunt
```
