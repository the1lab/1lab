<!--
```agda
open import 1Lab.Path.IdentitySystem.Strict

open import Cat.Skeletal
open import Cat.Prelude
open import Cat.Strict

import Cat.Reasoning

open Cat.Reasoning using (Isomorphism; id-iso)
```
-->

```agda
module Cat.Gaunt where
```

# Gaunt (pre)categories

A precategory $\cC$ is **gaunt** if it is [[univalent|univalent
category]] and [strict]: its type of objects $\rm{Ob}(\cC)$ is a set,
and identity in $\rm{Ob}$ is equivalent to isomorphism in $\cC$. This is
a truncation condition on the isomorphisms $a \cong b : \cC$, which must
all be trivial.

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
private unquoteDecl eqv = declare-record-iso eqv (quote is-gaunt)

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
  iso-is-prop = hlevel 1
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
skeletal+category→gaunt
  : ∀ {o ℓ} {C : Precategory o ℓ}
  → is-skeletal C
  → is-category C
  → is-gaunt C
skeletal+category→gaunt skel cat .is-gaunt.has-category = cat
skeletal+category→gaunt skel cat .is-gaunt.has-strict = skeletal→strict _ skel
```

This implies that gaunt categories are **precisely** the skeletal
univalent categories.

```agda
skeletal-category≃gaunt
  : ∀ {o ℓ} {C : Precategory o ℓ}
  → (is-skeletal C × is-category C) ≃ is-gaunt C
skeletal-category≃gaunt = prop-ext (hlevel 1) (hlevel 1)
    (λ { (skel , cat) → skeletal+category→gaunt skel cat })
    (λ gaunt → gaunt→skeletal gaunt , has-category gaunt)
  where open is-gaunt
```

If a category is skeletal and has only trivial automorphisms, then it
is gaunt.

```agda
skeletal+trivial-automorphisms→gaunt
  : ∀ {o ℓ} {C : Precategory o ℓ}
  → is-skeletal C
  → (∀ {x} → (f : Isomorphism C x x) → f ≡ id-iso C)
  → is-gaunt C
```

To show that $\cC$ is gaunt, it suffices to show that isomorphisms of
$\cC$ are equivalent to paths. $\cC$ is skeletal, so it is straightforward
to construct an inverse to `path→iso`{.Agda} by applying `to-path`{.Agda}
to the truncation of an isomorphism. Showing that this is a right inverse
is straightforward, as $\cC$ is strict.


```agda
skeletal+trivial-automorphisms→gaunt {C = C} skel trivial-aut =
  skeletal+category→gaunt skel $
    equiv-path→identity-system
      (Iso→Equiv path-iso)
      (λ _ → transport-refl _)
  where
    open is-gaunt

    path-iso : ∀ {x y} → Iso (Isomorphism C x y) (x ≡ y)
    path-iso .fst f = skel .to-path (inc f)
    path-iso .snd .is-iso.inv f = path→iso f
    path-iso .snd .is-iso.rinv _ =
      skeletal→strict C skel _ _ _ _
```

To see that this is a left inverse, we can use the fact that truncated
isomorphisms form an [[identity system]] to contract the iso down into an
automorphism. However, all automorphisms are trivial, which allows us to
finish off the proof.

```agda
    path-iso {x = x} .snd .is-iso.linv f =
      IdsJ skel
        (λ y' ∥f∥ → ∀ (f : Isomorphism C x y') → path→iso (skel .to-path ∥f∥) ≡ f)
        (λ f → trivial-aut _ ∙ sym (trivial-aut _))
        (inc f) f
```
