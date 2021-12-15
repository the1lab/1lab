```agda
open import 1Lab.Prelude

open import Algebra.Semigroup

module Algebra.Monoid where
```

<!--
```agda
private variable
  ℓ ℓ₁ : Level
  A : Type ℓ
```
-->

A **monoid** is a semigroup equipped with a _two-sided identity_
element: An element $e \in M$ such that $e \star x = x = x \star e$. For
any particular choice of binary operator $\star$, if a two-sided
identity exists, then it is unique; In this sense, "being a monoid"
could be considered an "axiom" that semigroups may satisfy.

However, since semigroup homomorphisms do not automatically preserve the
identity element[^1], it is part of the type signature for
`isMonoid`{.Agda}, being considered _structure_ that a semigroup may be
equipped with.

[^1]: Counterexample: The map $f : (\mathbb{Z}, *) \to (\mathbb{Z}, *)$
which sends everything to zero is a semigroup homomorphism, but does not
preserve the unit of $(\mathbb{Z}, *)$.

```
record isMonoid (id : A) (_⋆_ : A → A → A) : Type (level-of A) where
  field
    monoid-semigroup : isSemigroup _⋆_

  open isSemigroup monoid-semigroup public

  field
    idˡ : {x : A} → id ⋆ x ≡ x
    idʳ : {x : A} → x ⋆ id ≡ x

open isMonoid
```

The condition of $(A, id, \star)$ defining a monoid is a proposition, so
that we may safely decompose monoids as the _structure_ $(id, \star)
satisfying the _property_ of being a monoid.

```
isProp-isMonoid : {id : A} {_⋆_ : A → A → A}
                → isProp (isMonoid id _⋆_)
isProp-isMonoid x y i .monoid-semigroup =
  isProp-isSemigroup (x .monoid-semigroup) (y .monoid-semigroup) i
isProp-isMonoid x y i .idˡ = x .hasIsSet _ _ (x .idˡ) (y .idˡ) i
isProp-isMonoid x y i .idʳ = x .hasIsSet _ _ (x .idʳ) (y .idʳ) i
```

A `monoid structure on`{.Agda} a type is given by the choice of identity
element, the choice of binary operation, and the witness that these
choices form a monoid. A `Monoid`{.Agda}, then, is a `type with`{.Agda
ident=Σ} a monoid structure.

```
record MonoidOn (A : Type ℓ) : Type ℓ where
  field
    identity : A
    _⋆_ : A → A → A

    hasIsMonoid : isMonoid identity _⋆_

Monoid : (ℓ : Level) → Type (lsuc ℓ)
Monoid ℓ = Σ (MonoidOn {ℓ = ℓ})

open MonoidOn
```

There is also a predicate which witnesses when an equivalence between
monoids is a monoid homomorphism. It has to preserve the identity, and
commute with the multiplication:

```
record
  Monoid≃ (A B : Σ (MonoidOn {ℓ = ℓ})) (e : A .fst ≃ B .fst) : Type ℓ where
  private
    module A = MonoidOn (A .snd)
    module B = MonoidOn (B .snd)

  field
    pres-id : e .fst A.identity ≡ B.identity
    pres-⋆ : (x y : A .fst) → e .fst (x A.⋆ y) ≡ e .fst x B.⋆ e .fst y

open Monoid≃
```

We automatically derive a proof that `MonoidOn`{.Agda} is univalent for
the `structure induced`{.Agda HomT→Str} by `Monoid≃`{.Agda}:

```
Monoid-univalent : isUnivalent {ℓ = ℓ} (HomT→Str Monoid≃)
Monoid-univalent {ℓ = ℓ} =
  autoUnivalentRecord (autoRecord
    (MonoidOn {ℓ = ℓ}) Monoid≃
    (record:
      field[ identity    by pres-id ]
      field[ _⋆_         by pres-⋆ ]
      axiom[ hasIsMonoid by (λ _ → isProp-isMonoid) ]))
```

From this, we automatically get a specialisation of the `SIP`{.Agda} for
`Monoid`{.Agda}s, which says that _equality of monoids is monoid
isomorphism_.

```
Monoid≡ : {A B : Monoid ℓ} → (A ≃[ HomT→Str Monoid≃ ] B) ≃ (A ≡ B)
Monoid≡ = SIP Monoid-univalent
```