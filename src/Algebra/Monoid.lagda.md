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

# Monoids

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

```agda
record isMonoid (id : A) (_⋆_ : A → A → A) : Type (level-of A) where
  field
    hasIsSemigroup : isSemigroup _⋆_

  open isSemigroup hasIsSemigroup public

  field
    idˡ : {x : A} → id ⋆ x ≡ x
    idʳ : {x : A} → x ⋆ id ≡ x

open isMonoid public
```

The condition of $(A, 0, \star)$ defining a monoid is a proposition, so
that we may safely decompose monoids as the _structure_ $(0, \star)$,
which has to satisfy the _property_ of being a monoid.

```agda
isProp-isMonoid : {id : A} {_⋆_ : A → A → A}
                → isProp (isMonoid id _⋆_)
isProp-isMonoid x y i .hasIsSemigroup =
  isProp-isSemigroup (x .hasIsSemigroup) (y .hasIsSemigroup) i
isProp-isMonoid x y i .idˡ = x .hasIsSet _ _ (x .idˡ) (y .idˡ) i
isProp-isMonoid x y i .idʳ = x .hasIsSet _ _ (x .idʳ) (y .idʳ) i
```

A `monoid structure on`{.Agda ident=MonoidOn} a type is given by the
choice of identity element, the choice of binary operation, and the
witness that these choices form a monoid. A `Monoid`{.Agda}, then, is a
`type with`{.Agda ident=Σ} a monoid structure.

```agda
record MonoidOn (A : Type ℓ) : Type ℓ where
  field
    identity : A
    _⋆_ : A → A → A

    hasIsMonoid : isMonoid identity _⋆_

  open isMonoid hasIsMonoid public

Monoid : (ℓ : Level) → Type (lsuc ℓ)
Monoid ℓ = Σ (MonoidOn {ℓ = ℓ})

open MonoidOn
```

There is also a predicate which witnesses when an equivalence between
monoids is a monoid homomorphism. It has to preserve the identity, and
commute with the multiplication:

```agda
record
  MonoidHom (A B : Σ (MonoidOn {ℓ = ℓ})) (e : A .fst → B .fst) : Type ℓ where
  private
    module A = MonoidOn (A .snd)
    module B = MonoidOn (B .snd)

  field
    pres-id : e A.identity ≡ B.identity
    pres-⋆ : (x y : A .fst) → e (x A.⋆ y) ≡ e x B.⋆ e y

open MonoidHom

Monoid≃ : (A B : Σ (MonoidOn {ℓ = ℓ})) (e : A .fst ≃ B .fst) → Type _
Monoid≃ A B (e , _) = MonoidHom A B e
```

We automatically derive a proof that `MonoidOn`{.Agda} is univalent for
the `structure induced`{.Agda ident=HomT→Str} by `Monoid≃`{.Agda}:

```agda
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

```agda
Monoid≡ : {A B : Monoid ℓ} → (A ≃[ HomT→Str Monoid≃ ] B) ≃ (A ≡ B)
Monoid≡ = SIP Monoid-univalent
```

# Relationships to Unital Magmas

```agda
open import Algebra.Magma.Unital
```

By definition, every monoid is exactly a `unital magma`{.Agda ident=isUnitalMagma}
that is also a `semigroup`{.Agda ident=isSemigroup}. However, adopting
this as a definition yields several issues especially when it comes to
metaprogramming, which is why this is instead expressed by explicitly
proving the implications between the properties.

First, we show that every monoid is a unital magma:

```agda
module _ {id : A} {_⋆_ : A → A → A} where
  isMonoid→isUnitalMagma : isMonoid id _⋆_ → isUnitalMagma id _⋆_
  isMonoid→isUnitalMagma mon .hasIsMagma = mon .hasIsSemigroup .hasIsMagma
  isMonoid→isUnitalMagma mon .idˡ = mon .idˡ
  isMonoid→isUnitalMagma mon .idʳ = mon .idʳ
```

"Reshuffling" the record fields also allows us to show the reverse
direction, namely, that every unital semigroup is a monoid.

```agda
  isUnitalMagma→isSemigroup→isMonoid : isUnitalMagma id _⋆_ → isSemigroup _⋆_ →
    isMonoid id _⋆_
  isUnitalMagma→isSemigroup→isMonoid uni sem .hasIsSemigroup = sem
  isUnitalMagma→isSemigroup→isMonoid uni sem .idˡ = uni .idˡ
  isUnitalMagma→isSemigroup→isMonoid uni sem .idʳ = uni .idʳ
```

# Inverses

A useful application of the monoid laws is in showing that _having an
**inverse**_ is a _proprety_ of a specific element, not structure on
that element. To make this precise: Let $e$ be an element of a monoid,
say $(M, 1, \star)$; If there are $x$ and $y$ such that $x \star e = e$
and $e \star y = e$, then $x = y$.

```
monoid-inverse-unique
  : ∀ {1M : A} {_⋆_ : A → A → A}
  → (m : isMonoid 1M _⋆_)
  → (e x y : A)
  → (x ⋆ e ≡ 1M) → (e ⋆ y ≡ 1M)
  → x ≡ y
```

This is a happy theorem where stating the assumptions takes as many
lines as the proof, which is a rather boring calculation. Since $1$ is
an identity for $\star$, we can freely multiply by $1$ to "sneak in" a
$y$:

```
monoid-inverse-unique {1M = 1M} {_⋆_} m e x y li1 ri2 =
  x             ≡⟨ sym (m .idʳ) ⟩
  x ⋆ 1M        ≡⟨ ap₂ _⋆_ refl (sym ri2) ⟩ 
  x ⋆ (e ⋆ y)   ≡⟨ m .associative ⟩
  (x ⋆ e) ⋆ y   ≡⟨ ap₂ _⋆_ li1 refl ⟩ 
  1M ⋆ y        ≡⟨ m .idˡ ⟩
  y             ∎
```