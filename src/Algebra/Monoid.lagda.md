<!--
```agda
open import 1Lab.Prelude

open import Algebra.Semigroup
```
-->

```agda
module Algebra.Monoid where
```

<!--
```agda
private variable
  ℓ ℓ₁ : Level
  A : Type ℓ
```
-->

# Monoids {defines="monoid"}

A **monoid** is a semigroup equipped with a _two-sided identity_
element: An element $e \in M$ such that $e \star x = x = x \star e$. For
any particular choice of binary operator $\star$, if a two-sided
identity exists, then it is unique; In this sense, "being a monoid"
could be considered an "axiom" that semigroups may satisfy.

However, since semigroup homomorphisms do not automatically preserve the
identity element[^1], it is part of the type signature for
`is-monoid`{.Agda}, being considered _structure_ that a semigroup may be
equipped with.

[^1]: Counterexample: The map $f : (\bb{Z}, *) \to (\bb{Z}, *)$
which sends everything to zero is a semigroup homomorphism, but does not
preserve the unit of $(\bb{Z}, *)$.

```agda
record is-monoid (id : A) (_⋆_ : A → A → A) : Type (level-of A) where
  field
    has-is-semigroup : is-semigroup _⋆_

  open is-semigroup has-is-semigroup public

  field
    idl : {x : A} → id ⋆ x ≡ x
    idr : {x : A} → x ⋆ id ≡ x

open is-monoid public
```

The condition of $(A, 0, \star)$ defining a monoid is a proposition, so
that we may safely decompose monoids as the _structure_ $(0, \star)$,
which has to satisfy the _property_ of being a monoid.

```agda
private unquoteDecl eqv = declare-record-iso eqv (quote is-monoid)

instance
  H-Level-is-monoid : ∀ {id : A} {_⋆_ : A → A → A} {n}
                    → H-Level (is-monoid id _⋆_) (suc n)
  H-Level-is-monoid = prop-instance λ x →
    let open is-monoid x in Iso→is-hlevel 1 eqv (hlevel 1) x
```

A `monoid structure on`{.Agda ident=Monoid-on} a type is given by the
choice of identity element, the choice of binary operation, and the
witness that these choices form a monoid. A `Monoid`{.Agda}, then, is a
`type with`{.Agda ident=Σ} a monoid structure.

```agda
record Monoid-on (A : Type ℓ) : Type ℓ where
  field
    identity : A
    _⋆_ : A → A → A

    has-is-monoid : is-monoid identity _⋆_

  open is-monoid has-is-monoid public

Monoid : (ℓ : Level) → Type (lsuc ℓ)
Monoid ℓ = Σ (Type ℓ) Monoid-on

open Monoid-on
```

There is also a predicate which witnesses when an equivalence between
monoids is a monoid homomorphism. It has to preserve the identity, and
commute with the multiplication:

```agda
record
  Monoid-hom {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
             (s : Monoid-on A) (t : Monoid-on B)
             (e : A → B)
           : Type (ℓ ⊔ ℓ') where
  private
    module A = Monoid-on s
    module B = Monoid-on t

  field
    pres-id : e A.identity ≡ B.identity
    pres-⋆ : (x y : A) → e (x A.⋆ y) ≡ e x B.⋆ e y

open Monoid-hom

Monoid≃ : (A B : Monoid ℓ) (e : A .fst ≃ B .fst) → Type _
Monoid≃ A B (e , _) = Monoid-hom (A .snd) (B .snd) e
```

# Relationships to unital magmas

```agda
open import Algebra.Magma.Unital
```

By definition, every monoid is exactly a `unital magma`{.Agda ident=is-unital-magma}
that is also a `semigroup`{.Agda ident=is-semigroup}. However, adopting
this as a definition yields several issues especially when it comes to
metaprogramming, which is why this is instead expressed by explicitly
proving the implications between the properties.

First, we show that every monoid is a unital magma:

```agda
module _ {id : A} {_⋆_ : A → A → A} where
  is-monoid→is-unital-magma : is-monoid id _⋆_ → is-unital-magma id _⋆_
  is-monoid→is-unital-magma mon .has-is-magma = mon .has-is-semigroup .has-is-magma
  is-monoid→is-unital-magma mon .idl = mon .idl
  is-monoid→is-unital-magma mon .idr = mon .idr
```

"Reshuffling" the record fields also allows us to show the reverse
direction, namely, that every unital semigroup is a monoid.

```agda
  is-unital-magma→is-semigroup→is-monoid
    : is-unital-magma id _⋆_ → is-semigroup _⋆_ → is-monoid id _⋆_
  is-unital-magma→is-semigroup→is-monoid uni sem .has-is-semigroup = sem
  is-unital-magma→is-semigroup→is-monoid uni sem .idl = uni .idl
  is-unital-magma→is-semigroup→is-monoid uni sem .idr = uni .idr
```

# Inverses

A useful application of the monoid laws is in showing that _having an
**inverse**_ is a _property_ of a specific element, not structure on
that element. To make this precise: Let $e$ be an element of a monoid,
say $(M, 1, \star)$; If there are $x$ and $y$ such that $x \star e = 1$
and $e \star y = 1$, then $x = y$.

```agda
monoid-inverse-unique
  : ∀ {1M : A} {_⋆_ : A → A → A}
  → (m : is-monoid 1M _⋆_)
  → (e x y : A)
  → (x ⋆ e ≡ 1M) → (e ⋆ y ≡ 1M)
  → x ≡ y
```

This is a happy theorem where stating the assumptions takes as many
lines as the proof, which is a rather boring calculation. Since $1$ is
an identity for $\star$, we can freely multiply by $1$ to "sneak in" a
$y$:

```agda
monoid-inverse-unique {1M = 1M} {_⋆_} m e x y li1 ri2 =
  x             ≡⟨ sym (m .idr) ⟩
  x ⋆ ⌜ 1M ⌝    ≡˘⟨ ap¡ ri2 ⟩
  x ⋆ (e ⋆ y)   ≡⟨ m .associative ⟩
  ⌜ x ⋆ e ⌝ ⋆ y ≡⟨ ap! li1 ⟩
  1M ⋆ y        ≡⟨ m .idl ⟩
  y             ∎
```
