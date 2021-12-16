
```agda
open import 1Lab.Prelude
open import Algebra.Magma

module Algebra.UnitalMagma where
```

<!--
```agda
private variable
  ℓ ℓ₁ : Level
  A : Type ℓ
```
-->

# Unital Magmas

A **unital magma** is a `magma`{.Agda ident=isMagma} equipped with a
_two-sided identity element_, that is, an element $e$ such that
$e \star x = x = x \star e$. For any given $\star$, such an element is exists
as long as it is unique. This makes unitality a property of magmas rather then
additional data, leading to the conclusion that the identity element should
be part of the record `isUnitalMagma` instead of its type signature.

However, since magma homomorphisms do not automatically preserve the
identity element[^1], it is part of the type signature for
`isUnitalMagma`{.Agda}, being considered _structure_ that a magma may be
equipped with.

[^1]: Counterexample: The map $f : (\mathbb{Z}, *) \to (\mathbb{Z}, *)$
which sends everything to zero is a semigroup homomorphism, but does not
preserve the unit of $(\mathbb{Z}, *)$.

```agda
record isUnitalMagma (id : A) (_⋆_ : A → A → A) : Type (level-of A) where
  field
    hasIsMagma : isMagma _⋆_

  open isMagma hasIsMagma public

  field
    idˡ : {x : A} → id ⋆ x ≡ x
    idʳ : {x : A} → x ⋆ id ≡ x

open isUnitalMagma public
```

Since `A` is a set, we do not have to worry about higher coherence conditions
when it comes to `idˡ`{.Agda} or `idʳ`{.Agda} - all paths between the same
endpoints in `A` are equal. This allows us to show that being a unital magma
is a _property_ of the operator and the identity:

```agda
isProp-isUnitalMagma : {e : A} → {_⋆_ : A → A → A} → isProp (isUnitalMagma e _⋆_)
isProp-isUnitalMagma x y i .isUnitalMagma.hasIsMagma = isProp-isMagma
  (x .hasIsMagma) (y .hasIsMagma) i
isProp-isUnitalMagma x y i .isUnitalMagma.idˡ = x .hasIsSet _ _ (x .idˡ) (y .idˡ) i
isProp-isUnitalMagma x y i .isUnitalMagma.idʳ = x .hasIsSet _ _ (x .idʳ) (y .idʳ) i
```

We can also show that two units of a magma are necessarily the same, since the
products of the identities has to be equal to either one:

```agda
identities-equal : (e e' : A) → {_⋆_ : A → A → A} → isUnitalMagma e _⋆_ →
  isUnitalMagma e' _⋆_ → e ≡ e'
identities-equal e e' {_⋆_ = _⋆_} unital unital' =
  e ≡⟨ sym (idʳ unital') ⟩
  e ⋆ e' ≡⟨ idˡ unital ⟩
  e' ∎
```

We also show that the type of two-sided identities of a magma,
meaning the type of elements combined with a proof that they make a given magma unital,
is a proposition. This is because `left-right-identities-equal`{.Agda} shows the elements are equal,
and the witnesses are equal because they are propositions, as can be derived from
`isProp-isUnitalMagma`{.Agda}

```agda
isProp-hasIdentity : {⋆ : A → A → A} → isMagma ⋆
                 → isProp (Σ[ u ∈ A ] (isUnitalMagma u ⋆))
isProp-hasIdentity mgm x y = Σ≡Prop (λ x → isProp-isUnitalMagma)
 (identities-equal (x .fst) (y .fst) (x .snd) (y .snd))
```

* One-sided identities

Dropping either of the paths involved in a unital magma results in a right identity or a left identity.

```agda
isLeftId : (⋆ : A → A → A) → A → Type _
isLeftId _⋆_ l = ∀ y → l ⋆ y ≡ y

isRightId : (⋆ : A → A → A) → A → Type _
isRightId _⋆_ r = ∀ y → y ⋆ r ≡ y
```

Perhaps surprisingly, the theorem above can be weakened: If $l$ is a left identity and
$r$ is a right identity, then $l = r$.

```agda
left-right-identities-equal : {⋆ : A → A → A} (l r : A) → isLeftId ⋆ l → isRightId ⋆ r → l ≡ r
left-right-identities-equal {⋆ = _⋆_} l r lid rid =
  l     ≡⟨ sym (rid _) ⟩
  l ⋆ r ≡⟨ lid _ ⟩
  r     ∎
```

This also allows us to show that a magma with both a left as well as a right identity
has to be unital - the identities are equal, which makes them both be left as well as
right identities.

```agda
left-right-identities-unital : {_⋆_ : A → A → A} (l r : A) → isLeftId _⋆_ l → isRightId _⋆_ r →
  isMagma _⋆_ → isUnitalMagma l _⋆_
left-right-identities-unital l r lid rid isMgm .hasIsMagma = isMgm
left-right-identities-unital l r lid rid isMgm .idˡ = lid _
left-right-identities-unital {_⋆_ = _⋆_} l r lid rid isMgm .idʳ {x = x} =
  subst (λ a → (x ⋆ a) ≡ x) (sym (left-right-identities-equal l r lid rid)) (rid _)
```


