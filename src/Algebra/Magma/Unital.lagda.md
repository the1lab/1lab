<!--
```agda
open import 1Lab.Prelude

open import Algebra.Magma
```
-->

```agda
module Algebra.Magma.Unital where
```

<!--
```agda
private variable
  ℓ ℓ₁ : Level
  A : Type ℓ
```
-->

# Unital magmas

A **unital magma** is a `magma`{.Agda ident=is-magma} equipped with a
_two-sided identity element_, that is, an element $e$ such that
$e \star x = x = x \star e$. For any given $\star$, such an element is
exists as long as it is unique. This makes unitality a property of
magmas rather then additional data, leading to the conclusion that the
identity element should be part of the record `is-unital-magma` instead
of its type signature.

However, since magma homomorphisms do not automatically preserve the
identity element[^1], it is part of the type signature for
`is-unital-magma`{.Agda}, being considered _structure_ that a magma may be
equipped with.

[^1]: Counterexample: The map $f : (\bb{Z}, *) \to (\bb{Z}, *)$
which sends everything to zero is a magma homomorphism, but does not
preserve the unit of $(\bb{Z}, *)$.

```agda
record is-unital-magma (identity : A) (_⋆_ : A → A → A) : Type (level-of A) where
  field
    has-is-magma : is-magma _⋆_

  open is-magma has-is-magma public

  field
    idl : {x : A} → identity ⋆ x ≡ x
    idr : {x : A} → x ⋆ identity ≡ x

open is-unital-magma public
```

Since `A` is a set, we do not have to worry about higher coherence
conditions when it comes to `idl`{.Agda} or `idr`{.Agda} - all paths
between the same endpoints in `A` are equal. This allows us to show that
being a unital magma is a _property_ of the operator and the identity:

```agda
is-unital-magma-is-prop : {e : A} → {_⋆_ : A → A → A} → is-prop (is-unital-magma e _⋆_)
is-unital-magma-is-prop x y i .is-unital-magma.has-is-magma = is-magma-is-prop
  (x .has-is-magma) (y .has-is-magma) i
is-unital-magma-is-prop x y i .is-unital-magma.idl = x .has-is-set _ _ (x .idl) (y .idl) i
is-unital-magma-is-prop x y i .is-unital-magma.idr = x .has-is-set _ _ (x .idr) (y .idr) i
```

We can also show that two units of a magma are necessarily the same,
since the products of the identities has to be equal to either one:

```agda
identities-equal
  : (e e' : A) {_⋆_ : A → A → A}
  → is-unital-magma e _⋆_
  → is-unital-magma e' _⋆_
  → e ≡ e'
identities-equal e e' {_⋆_ = _⋆_} unital unital' =
  e      ≡⟨ sym (idr unital') ⟩
  e ⋆ e' ≡⟨ idl unital ⟩
  e' ∎
```

We also show that the type of two-sided identities of a magma,
meaning the type of elements combined with a proof that they make a
given magma unital, is a proposition. This is because
`left-right-identities-equal`{.Agda} shows the elements are equal,
and the witnesses are equal because they are propositions, as can
be derived from `is-unital-magma-is-prop`{.Agda}

```agda
has-identity-is-prop
  : {A : Type ℓ} {⋆ : A → A → A}
  → is-magma ⋆ → is-prop (Σ[ u ∈ A ] (is-unital-magma u ⋆))
has-identity-is-prop mgm x y = Σ-prop-path (λ x → is-unital-magma-is-prop)
 (identities-equal (x .fst) (y .fst) (x .snd) (y .snd))
```

By turning both operation and identity element into record fields,
we obtain the notion of a **unital magma structure** on a type
that can be further used to define the type of unital magmas,
as well as their underlying magma structures.

```agda
record Unital-magma-on (A : Type ℓ) : Type ℓ where
  field
    identity : A
    _⋆_ : A → A → A

    has-is-unital-magma : is-unital-magma identity _⋆_

  has-Magma-on : Magma-on A
  has-Magma-on .Magma-on._⋆_ = _⋆_
  has-Magma-on .Magma-on.has-is-magma = has-is-unital-magma .has-is-magma

  open is-unital-magma has-is-unital-magma public

Unital-magma : (ℓ : Level) → Type (lsuc ℓ)
Unital-magma ℓ = Σ (Type ℓ) Unital-magma-on

Unital-magma→Magma : {ℓ : _} → Unital-magma ℓ → Magma ℓ
Unital-magma→Magma (A , unital-mgm) = A , Unital-magma-on.has-Magma-on unital-mgm
```

This allows us to define **equivalences of unital magmas** - two unital
magmas are equivalent if there is an equivalence of their carrier sets
that preserves both the magma operation (which implies it is a magma
homomorphism) and the identity element.

```agda
record
  Unital-magma≃ (A B : Unital-magma ℓ) (e : A .fst ≃ B .fst) : Type ℓ where
  private
    module A = Unital-magma-on (A .snd)
    module B = Unital-magma-on (B .snd)

  field
    pres-⋆ : (x y : A .fst) → e .fst (x A.⋆ y) ≡ e .fst x B.⋆ e .fst y
    pres-identity : e .fst A.identity ≡ B.identity

  has-magma≃ : Magma≃ (Unital-magma→Magma A) (Unital-magma→Magma B) e
  has-magma≃ .Magma≃.pres-⋆ = pres-⋆

open Unital-magma≃
```

## One-sided identities

Dropping either of the paths involved in a unital magma results in a
right identity or a left identity.

```agda
is-left-id : (⋆ : A → A → A) → A → Type _
is-left-id _⋆_ l = ∀ y → l ⋆ y ≡ y

is-right-id : (⋆ : A → A → A) → A → Type _
is-right-id _⋆_ r = ∀ y → y ⋆ r ≡ y
```

Perhaps surprisingly, the premises of the above theorem can be weakened:
If $l$ is a left identity and $r$ is a right identity, then $l = r$.

```agda
left-right-identities-equal
  : {⋆ : A → A → A} (l r : A)
  → is-left-id ⋆ l → is-right-id ⋆ r → l ≡ r
left-right-identities-equal {⋆ = _⋆_} l r lid rid =
  l     ≡⟨ sym (rid _) ⟩
  l ⋆ r ≡⟨ lid _ ⟩
  r     ∎
```

This also allows us to show that a magma with both a left as well as a
right identity has to be unital - the identities are equal, which makes
them both be left as well as right identities.

```agda
left-right-identity→unital
  : {_⋆_ : A → A → A} (l r : A)
  → is-left-id _⋆_ l → is-right-id _⋆_ r
  → is-magma _⋆_ → is-unital-magma l _⋆_
left-right-identity→unital l r lid rid isMgm .has-is-magma = isMgm
left-right-identity→unital l r lid rid isMgm .idl = lid _
left-right-identity→unital {_⋆_ = _⋆_} l r lid rid isMgm .idr {x = x} =
  subst (λ a → (x ⋆ a) ≡ x) (sym (left-right-identities-equal l r lid rid)) (rid _)
```
