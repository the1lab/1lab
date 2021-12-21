
```agda
open import 1Lab.Prelude

open import Algebra.Magma

module Algebra.Magma.Unital where
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
$e \star x = x = x \star e$. For any given $\star$, such an element is
exists as long as it is unique. This makes unitality a property of
magmas rather then additional data, leading to the conclusion that the
identity element should be part of the record `isUnitalMagma` instead
of its type signature.

However, since magma homomorphisms do not automatically preserve the
identity element[^1], it is part of the type signature for
`isUnitalMagma`{.Agda}, being considered _structure_ that a magma may be
equipped with.

[^1]: Counterexample: The map $f : (\mathbb{Z}, *) \to (\mathbb{Z}, *)$
which sends everything to zero is a magma homomorphism, but does not
preserve the unit of $(\mathbb{Z}, *)$.

```agda
record isUnitalMagma (identity : A) (_⋆_ : A → A → A) : Type (level-of A) where
  field
    hasIsMagma : isMagma _⋆_

  open isMagma hasIsMagma public

  field
    idˡ : {x : A} → identity ⋆ x ≡ x
    idʳ : {x : A} → x ⋆ identity ≡ x

open isUnitalMagma public
```

Since `A` is a set, we do not have to worry about higher coherence
conditions when it comes to `idˡ`{.Agda} or `idʳ`{.Agda} - all paths
between the same endpoints in `A` are equal. This allows us to show that
being a unital magma is a _property_ of the operator and the identity:

```agda
isProp-isUnitalMagma : {e : A} → {_⋆_ : A → A → A} → isProp (isUnitalMagma e _⋆_)
isProp-isUnitalMagma x y i .isUnitalMagma.hasIsMagma = isProp-isMagma
  (x .hasIsMagma) (y .hasIsMagma) i
isProp-isUnitalMagma x y i .isUnitalMagma.idˡ = x .hasIsSet _ _ (x .idˡ) (y .idˡ) i
isProp-isUnitalMagma x y i .isUnitalMagma.idʳ = x .hasIsSet _ _ (x .idʳ) (y .idʳ) i
```

We can also show that two units of a magma are necessarily the same,
since the products of the identities has to be equal to either one:

```agda
identities-equal : (e e' : A) → {_⋆_ : A → A → A} → isUnitalMagma e _⋆_
  → isUnitalMagma e' _⋆_ → e ≡ e'
identities-equal e e' {_⋆_ = _⋆_} unital unital' =
  e ≡⟨ sym (idʳ unital') ⟩
  e ⋆ e' ≡⟨ idˡ unital ⟩
  e' ∎
```

We also show that the type of two-sided identities of a magma,
meaning the type of elements combined with a proof that they make a
given magma unital, is a proposition. This is because
`left-right-identities-equal`{.Agda} shows the elements are equal,
and the witnesses are equal because they are propositions, as can
be derived from `isProp-isUnitalMagma`{.Agda}

```agda
isProp-hasIdentity : {⋆ : A → A → A} → isMagma ⋆
                   → isProp (Σ[ u ∈ A ] (isUnitalMagma u ⋆))
isProp-hasIdentity mgm x y = Σ≡Prop (λ x → isProp-isUnitalMagma)
 (identities-equal (x .fst) (y .fst) (x .snd) (y .snd))
```

By turning both operation and identity element into record fields,
we obtain the notion of a **unital magma structure** on a type
that can be further used to define the type of unital magmas,
as well as their underlying magma structures.

```agda
record UnitalMagmaOn (A : Type ℓ) : Type ℓ where
  field
    identity : A
    _⋆_ : A → A → A

    hasIsUnitalMagma : isUnitalMagma identity _⋆_

  hasMagmaOn : MagmaOn A
  hasMagmaOn .MagmaOn._⋆_ = _⋆_
  hasMagmaOn .MagmaOn.hasIsMagma = hasIsUnitalMagma .hasIsMagma

  open isUnitalMagma hasIsUnitalMagma public

UnitalMagma : (ℓ : Level) → Type (lsuc ℓ)
UnitalMagma ℓ = Σ UnitalMagmaOn

UnitalMagma→Magma : {ℓ : _} → UnitalMagma ℓ → Magma ℓ
UnitalMagma→Magma (A , unital-mgm) = A , UnitalMagmaOn.hasMagmaOn unital-mgm
```

This allows us to define **equivalences of unital magmas** - two unital
magmas are equivalent if there is an equivalence of their carrier sets
that preserves both the magma operation (which implies it is a magma
homomorphism) and the identity element.

```
record
  UnitalMagma≃ (A B : UnitalMagma ℓ) (e : A .fst ≃ B .fst) : Type ℓ where
  private
    module A = UnitalMagmaOn (A .snd)
    module B = UnitalMagmaOn (B .snd)

  field
    pres-⋆ : (x y : A .fst) → e .fst (x A.⋆ y) ≡ e .fst x B.⋆ e .fst y
    pres-identity : e .fst A.identity ≡ B.identity
    
  hasMagma≃ : Magma≃ (UnitalMagma→Magma A) (UnitalMagma→Magma B) e
  hasMagma≃ .Magma≃.pres-⋆ = pres-⋆

open UnitalMagma≃
```

Similar to the `process for magmas`{.Agda ident=Magma≡}, we can see that
the identity type between two unital magmas is the same as the type of
their equivalences.

```agda
UnitalMagma-univalent : isUnivalent {ℓ = ℓ} (HomT→Str UnitalMagma≃)
UnitalMagma-univalent {ℓ = ℓ} = autoUnivalentRecord
  (autoRecord (UnitalMagmaOn {ℓ = ℓ}) UnitalMagma≃
  (record:
    field[ UnitalMagmaOn._⋆_ by pres-⋆ ]
    field[ UnitalMagmaOn.identity by pres-identity ]
    axiom[ UnitalMagmaOn.hasIsUnitalMagma by (λ _ → isProp-isUnitalMagma) ]
  ))

UnitalMagma≡ : {A B : UnitalMagma ℓ} → (A ≃[ HomT→Str UnitalMagma≃ ] B) ≃ (A ≡ B)
UnitalMagma≡ = SIP UnitalMagma-univalent 
```

* One-sided identities

Dropping either of the paths involved in a unital magma results in a
right identity or a left identity.

```agda
isLeftId : (⋆ : A → A → A) → A → Type _
isLeftId _⋆_ l = ∀ y → l ⋆ y ≡ y

isRightId : (⋆ : A → A → A) → A → Type _
isRightId _⋆_ r = ∀ y → y ⋆ r ≡ y
```

Perhaps surprisingly, the premises of the above theorem can be weakened:
If $l$ is a left identity and $r$ is a right identity, then $l = r$.

```agda
left-right-identities-equal : {⋆ : A → A → A} (l r : A) → isLeftId ⋆ l → isRightId ⋆ r → l ≡ r
left-right-identities-equal {⋆ = _⋆_} l r lid rid =
  l     ≡⟨ sym (rid _) ⟩
  l ⋆ r ≡⟨ lid _ ⟩
  r     ∎
```

This also allows us to show that a magma with both a left as well as a
right identity has to be unital - the identities are equal, which makes
them both be left as well as right identities.

```agda
left-right-identities-unital
  : {_⋆_ : A → A → A} (l r : A)
  → isLeftId _⋆_ l → isRightId _⋆_ r
  → isMagma _⋆_ → isUnitalMagma l _⋆_
left-right-identities-unital l r lid rid isMgm .hasIsMagma = isMgm
left-right-identities-unital l r lid rid isMgm .idˡ = lid _
left-right-identities-unital {_⋆_ = _⋆_} l r lid rid isMgm .idʳ {x = x} =
  subst (λ a → (x ⋆ a) ≡ x) (sym (left-right-identities-equal l r lid rid)) (rid _)
```
