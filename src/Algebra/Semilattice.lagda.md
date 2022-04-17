```agda
open import 1Lab.Prelude

open import Algebra.Semigroup

open import Cat.Diagram.Coproduct
open import Cat.Diagram.Product
open import Cat.Prelude
open import Cat.Thin

module Algebra.Semilattice where
```

<!--
```agda
private variable
  ℓ : Level
  A : Type ℓ
```
-->

# Semilattices

A **semilattice** is a [partially ordered set] where all elements have a
[meet] (a **meet semilattice**), or a [join] (a **join semilattice**).
Rather than use a definition in terms of ordered sets, we choose an
_algebraic_ definition of semilattices: A semilattice $(A, \land)$ is a
commutative [semigroup] where every element is _idempotent_: $x \land x = x$.

[partially ordered set]: Cat.Thin.html
[meet]: Cat.Diagram.Limit.Base.html
[join]: Cat.Diagram.Colimit.Base.html
[semigroup]: Algebra.Semigroup.html

```agda
record is-semilattice (_∧_ : A → A → A) : Type (level-of A) where
  field
    has-is-semigroup : is-semigroup _∧_
    commutative    : ∀ {x y} → x ∧ y ≡ y ∧ x
    idempotent     : ∀ {x} → x ∧ x ≡ x

  open is-semigroup has-is-semigroup public
```

## Order-theoretically

Each semilattice structure $(A, \land)$ on $A$ induces two [partial
orders] on $A$ by setting $x \le y$ when $x = x \land y$ or when $y = x
\land y$. In the former case, we call the semilattice structure a **meet
semilattice**, since the binary operation acts as a meet of $x$ and $y$,
and similarly the dual choice is called a **join semilattice**. We
detail the construction of a meet semilattice, and leave the
construction of a join semilattice in a `<details>` tag.

[partial orders]: Cat.Thin.html

```agda
Semilattice-on→Meet-on
  : ∀ {∧ : A → A → A}
  → is-semilattice ∧
  → Poset (level-of A) (level-of A)
Semilattice-on→Meet-on {A = A} {∧ = _∧_} semi = r where
  open Poset
  open is-semilattice

  rel : A → A → _
  rel x y = (x ≡ x ∧ y)
```

As mentioned, the order relation is defined by setting $(x \le y)
\leftrightarrow (x ≡ x ∧ y)$. For this to be reflexive, we need that $x
≡ (x ∧ x)$, which is guaranteed by the idempotence axiom:

```agda
  rel-refl : ∀ {x} → rel x x
  rel-refl = sym (idempotent semi)
```

The relation is transitive by a use of associativity, as can be seen in
the equational computation below:

```agda
  rel-transitive : ∀ {x y z} → rel x y → rel y z → rel x z
  rel-transitive {x} {y} {z} x≡x∧y y≡y∧z =
    x             ≡⟨ x≡x∧y ⟩
    (x ∧ y)       ≡⟨ ap₂ _∧_ refl y≡y∧z ⟩
    (x ∧ (y ∧ z)) ≡⟨ associative semi ⟩
    ((x ∧ y) ∧ z) ≡⟨ ap₂ _∧_ (sym x≡x∧y) refl ⟩
    x ∧ z         ∎
```

The relation is propositional since it is equality in a set --- the type
$A$ is assumed to be a set since $(A, \land)$ must be a semigroup, and
semigroups must be sets.

```agda
  rel-prop : ∀ {x y} → is-prop (rel x y)
  rel-prop = has-is-set semi _ _
```

The relation is antisymmetric by a use of commutativitiy:

```agda
  rel-antisym : ∀ {x y} → rel x y → rel y x → x ≡ y
  rel-antisym {x} {y} x≡x∧y y≡y∧x =
    x     ≡⟨ x≡x∧y ⟩
    x ∧ y ≡⟨ commutative semi ⟩
    y ∧ x ≡⟨ sym y≡y∧x ⟩
    y     ∎
```

This data defines a poset:

```agda
  r = make-poset {R = rel} rel-refl rel-transitive rel-antisym rel-prop
```

We now prove that, under this relation, $x \land y$ is the
`product`{.Agda ident=is-product} of $x$ and $y$. Since the product of
two objects $x$, $y$ in a thin category is the largest object which is
still smaller than $x$ and $y$, we refer to it as a _meet_, to keep with
the order-theoretic naming. First, we must show that $x \land y$ admits
"maps into" (i.e., is lesser than or equal to) $x$ and $y$.

```agda
module _ {_∧_ : A → A → A} (semi : is-semilattice _∧_) where
  private Po = Semilattice-on→Meet-on semi
  open Poset Po
  open is-semilattice semi

  ∧-less-thanl : ∀ {x y} → (x ∧ y) ≤ x
  ∧-less-thanl {x} {y} = sym (
    (x ∧ y) ∧ x ≡⟨ commutative ⟩
    x ∧ (x ∧ y) ≡⟨ associative semi ⟩
    (x ∧ x) ∧ y ≡⟨ ap (_∧ _) idempotent ⟩
    x ∧ y       ∎)

  ∧-less-thanr : ∀ {x y} → (x ∧ y) ≤ y
  ∧-less-thanr {x} {y} =
    x ∧ y       ≡˘⟨ ap (_ ∧_) idempotent ⟩
    x ∧ (y ∧ y) ≡⟨ associative semi ⟩
    (x ∧ y) ∧ y ∎
```

We can now prove that this [cone] is universal. Since the less-than
relation in a poset `is a proposition`{.Agda ident=Hom-is-prop}, the
only thing that must be shown is that if $q \le x$ and $q \le y$, then
$q \le (x \land y)$.

[cone]: Cat.Diagram.Limit.Base.html#Cone

```agda
  Semilattice→is-product
    : ∀ {x y} → is-product underlying {P = x ∧ y} ∧-less-thanl ∧-less-thanr
  Semilattice→is-product {x} {y} = r where
    open is-product

    r : is-product _ _ _
    r .π₁∘factor = Hom-is-prop _ _ _ _
    r .π₂∘factor = Hom-is-prop _ _ _ _
    r .unique _ _ _ = Hom-is-prop _ _ _ _
```

Fortunately, a neat little calculation is all we need:

```agda
    r .⟨_,_⟩ {Q} q=q∧x q=q∧y =
      Q           ≡⟨ q=q∧y ⟩
      Q ∧ y       ≡⟨ ap (_∧ _) q=q∧x ⟩
      (Q ∧ x) ∧ y ≡˘⟨ associative semi ⟩
      Q ∧ (x ∧ y) ∎
```

<details>
<summary>The construction of a join semilattice is formally dual, and so
we leave it in this details tag in the interest of conciseness.
</summary>

```agda
Semilattice-on→Join-on
  : ∀ {∨ : A → A → A} → is-semilattice ∨ → Poset (level-of A) (level-of A)
Semilattice-on→Join-on {∨ = _∨_} semi = r where
  open is-semilattice

  transitive : ∀ {x y z} → y ≡ x ∨ y → z ≡ y ∨ z → _
  transitive {x} {y} {z} y=x∨y z=y∨z =
    z           ≡⟨ z=y∨z ⟩
    y ∨ z       ≡⟨ ap₂ _∨_ y=x∨y refl ⟩
    (x ∨ y) ∨ z ≡⟨ sym (associative semi) ⟩
    x ∨ (y ∨ z) ≡⟨ ap₂ _∨_ refl (sym z=y∨z) ⟩
    x ∨ z ∎

  antisym : ∀ {x y} → _ → _ → _
  antisym {x} {y} y=x∨y x=y∨x =
     x     ≡⟨ x=y∨x ⟩
     y ∨ x ≡⟨ commutative semi ⟩
     x ∨ y ≡⟨ sym y=x∨y ⟩
     y     ∎

  r : Poset _ _
  r = make-poset
    {R = λ x y → y ≡ (x ∨ y)}
    (sym (idempotent semi)) transitive antisym (has-is-set semi _ _)
```

We also have that, under this order relation, the semilattice operator
gives the coproduct (join) of the operands, as promised.

-- ```agda
module _ {_∨_ : A → A → A} (semi : is-semilattice _∨_) where
  private Po = Semilattice-on→Join-on semi
  open Poset Po
  open is-semilattice semi

  ∨-greater-thanl : ∀ {x y} → x ≤ (x ∨ y)
  ∨-greater-thanl {x} {y} =
    x ∨ y       ≡˘⟨ ap (_∨ _) idempotent ⟩
    (x ∨ x) ∨ y ≡˘⟨ associative semi ⟩
    x ∨ (x ∨ y) ∎

  ∨-greater-thanr : ∀ {x y} → y ≤ (x ∨ y)
  ∨-greater-thanr {x} {y} =
    x ∨ y       ≡˘⟨ ap (_ ∨_) idempotent ⟩
    x ∨ (y ∨ y) ≡⟨ associative semi ⟩
    (x ∨ y) ∨ y ≡˘⟨ ap (_∨ _) commutative ⟩
    (y ∨ x) ∨ y ≡˘⟨ associative semi ⟩
    y ∨ (x ∨ y) ∎

  Semilattice→is-coproduct
    : ∀ {x y} → is-coproduct underlying {P = x ∨ y} ∨-greater-thanl ∨-greater-thanr
  Semilattice→is-coproduct {x} {y} = c where
    open is-coproduct
    c : is-coproduct _ _ _
    c .[_,_] {Q} q=x∨q q=y∨q =
      Q           ≡⟨ q=x∨q ⟩
      x ∨ Q       ≡⟨ ap (_ ∨_) q=y∨q ⟩
      x ∨ (y ∨ Q) ≡⟨ associative semi ⟩
      (x ∨ y) ∨ Q ∎
    c .in₀∘factor = Hom-is-prop _ _ _ _
    c .in₁∘factor = Hom-is-prop _ _ _ _
    c .unique _ _ _ = Hom-is-prop _ _ _ _
```
</details>

## Maps

As is typical with algebraic structures, we define a semilattice
homomorphism as being a map which commutes with the binary operator.
Since being a semilattice is a _property_ of $(A, \land)$, we have a
characterisation of identifications of semilattices: Two semilattices
are identified precisely when their underlying types are equivalent by
some homomorphic equivalence.

```agda
private unquoteDecl eqv = declare-record-iso eqv (quote is-semilattice)

instance
  H-Level-is-semilattice : ∀ {M : A → A → A} {n} → H-Level (is-semilattice M) (suc n)
  H-Level-is-semilattice = prop-instance λ x →
    let open is-semilattice x in is-hlevel≃ 1 (Iso→Equiv eqv e⁻¹) (hlevel 1) x
```

A **semilattice structure** on a type $A$ equips the type with an
operator $\land$ and the proof that this operator has the properties of
a semilattice.

```agda
record Semilattice-on {ℓ} (A : Type ℓ) : Type ℓ where
  field
    ∧ : A → A → A
    has-is-semilattice : is-semilattice ∧

  open is-semilattice has-is-semilattice public

  -- Considered as a meet-semilattice:
  →Meet : Poset ℓ ℓ
  →Meet = Semilattice-on→Meet-on has-is-semilattice

  -- Considered as a join-semilattice:
  →Join : Poset ℓ ℓ
  →Join = Semilattice-on→Join-on has-is-semilattice

  ∨ : A → A → A
  ∨ = ∧

open Semilattice-on using (→Meet ; →Join)

Semilattice : ∀ ℓ → Type (lsuc ℓ)
Semilattice ℓ = Σ (Semilattice-on {ℓ = ℓ})
```

The property `is-semilattice-hom`{.Agda} follows the trend of naming the
operator $\land$; However, it also exports a renaming of the
preservation datum `pres-∧`{.Agda} which refers to the operator as
$\lor$.

```agda
record is-semilattice-hom (A B : Semilattice ℓ) (f : A .fst → B .fst) : Type ℓ where
  private
    module A = Semilattice-on (A .snd)
    module B = Semilattice-on (B .snd)

  field
    pres-∧ : ∀ x y → f (A.∧ x y) ≡ B.∧ (f x) (f y)

  -- Considered as a homomorphism of join semilattices:

  pres-∨ : ∀ x y → f (A.∨ x y) ≡ B.∨ (f x) (f y)
  pres-∨ = pres-∧

Semilattice≃ : (A B : Semilattice ℓ) (f : A .fst ≃ B .fst) → Type ℓ
Semilattice≃ A B = is-semilattice-hom A B ∘ fst
```

Using the automated machinery for deriving `is-univalent`{.Agda} proofs,
we get the promised characterisation of identifications in the type of
semilattices.

```agda
Semilattice-univalent : ∀ {ℓ} → is-univalent (HomT→Str (Semilattice≃ {ℓ = ℓ}))
Semilattice-univalent {ℓ = ℓ} =
  Derive-univalent-record (record-desc (Semilattice-on {ℓ = ℓ}) Semilattice≃
    (record:
      field[ Semilattice-on.∧ by is-semilattice-hom.pres-∧ ]
      axiom[ Semilattice-on.has-is-semilattice by (λ _ → hlevel 1) ]))
```

Any semilattice homomorphism is `monotone`{.Agda ident=is-monotone} when
considered as a map between the posets induced by a semilattice,
regardless of whether we consider it as a meet or as a join semilattice.

```agda
module _
  {A B : Semilattice ℓ} (f : A .fst → B .fst) (ishom : is-semilattice-hom A B f)
  where
    private
      module A = Semilattice-on (A .snd)
      module B = Semilattice-on (B .snd)

    open is-semilattice-hom ishom

    is-semilattice-hom→is-monotone-meet
      : Monotone-map A.→Meet B.→Meet
    is-semilattice-hom→is-monotone-meet =
      make-monotone-map A.→Meet B.→Meet f λ x y x=x∧y →
        f x             ≡⟨ ap f x=x∧y ⟩
        f (A.∧ x y)     ≡⟨ pres-∧ _ _ ⟩
        B.∧ (f x) (f y) ∎

    is-semilattice-hom→is-monotone-join
      : Monotone-map A.→Join B.→Join
    is-semilattice-hom→is-monotone-join =
      make-monotone-map A.→Join B.→Join f λ x y y=x∨y →
        f y             ≡⟨ ap f y=x∨y ⟩
        f (A.∨ x y)     ≡⟨ pres-∨ _ _ ⟩
        B.∨ (f x) (f y) ∎
```
