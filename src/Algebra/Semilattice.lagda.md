```agda
open import 1Lab.Prelude

open import Algebra.Semigroup

open import Order.Proset hiding (isMonotone)
open import Order.Poset 

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

[partially ordered set]: Order.Poset.html
[meet]: agda://Order.Poset#is-meet
[join]: agda://Order.Poset#is-join
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

Each semilattice structure $(A, \land)$ on $A$ induces two partial
orders on $A$ by setting $x \le y$ when $x = x \land y$ or when $y = x
\land y$. In the former case, we call the semilattice structure a _meet_
semilattice, since the binary operation acts as a meet for $x$ and $y$,
and similarly the dual choice is called a _join_ semilattice. We detail
the construction of a meet semilattice, and leave the construction of a
join semilattice in a `<details>` tag.

```agda
Semilattice-on→MeetOn
  : ∀ {∧ : A → A → A}
  → is-semilattice ∧
  → PosetOn {ℓ' = level-of A} A
Semilattice-on→MeetOn {∧ = _∧_} semi = r where
  open PosetOn
  open is-partial-order
  open is-preorder
  open is-semilattice

  r : PosetOn _
  r ._≤_ = λ x y → x ≡ x ∧ y
```

As mentioned, the order relation is induced by setting $(x \le y)
\leftrightarrow (x ≡ x ∧ y)$. For this to be reflexive, we need that $x
≡ (x ∧ x)$, which is guaranteed by the idempotence axiom:

```agda
  r .has-is-partialOrder .has-is-preorder .reflexive = sym (idempotent semi)
```

The relation is transitive by a use of associativity, as can be seen in
the equational computation below:

```agda
  r .has-is-partialOrder .has-is-preorder .transitive {x} {y} {z} x≡x∧y y≡y∧z =
    x             ≡⟨ x≡x∧y ⟩
    (x ∧ y)       ≡⟨ ap₂ _∧_ refl y≡y∧z ⟩ 
    (x ∧ (y ∧ z)) ≡⟨ associative semi ⟩ 
    ((x ∧ y) ∧ z) ≡⟨ ap₂ _∧_ (sym x≡x∧y) refl ⟩ 
    x ∧ z         ∎
```

The relation is propositional since it is equality in a set --- the type
$A$ is assumed to be a set since $(A, \and)$ must be a semigroup, and
semigroups must be sets.

```agda
  r .has-is-partialOrder .has-is-preorder .propositional = has-is-set semi _ _
```

The relation is antisymmetric by a use of commutativitiy:

```agda
  r .has-is-partialOrder .antisym {x} {y} x≡x∧y y≡y∧x =
    x     ≡⟨ x≡x∧y ⟩
    x ∧ y ≡⟨ commutative semi ⟩ 
    y ∧ x ≡⟨ sym y≡y∧x ⟩
    y     ∎
```

We now prove that, under this relation, $x \and y$ is the `meet`{.Agda
ident=is-meet} of $x$ and $y$. Recall that a meet is the greatest element
$m$ for which $m \le x$ and $m \le y$.

```agda
Semilattice→is-meet : ∀ {_∧_ : A → A → A} (semi : is-semilattice _∧_)
                   → ∀ {x y} → is-meet (A , Semilattice-on→MeetOn semi) (x ∧ y) x y
Semilattice→is-meet {_∧_ = _∧_} semi {x} {y} = r where
  open is-meet
  open is-semilattice

  r : is-meet _ (x ∧ y) x y
```

By a rather tedious calculation (using idempotence to insert an extra
$x$ term, and reassociating), we have that $(x \land y) ≡ (x \land y)
\land x$, so that $(x \land y) \le x$, as required.

```agda
  r .m≤x =
    x ∧ y       ≡⟨ ap₂ _∧_ (sym (idempotent semi)) refl ⟩
    (x ∧ x) ∧ y ≡⟨ sym (associative semi) ⟩
    x ∧ (x ∧ y) ≡⟨ ap₂ _∧_ refl (commutative semi) ⟩
    x ∧ (y ∧ x) ≡⟨ associative semi ⟩
    (x ∧ y) ∧ x ∎
```

A similar calculation shows us that $(x \land y) ≡ (x \land y) \land y$,
as required for $(x \land y) \le y$. This computation is simpler because
of the chosen ordering of the terms - if we had instead gone with $y
\land x$ in the statement of the theorem, this calculation would be
complicated, and the one above would be simple.

```agda
  r .m≤y =
    x ∧ y       ≡⟨ ap₂ _∧_ refl (sym (idempotent semi)) ⟩
    x ∧ (y ∧ y) ≡⟨ associative semi ⟩
    (x ∧ y) ∧ y ∎
```

It remains to show that if $a \le x$ and $a \le y$, then $a \le (x \land
y)$, which is again a calculation:

```agda
  r .limiting a a≡a∧x a≡a∧y =
    a           ≡⟨ a≡a∧y ⟩
    a ∧ y       ≡⟨ ap₂ _∧_ a≡a∧x refl ⟩
    (a ∧ x) ∧ y ≡⟨ sym (associative semi) ⟩
    a ∧ (x ∧ y) ∎
```

<details>
<summary>The construction of a join semilattice is formally dual, and so
we leave it in this details tag in the interest of conciseness.
</summary>

```agda
Semilattice-on→JoinOn
  : ∀ {∨ : A → A → A} → is-semilattice ∨ → PosetOn {ℓ' = level-of A} A
Semilattice-on→JoinOn {∨ = _∨_} semi = r where
  open PosetOn
  open is-partial-order
  open is-preorder
  open is-semilattice

  r : PosetOn _
  r ._≤_ = λ x y → y ≡ x ∨ y
  r .has-is-partialOrder .has-is-preorder .reflexive = sym (idempotent semi)
  r .has-is-partialOrder .has-is-preorder .transitive {x} {y} {z} y=x∨y z=y∨z =
    z           ≡⟨ z=y∨z ⟩
    y ∨ z       ≡⟨ ap₂ _∨_ y=x∨y refl ⟩
    (x ∨ y) ∨ z ≡⟨ sym (associative semi) ⟩
    x ∨ (y ∨ z) ≡⟨ ap₂ _∨_ refl (sym z=y∨z) ⟩
    x ∨ z ∎
  r .has-is-partialOrder .has-is-preorder .propositional = has-is-set semi _ _
  r .has-is-partialOrder .antisym {x} {y} y=x∨y x=y∨x =
    x     ≡⟨ x=y∨x ⟩
    y ∨ x ≡⟨ commutative semi ⟩
    x ∨ y ≡⟨ sym y=x∨y ⟩
    y     ∎
```

We also have that, under this order relation, the semilattice operator
is the _join_ of the operands, as promised.

```agda
Semilattice→is-join : ∀ {_∨_ : A → A → A} (semi : is-semilattice _∨_)
                   → ∀ {x y} → is-join (A , Semilattice-on→JoinOn semi) (x ∨ y) x y
Semilattice→is-join {_∨_ = _∨_} semi {x} {y} = r where
  open is-join
  open is-semilattice

  r : is-join _ (x ∨ y) x y
  r .x≤j =
    x ∨ y       ≡⟨ ap₂ _∨_ (sym (idempotent semi)) refl ⟩
    (x ∨ x) ∨ y ≡⟨ sym (associative semi) ⟩
    x ∨ (x ∨ y) ∎
  r .y≤j =
    x ∨ y       ≡⟨ ap₂ _∨_ refl (sym (idempotent semi)) ⟩
    x ∨ (y ∨ y) ≡⟨ associative semi ⟩
    (x ∨ y) ∨ y ≡⟨ ap₂ _∨_ (commutative semi) refl ⟩
    (y ∨ x) ∨ y ≡⟨ sym (associative semi) ⟩
    y ∨ (x ∨ y) ∎
    
  r .colimiting a a=x∨a a=y∨a =
    a           ≡⟨ a=x∨a ⟩
    x ∨ a       ≡⟨ ap₂ _∨_ refl a=y∨a ⟩
    x ∨ (y ∨ a) ≡⟨ associative semi ⟩
    (x ∨ y) ∨ a ∎
```
</details>

## Maps

As is typical with algebraic structures, we define a semilattice
homomorphism as being a map which commutes with the binary operator.
Since being a semilattice is a _property_ of $(A, \land)$, we have
a characterisation of identifications of semilattices: Two semilattices
are identified precisely when their underlying types are equivalent by
some homomorphic equivalence.

```agda
is-semilattice-is-prop : ∀ {∧ : A → A → A} → is-prop (is-semilattice ∧)
is-semilattice-is-prop x y i = p where
  open is-semilattice

  p : is-semilattice _
  p .has-is-semigroup = is-semigroup-is-prop (x .has-is-semigroup) (y .has-is-semigroup) i
  p .commutative = x .has-is-set _ _ (x .commutative) (y .commutative) i
  p .idempotent = x .has-is-set _ _ (x .idempotent) (y .idempotent) i
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
  →Meet = A , Semilattice-on→MeetOn has-is-semilattice

  -- Considered as a join-semilattice:
  →Join : Poset ℓ ℓ
  →Join = A , Semilattice-on→JoinOn has-is-semilattice

  ∨ : A → A → A
  ∨ = ∧ 

open Semilattice-on using (→Meet ; →Join)

Semilattice : ∀ ℓ → Type (lsuc ℓ)
Semilattice ℓ = Σ (Semilattice-on {ℓ = ℓ})
```

In the names of functions, we'll abbreviate "**S**emi**lat**tice" as
"SLat", which has the three desirable properties of an abbreviation: It
is funny, short and pronounceable.

```agda
record Semilattice→ (A B : Semilattice ℓ) (f : A .fst → B .fst) : Type ℓ where
  private
    module A = Semilattice-on (A .snd)
    module B = Semilattice-on (B .snd)

  field
    pres-∧ : ∀ x y → f (A.∧ x y) ≡ B.∧ (f x) (f y)

  -- Considered as a homomorphism of join semilattices:

  pres-∨ : ∀ x y → f (A.∨ x y) ≡ B.∨ (f x) (f y)
  pres-∨ = pres-∧

Semilattice≃ : (A B : Semilattice ℓ) (f : A .fst ≃ B .fst) → Type ℓ
Semilattice≃ A B = Semilattice→ A B ∘ fst
```

Using the automated machinery for deriving `is-univalent`{.Agda} proofs,
we get the promised characterisation of identifications in the type of
semilattices.

```agda
Semilattice-univalent : ∀ {ℓ} → is-univalent (HomT→Str (Semilattice≃ {ℓ = ℓ}))
Semilattice-univalent {ℓ = ℓ} =
  Derive-univalent-record (record-desc (Semilattice-on {ℓ = ℓ}) (Semilattice≃)
    (record:
      field[ Semilattice-on.∧ by Semilattice→.pres-∧ ]
      axiom[ Semilattice-on.has-is-semilattice by (λ _ → is-semilattice-is-prop) ]))
```

Any semilattice homomorphism is `monotone`{.Agda ident=isMonotone} when
considered as a map between the posets induced by a semilattice,
regardless of whether we consider it as a meet or as a join semilattice.

```agda
module _
  {A B : Semilattice ℓ} (f : A .fst → B .fst) (ishom : Semilattice→ A B f)
  where
    private
      module A = Semilattice-on (A .snd)
      module B = Semilattice-on (B .snd)

    open Semilattice→ ishom

    isSLatHom→isMonotoneMeet : isMonotone (→Meet (A .snd)) (→Meet (B .snd)) f
    isSLatHom→isMonotoneMeet x y x=x∧y =
      f x             ≡⟨ ap f x=x∧y ⟩
      f (A.∧ x y)     ≡⟨ pres-∧ _ _ ⟩
      B.∧ (f x) (f y) ∎

    isSLatHom→isMonotoneJoin : isMonotone (→Join (A .snd)) (→Join (B .snd)) f
    isSLatHom→isMonotoneJoin x y y=x∨y =
      f y             ≡⟨ ap f y=x∨y ⟩
      f (A.∨ x y)     ≡⟨ pres-∨ _ _ ⟩
      B.∨ (f x) (f y) ∎
```
