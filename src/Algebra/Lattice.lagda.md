```agda
open import 1Lab.Prelude

open import Algebra.Semilattice

open import Cat.Functor.Equivalence
open import Cat.Functor.Base
open import Cat.Prelude
open import Cat.Thin

module Algebra.Lattice where
```

<!--
```agda
private variable
  ℓ : Level
  A : Type ℓ
open Functor
```
-->

# Lattices

A **lattice** $(A, \land, \lor)$ is a pair of semilattices $(A, \land)$
and $(A, \lor)$ which “fit together” with equations specifying that
$\land$ and $\lor$ are duals, called _absorption laws_.

```agda
record is-lattice (_∧_ : A → A → A) (_∨_ : A → A → A) : Type (level-of A) where
  field
    has-meets : is-semilattice _∧_
    has-joins : is-semilattice _∨_
```

<details>
<summary>
We rename the fields of `has-meets`{.Agda} and `has-joins`{.Agda} so they
refer to the operator in their name, and hide anything extra from the
hierarchy.
</summary>

```agda
  open is-semilattice has-meets public
    renaming ( associative to ∧-associative
             ; commutative to ∧-commutative
             ; idempotent to ∧-idempotent
             )
    hiding ( has-is-magma ; has-is-semigroup )

  open is-semilattice has-joins public
    renaming ( associative to ∨-associative
             ; commutative to ∨-commutative
             ; idempotent to ∨-idempotent
             )
    hiding ( underlying-set ; has-is-magma ; has-is-set ; magma-hlevel )
```
</details>

```agda
  field
    ∧-absorbs-∨ : ∀ {x y} → (x ∧ (x ∨ y)) ≡ x
    ∨-absorbs-∧ : ∀ {x y} → (x ∨ (x ∧ y)) ≡ x
```

A **lattice structure** equips a type $A$ with two binary operators,
the meet $\land$ and join $\lor$, such that $(A, \land, \lor)$ is a
lattice. Since being a semilattice includes being a set, this means that
being a lattice is a _property_ of $(A, \land, \lor)$:

```agda
private unquoteDecl eqv = declare-record-iso eqv (quote is-lattice)

instance
  H-Level-is-lattice : ∀ {M J : A → A → A} {n} → H-Level (is-lattice M J) (suc n)
  H-Level-is-lattice = prop-instance λ x →
    let open is-lattice x in is-hlevel≃ 1 (Iso→Equiv eqv e⁻¹) (hlevel 1) x

record Lattice-on (A : Type ℓ) : Type ℓ where
  field
    _L∧_ : A → A → A
    _L∨_ : A → A → A

  infixr 40 _L∧_
  infixr 30 _L∨_

  field
    has-is-lattice : is-lattice _L∧_ _L∨_

  open is-lattice has-is-lattice public

  Lattice-on→is-meet-semi : is-semilattice _L∧_
  Lattice-on→is-meet-semi = has-meets

  Lattice-on→is-join-semi : is-semilattice _L∨_
  Lattice-on→is-join-semi = has-joins

open Lattice-on using (Lattice-on→is-meet-semi ; Lattice-on→is-join-semi) public

Lattice : ∀ ℓ → Type (lsuc ℓ)
Lattice ℓ = Σ (Lattice-on {ℓ = ℓ})
```

Since the absorption laws are property, not structure, a lattice
homomorphism turns out to be a function which is homomorphic for both
semilattice structures, i.e. one that independently preserves meets and
joins.

```agda
record Lattice→ (A B : Lattice ℓ) (f : A .fst → B .fst) : Type ℓ where
  private
    module A = Lattice-on (A .snd)
    module B = Lattice-on (B .snd)

  field
    pres-∧ : ∀ x y → f (x A.L∧ y) ≡ f x B.L∧ f y
    pres-∨ : ∀ x y → f (x A.L∨ y) ≡ f x B.L∨ f y

Lattice≃ : (A B : Lattice ℓ) (f : A .fst ≃ B .fst) → Type ℓ
Lattice≃ A B = Lattice→ A B ∘ fst
```

Using the automated machinery for deriving `is-univalent`{.Agda} proofs,
we get that identification of lattices is the same thing as lattice
isomorphism.

```agda
Lattice-univalent : ∀ {ℓ} → is-univalent (HomT→Str (Lattice≃ {ℓ = ℓ}))
Lattice-univalent {ℓ = ℓ} =
  Derive-univalent-record (record-desc (Lattice-on {ℓ = ℓ}) Lattice≃
    (record:
      field[ Lattice-on._L∧_ by Lattice→.pres-∧ ]
      field[ Lattice-on._L∨_ by Lattice→.pres-∨ ]
      axiom[ Lattice-on.has-is-lattice by (λ _ → hlevel 1) ]))
```

## Order-theoretically

We [already know] that a given semilattice structure can induce one of
two posets, depending on whether the semilattice operator is being
considered as equipping the poset with meets or joins. We'd then expect
that a lattice, having two semi-lattices, would have _four_ poset
structures. However, there are only two, which we call the "covariant"
and "contravariant" orderings.

[already know]: Algebra.Semilattice.html#order-theoretically

```agda
Lattice→covariant-on : Lattice-on A → Poset (level-of A) (level-of A)
Lattice→covariant-on lat = Semilattice-on→Meet-on (Lattice-on→is-meet-semi lat)

Lattice→contravariant-on : Lattice-on A → Poset (level-of A) (level-of A)
Lattice→contravariant-on lat = Semilattice-on→Join-on (Lattice-on→is-meet-semi lat)
```

Above, the “covariant order” is obtaining by considering the $(A,
\land)$ semilattice as inducing _meets_ on the poset (hence the operator
being called $\land$). It can also be obtained in a dual way, by
considering that $(A, \lor)$ induces _joins_ on the poset. By the
absorption laws, these constructions give rise to the same poset; We
start by defining a `monotone map`{.Agda ident=Monotone-map} (that is, a
`Functor`{.Agda}) between the two possibilities:

```agda
covariant-order-map
  : (l : Lattice-on A)
  → Monotone-map
      (Semilattice-on→Meet-on (Lattice-on→is-meet-semi l))
      (Semilattice-on→Join-on (Lattice-on→is-join-semi l))
covariant-order-map {A = A} l = F where
  open Lattice-on l
    hiding (Lattice-on→is-join-semi ; Lattice-on→is-meet-semi)

  F : Monotone-map (Semilattice-on→Meet-on (Lattice-on→is-meet-semi l))
                   (Semilattice-on→Join-on (Lattice-on→is-join-semi l))
  F .F₀ = id
  F .F₁ {x} {y} p = q where abstract
    q : y ≡ x L∨ y
    q =
      y             ≡⟨ sym ∨-absorbs-∧ ⟩
      y L∨ (y L∧ x) ≡⟨ ap₂ _L∨_ refl ∧-commutative ⟩
      y L∨ (x L∧ y) ≡⟨ ap₂ _L∨_ refl (sym p) ⟩
      y L∨ x        ≡⟨ ∨-commutative ⟩
      x L∨ y        ∎
  F .F-id = has-is-set _ _ _ _
  F .F-∘ _ _ = has-is-set _ _ _ _
```

We now show that this functor is an equivalence: It is fully faithful
and split essentially surjective.

```agda
covariant-order-map-is-equivalence
  : (l : Lattice-on A) → is-equivalence (covariant-order-map l)
covariant-order-map-is-equivalence l =
  ff+split-eso→is-equivalence ff eso
  where
    open Lattice-on l hiding (Lattice-on→is-join-semi)
    import
      Cat.Reasoning
        (Semilattice-on→Join-on (Lattice-on→is-join-semi l) .Poset.underlying)
      as D
```

A tiny calculation shows that this functor is fully faithful, and
essential surjectivity is immediate:

```agda
    ff : is-fully-faithful (covariant-order-map l)
    ff {x} {y} .is-eqv p .centre .fst =
      x             ≡⟨ sym ∧-absorbs-∨ ⟩
      x L∧ (x L∨ y) ≡⟨ ap₂ _L∧_ refl (sym p) ⟩
      x L∧ y        ∎
    ff .is-eqv y .centre .snd = has-is-set _ _ _ _
    ff .is-eqv y .paths x =
      Σ-path (has-is-set _ _ _ _)
             (is-prop→is-set (has-is-set _ _) _ _ _ _)

    eso : is-split-eso (covariant-order-map l)
    eso y .fst = y
    eso y .snd =
      D.make-iso (sym ∨-idempotent) (sym ∨-idempotent)
        (has-is-set _ _ _ _)
        (has-is-set _ _ _ _)
```
