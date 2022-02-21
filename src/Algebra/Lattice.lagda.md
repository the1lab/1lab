```agda
open import 1Lab.Prelude

open import Algebra.Semilattice

open import Order.Proset
open import Order.Poset

module Algebra.Lattice where
```

<!--
```agda
private variable
  ℓ : Level
  A : Type ℓ
```
-->

# Lattices

A **lattice** $(A, \land, \lor)$ is a pair of semilattices $(A, \land)$
and $(A, \lor)$ which “fit together” with equations specifying that
$\land$ and $\lor$ are duals, called _absorption laws_.

```agda
record is-lattice (_∧_ : A → A → A) (_∨_ : A → A → A) : Type (level-of A) where
  field
    hasMeets : is-semilattice _∧_
    hasJoins : is-semilattice _∨_
```
  
<details>
<summary>
We rename the fields of `hasMeets`{.Agda} and `hasJoins`{.Agda} so they
refer to the operator in their name, and hide anything extra from the
hierarchy.
</summary>

```agda
  open is-semilattice hasMeets public
    renaming ( associative to ∧-associative
             ; commutative to ∧-commutative
             ; idempotent to ∧-idempotent
             )
    hiding ( has-is-magma ; has-is-semigroup )

  open is-semilattice hasJoins public
    renaming ( associative to ∨-associative
             ; commutative to ∨-commutative
             ; idempotent to ∨-idempotent )
    hiding ( underlying-set ; has-is-magma ; has-is-set )
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
is-lattice-is-prop : ∀ {_∧_ _∨_ : A → A → A} → is-prop (is-lattice _∧_ _∨_)
is-lattice-is-prop x y i = p where
  open is-lattice

  p : is-lattice _ _
  p .hasMeets = is-semilattice-is-prop (x .hasMeets) (y .hasMeets) i
  p .hasJoins = is-semilattice-is-prop (x .hasJoins) (y .hasJoins) i
  p .∧-absorbs-∨ = has-is-set x _ _ (x .∧-absorbs-∨) (y .∧-absorbs-∨) i
  p .∨-absorbs-∧ = has-is-set x _ _ (x .∨-absorbs-∧) (y .∨-absorbs-∧) i

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
  Lattice-on→is-meet-semi = hasMeets

  Lattice-on→is-join-semi : is-semilattice _L∨_
  Lattice-on→is-join-semi = hasJoins

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
      axiom[ Lattice-on.has-is-lattice by (λ _ → is-lattice-is-prop) ]))
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
Lattice→Covariant-on : Lattice-on A → PosetOn {ℓ' = level-of A} A
Lattice→Covariant-on lat = Semilattice-on→MeetOn (Lattice-on→is-meet-semi lat)

Lattice→Contravariant-on : Lattice-on A → PosetOn {ℓ' = level-of A} A
Lattice→Contravariant-on lat = Semilattice-on→JoinOn (Lattice-on→is-meet-semi lat)
```

Above, the “covariant order” is obtaining by considering the $(A,
\land)$ semilattice as inducing _meets_ on the poset (hence the operator
being called $\land$). It can also be obtained in a dual way, by
considering that $(A, \lor)$ induces _joins_ on the poset. By the
absorption laws, these constructions give rise to the same poset; Even
better, the path is induced by the identity function.

```agda
covariant-order-unique 
  : (l : Lattice-on A)
  → Path (Poset ℓ ℓ)
  (A , Semilattice-on→MeetOn (Lattice-on→is-meet-semi l))
  (A , Semilattice-on→JoinOn (Lattice-on→is-join-semi l))
covariant-order-unique {A = A} l = sip Poset-univalent ((id , id-equiv) , pres) where
  open Lattice-on l
```

To show that the identity equivalence is a homomorphic equivalent of
posets, it suffices to show that $x \le y$ in one order implies $y
\le\prime x$ in the other. We show these by calculations:

```agda
  l1 : ∀ {x y : A} → (x ≡ x L∧ y) → (y ≡ x L∨ y)
  l1 {x} {y} p =
    y             ≡⟨ sym ∨-absorbs-∧ ⟩
    y L∨ (y L∧ x) ≡⟨ ap₂ _L∨_ refl ∧-commutative ⟩
    y L∨ (x L∧ y) ≡⟨ ap₂ _L∨_ refl (sym p) ⟩
    y L∨ x        ≡⟨ ∨-commutative ⟩
    x L∨ y        ∎

  l2 : ∀ {x y : A} → (y ≡ x L∨ y) → (x ≡ x L∧ y)
  l2 {x} {y} p =
    x             ≡⟨ sym ∧-absorbs-∨ ⟩
    x L∧ (x L∨ y) ≡⟨ ap₂ _L∧_ refl (sym p) ⟩ 
    x L∧ y        ∎

  pres : Poset≃ _ _ (id , id-equiv)
  pres .Poset≃.pres-≤ x y = ua (prop-ext (has-is-set _ _) (has-is-set _ _) l1 l2)
```
}
The dual fact holds for the “contravariant order”, where the semilattice
$(A, \land)$ is taken to induce _joins_ instead of meets on the
poset.

<details>
<summary>
Since the proof is obtained by swapping $\land$ and $\lor$ in the proof
above, I've put it in a `<details>` tag, in the interest of conciseness.
</summary>

```agda
contravariant-order-unique
  : (l : Lattice-on A)
  → Path (Poset ℓ ℓ)
      (A , Semilattice-on→JoinOn (Lattice-on→is-meet-semi l))
      (A , Semilattice-on→MeetOn (Lattice-on→is-join-semi l))
contravariant-order-unique {A = A} l = 
  sip Poset-univalent ((id , id-equiv) , pres) 
  where
    open Lattice-on l

    l1 : ∀ {x y : A} → (y ≡ x L∧ y) → (x ≡ x L∨ y)
    l1 {x} {y} p =
      x             ≡⟨ sym ∨-absorbs-∧ ⟩
      x L∨ (x L∧ y) ≡⟨ ap₂ _L∨_ refl (sym p) ⟩
      x L∨ y        ∎

    l2 : ∀ {x y : A} → (x ≡ x L∨ y) → (y ≡ x L∧ y)
    l2 {x} {y} p =
      y             ≡⟨ sym ∧-absorbs-∨ ⟩
      y L∧ (y L∨ x) ≡⟨ ap₂ _L∧_ refl ∨-commutative ⟩
      y L∧ (x L∨ y) ≡⟨ ap₂ _L∧_ refl (sym p) ⟩
      y L∧ x        ≡⟨ ∧-commutative ⟩
      x L∧ y        ∎

    pres : Poset≃ _ _ (id , id-equiv)
    pres .Poset≃.pres-≤ x y = ua (prop-ext (has-is-set _ _) (has-is-set _ _) l1 l2)
```
</details>
