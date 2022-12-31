```agda
open import Cat.Prelude

open import Order.Diagram.Lub
open import Order.Semilattice
open import Order.Base

import Order.Reasoning as Pr

module Order.Lattice where
```

# Lattices

A **lattice** is a [poset] which is a [semilattice] in two compatible,
dual ways. We have a "meet" semilattice $(A, \cap, \top)$, and a "join"
semilattice $(A, \cup, \bot)$ --- and we take the order on $A$ induced
by, for definiteness, the $\cap$ semilattice. The question is then: how
do we write, algebraically, a condition on $\cap$ and $\cup$ which
guarantees that $\cup$ provides $(A, \le)$ with *joins*?

[poset]: Order.Base.html
[semilattice]: Order.Semilattice.html

<!--
```agda
record
  is-lattice
    {ℓ} {A : Type ℓ}
    (⊤ : A) (_∩_ : A → A → A)
    (⊥ : A) (_∪_ : A → A → A)
  : Type ℓ
  where

  no-eta-equality
```
-->

The answer is yes! Of course, since if it were not, this page would not
be being written. A **lattice** structure on $(A, \top, \bot, \cap,
\cup)$ is a pair of semilattices $(A, \cap, \top)$ and $(A, \cup,
\bot)$, such that the $\cap$ and $\cup$ operations satisfy the two
absorption laws with respect to eachother:

```agda
  field
    has-meets : is-semilattice ⊤ _∩_
    has-joins : is-semilattice ⊥ _∪_

    ∩-absorbs-∪ : ∀ {x y} → x ∩ (x ∪ y) ≡ x
    ∪-absorbs-∩ : ∀ {x y} → x ∪ (x ∩ y) ≡ x
```

<!--
```agda
  open is-semilattice has-meets public
    renaming ( associative to ∩-associative
             ; commutative to ∩-commutative
             ; idempotent  to ∩-idempotent
             ; idl         to ∩-idl
             ; idr         to ∩-idr
             )
    hiding ( has-is-magma ; has-is-semigroup )

  open is-semilattice has-joins public
    renaming ( associative to ∪-associative
             ; commutative to ∪-commutative
             ; idempotent  to ∪-idempotent
             ; idl         to ∪-idl
             ; idr         to ∪-idr
             )
    hiding ( underlying-set ; has-is-magma ; has-is-set ; magma-hlevel )

private unquoteDecl eqv = declare-record-iso eqv (quote is-lattice)

instance
  H-Level-is-lattice
    : ∀ {ℓ} {A : Type ℓ} {top bot : A} {meet join : A → A → A} {n}
    → H-Level (is-lattice top meet bot join) (suc n)
  H-Level-is-lattice = prop-instance λ x →
    let open is-lattice x in Iso→is-hlevel 1 eqv (hlevel 1) x
```
-->

As usual, a lattice structure on a set is a record packaging together
the operations and a proof that they are actually an instance of the
algebraic structure we're talking about.

```agda
record Lattice-on {ℓ} (A : Type ℓ) : Type ℓ where
  no-eta-equality
  field
    top : A
    bot : A
    _∩_ : A → A → A
    _∪_ : A → A → A
    has-is-lattice : is-lattice top _∩_ bot _∪_

  open is-lattice has-is-lattice public
```

<!--
```agda
module _ {ℓ} (L : Σ (Set ℓ) λ A → Lattice-on ∣ A ∣) where
  open Lattice-on (L .snd)

  Lattice→poset : Poset ℓ ℓ
  Lattice→poset =
    Meet-semi-lattice .Functor.F₀
      (L .fst , record { has-is-semilattice = has-meets })

  private module P = Pr Lattice→poset
```
-->

The question then becomes: what is the point of the absorption laws?
I'll tell you! Since we have two semilattice structures on the set, we
can imagine defining two orders on it: one is given by $x \le y$ iff $x
= x \cap y$, and the other is given by $y = x \cup y$. As an exercise,
try to work out that these are the same thing in the lattice of subsets
of a fixed $A$.

Really, there are four orderings we could imagine defining on a
semilattice: $x \le y$ iff. $x = x \cap y$, $y = x \cap y$, $x = x \cup
y$, and $y = x \cup y$. The absorption laws serve to cut these
possibilities in half, because using them we can show that $x = x \cap
y$ is the same as $y = x \cup y$ (and, respectively, $y = x \cap y$ is
the same as $x = x \cup y$).

```agda
  ∪-order→∩-order : ∀ {x y} → y ≡ x ∪ y → x ≡ x ∩ y
  ∪-order→∩-order {x} {y} y=x∪y =
    x             ≡˘⟨ ∩-absorbs-∪ ⟩
    x ∩ ⌜ x ∪ y ⌝ ≡˘⟨ ap¡ y=x∪y ⟩
    x ∩ y         ∎

  ∩-order→∪-order : ∀ {x y} → x ≡ x ∩ y → y ≡ x ∪ y
  ∩-order→∪-order {x} {y} p =
    y             ≡⟨ sym ∪-absorbs-∩ ⟩
    y ∪ ⌜ y ∩ x ⌝ ≡⟨ ap! ∩-commutative ⟩
    y ∪ ⌜ x ∩ y ⌝ ≡˘⟨ ap¡ p ⟩
    y ∪ x         ≡⟨ ∪-commutative ⟩
    x ∪ y         ∎
```

Using the "cup ordering", we can establish that cups provide a join of
two elements. Since the cup ordering and the "cap ordering" agree, we
can prove that cups give a join in that case, too!

```agda
  ∪-is-join : ∀ {x y} → is-join Lattice→poset x y (x ∪ y)
  ∪-is-join .is-join.l≤join = sym ∩-absorbs-∪
  ∪-is-join {x} {y} .is-join.r≤join =
    y             ≡˘⟨ ∩-absorbs-∪ ⟩
    y ∩ ⌜ y ∪ x ⌝ ≡⟨ ap! ∪-commutative ⟩
    y ∩ (x ∪ y)   ∎
  ∪-is-join {x} {y} .is-join.least ub′ x=x∩ub′ y=y∩ub′ = ∪-order→∩-order $ sym $
    (x ∪ y) ∪ ub′   ≡˘⟨ ∪-associative ⟩
    x ∪ ⌜ y ∪ ub′ ⌝ ≡˘⟨ ap¡ (∩-order→∪-order y=y∩ub′) ⟩
    x ∪ ub′         ≡˘⟨ ∩-order→∪-order x=x∩ub′ ⟩
    ub′             ∎

  ⊥-is-bottom : ∀ {x} → bot P.≤ x
  ⊥-is-bottom = ∪-order→∩-order (sym ∪-idl)
```

## Category of lattices

A **lattice homomorphism** is a function which is, at the same time, a
homomorphism for both of the semilattice monoid structures: A function
sending bottom to bottom, top to top, joins to joins, and meets to
meets. Put more concisely, a function which preserves finite meets and
finite joins.

```agda
record
  is-lattice-hom
    {ℓ ℓ′} {A : Type ℓ} {B : Type ℓ′}
    (f : A → B)
    (S : Lattice-on A) (T : Lattice-on B)
    : Type (ℓ ⊔ ℓ′)
  where

  private
    module S = Lattice-on S
    module T = Lattice-on T

  field
    pres-⊤ : f S.top ≡ T.top
    pres-⊥ : f S.bot ≡ T.bot
    pres-∩ : ∀ {x y} → f (x S.∩ y) ≡ f x T.∩ f y
    pres-∪ : ∀ {x y} → f (x S.∪ y) ≡ f x T.∪ f y
```
