<!--
```agda
open import Cat.Functor.Subcategory
open import Cat.Prelude

open import Order.Semilattice.Join
open import Order.Semilattice.Meet
open import Order.Diagram.Bottom
open import Order.Diagram.Join
open import Order.Diagram.Meet
open import Order.Diagram.Top
open import Order.Base

import Order.Reasoning
```
-->

```agda
module Order.Lattice where
```

# Lattices {defines=lattice}

```agda
record is-lattice {o ℓ} (P : Poset o ℓ) : Type (o ⊔ ℓ) where
  no-eta-equality
  open Order.Reasoning P
  field
    has-meets : ∀ x y → Meet P x y
    has-top : Top P
    has-joins : ∀ x y → Join P x y
    has-bottom : Bottom P

  has-meet-slat : is-meet-semilattice P
  has-meet-slat .is-meet-semilattice.has-meets = has-meets
  has-meet-slat .is-meet-semilattice.has-top = has-top

  has-join-slat : is-join-semilattice P
  has-join-slat .is-join-semilattice.has-joins = has-joins
  has-join-slat .is-join-semilattice.has-bottom = has-bottom

  open is-meet-semilattice has-meet-slat public
  open is-join-semilattice has-join-slat public
```

<!--
```agda
private
  variable
    o ℓ o' ℓ' : Level
    P Q R : Poset o ℓ

is-lattice-is-prop : is-prop (is-lattice P)
is-lattice-is-prop {P = P} = Iso→is-hlevel 1 eqv hlevel! where
  open Order.Diagram.Meet P using (H-Level-Meet)
  open Order.Diagram.Join P using (H-Level-Join)
  open Order.Diagram.Top P using (H-Level-Top)
  open Order.Diagram.Bottom P using (H-Level-Bottom)
  unquoteDecl eqv = declare-record-iso eqv (quote is-lattice)

instance
  H-Level-is-lattice
    : ∀ {n} → H-Level (is-lattice P) (suc n)
  H-Level-is-lattice = prop-instance is-lattice-is-prop
```
-->

## Category of lattices

A **lattice homomorphism** is a function which is, at the same time, a
homomorphism for both of the semilattice monoid structures: A function
sending bottom to bottom, top to top, joins to joins, and meets to
meets. Put more concisely, a function which preserves finite meets and
finite joins.

```agda
record
  is-lattice-hom
    {P : Poset o ℓ} {Q : Poset o' ℓ'}
    (f : Monotone P Q)
    (S : is-lattice P)
    (T : is-lattice Q)
    : Type (o ⊔ ℓ')
  where

  private
    module P = Poset P
    module Q = Order.Reasoning Q
    module S = is-lattice S
    module T = is-lattice T

  field
    top-≤ : T.top Q.≤ f # S.top
    bot-≤ : f # S.bot Q.≤ T.bot
    ∩-≤ : ∀ {x y} → f # x T.∩ f # y Q.≤ f # (x S.∩ y)
    ∪-≤ : ∀ {x y} → f # (x S.∪ y) Q.≤ f # x T.∪ f # y
```

<!--
```agda
is-lattice-hom-is-prop
  : ∀ {f : Monotone P Q} {P-lattice Q-lattice}
  → is-prop (is-lattice-hom f P-lattice Q-lattice)
is-lattice-hom-is-prop = Iso→is-hlevel 1 eqv hlevel!
  where unquoteDecl eqv = declare-record-iso eqv (quote is-lattice-hom)

instance
  H-Level-is-lattice-hom
    : ∀ {f : Monotone P Q} {P-lattice Q-lattice n}
    → H-Level (is-lattice-hom f P-lattice Q-lattice) (suc n)
  H-Level-is-lattice-hom = prop-instance is-lattice-hom-is-prop

open is-lattice-hom
```
-->

```agda
id-lattice-hom
  : ∀ (L : is-lattice P)
  → is-lattice-hom idₘ L L
id-lattice-hom {P = P} L .top-≤ =
  Poset.≤-refl P
id-lattice-hom {P = P} L .bot-≤ =
  Poset.≤-refl P
id-lattice-hom {P = P} L .∩-≤ =
  Poset.≤-refl P
id-lattice-hom {P = P} L .∪-≤ =
  Poset.≤-refl P

∘-lattice-hom
  : ∀ {L J K} {f : Monotone Q R} {g : Monotone P Q}
  → is-lattice-hom f J K
  → is-lattice-hom g L J
  → is-lattice-hom (f ∘ₘ g) L K
∘-lattice-hom {R = R} {f = f} f-pres g-pres .top-≤ =
  R .Poset.≤-trans (f-pres .top-≤) (f .pres-≤ (g-pres .top-≤))
∘-lattice-hom {R = R} {f = f} f-pres g-pres .bot-≤ =
  R .Poset.≤-trans (f .pres-≤ (g-pres .bot-≤)) (f-pres .bot-≤)
∘-lattice-hom {R = R} {f = f} f-pres g-pres .∩-≤ =
  R .Poset.≤-trans (f-pres .∩-≤) (f .pres-≤ (g-pres .∩-≤))
∘-lattice-hom {R = R} {f = f} f-pres g-pres .∪-≤ =
  R .Poset.≤-trans (f .pres-≤ (g-pres .∪-≤)) (f-pres .∪-≤)
```

```agda
Lattices-subcat : ∀ o ℓ → Subcat (Posets o ℓ) _ _
Lattices-subcat o ℓ .Subcat.is-ob = is-lattice
Lattices-subcat o ℓ .Subcat.is-hom = is-lattice-hom
Lattices-subcat o ℓ .Subcat.is-hom-prop = hlevel!
Lattices-subcat o ℓ .Subcat.is-hom-id = id-lattice-hom
Lattices-subcat o ℓ .Subcat.is-hom-∘ = ∘-lattice-hom

Lattices : ∀ o ℓ → Precategory _ _
Lattices o ℓ = Subcategory (Lattices-subcat o ℓ)
```
