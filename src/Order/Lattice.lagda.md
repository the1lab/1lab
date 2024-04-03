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

import Cat.Reasoning

import Order.Diagram.Join.Reasoning as Joins
import Order.Diagram.Meet.Reasoning as Meets
import Order.Reasoning
```
-->

```agda
module Order.Lattice where
```

# Lattices {defines=lattice}

A **lattice** is a [[poset]] which is simultaneously a [[meet semilattice]]
and a [[join semilattice]].

```agda
record is-lattice {o ℓ} (P : Poset o ℓ) : Type (o ⊔ ℓ) where
  no-eta-equality

  field
    _∩_     : ⌞ P ⌟ → ⌞ P ⌟ → ⌞ P ⌟
    ∩-meets : ∀ x y → is-meet P x y (x ∩ y)

    _∪_     : ⌞ P ⌟ → ⌞ P ⌟ → ⌞ P ⌟
    ∪-joins : ∀ x y → is-join P x y (x ∪ y)

    has-top : Top P
    has-bottom : Bottom P

  infixr 24 _∪_
  infixr 25 _∩_

  open Joins {P = P} ∪-joins public
  open Meets {P = P} ∩-meets public

  has-meet-slat : is-meet-semilattice P
  has-meet-slat .is-meet-semilattice._∩_     = _∩_
  has-meet-slat .is-meet-semilattice.∩-meets = ∩-meets
  has-meet-slat .is-meet-semilattice.has-top = has-top

  has-join-slat : is-join-semilattice P
  has-join-slat .is-join-semilattice._∪_ = _∪_
  has-join-slat .is-join-semilattice.∪-joins = ∪-joins
  has-join-slat .is-join-semilattice.has-bottom = has-bottom

  open Top has-top using (top ; !) public
  open Bottom has-bottom using (bot ; ¡) public
```

<!--
```agda
private
  variable
    o ℓ o' ℓ' : Level
    P Q R : Poset o ℓ

is-lattice-is-prop : is-prop (is-lattice P)
is-lattice-is-prop {P = P} p q = path where
  open Order.Diagram.Top P using (H-Level-Top)
  open Order.Diagram.Bottom P using (H-Level-Bottom)

  module p = is-lattice p
  module q = is-lattice q
  open is-lattice

  joinp : ∀ x y → x p.∪ y ≡ x q.∪ y
  joinp x y = join-unique (p.∪-joins x y) (q.∪-joins x y)

  meetp : ∀ x y → x p.∩ y ≡ x q.∩ y
  meetp x y = meet-unique (p.∩-meets x y) (q.∩-meets x y)

  path : p ≡ q
  path i ._∪_ x y = joinp x y i
  path i ._∩_ x y = meetp x y i
  path i .∪-joins x y = is-prop→pathp
    (λ i → hlevel {T = is-join P x y (joinp x y i)} 1)
    (p.∪-joins x y) (q.∪-joins x y) i
  path i .∩-meets x y = is-prop→pathp
    (λ i → hlevel {T = is-meet P x y (meetp x y i)} 1)
    (p.∩-meets x y) (q.∩-meets x y) i
  path i .has-top    = hlevel {T = Top P} 1 p.has-top q.has-top i
  path i .has-bottom = hlevel {T = Bottom P} 1 p.has-bottom q.has-bottom i

instance
  H-Level-is-lattice
    : ∀ {n} → H-Level (is-lattice P) (suc n)
  H-Level-is-lattice = prop-instance is-lattice-is-prop
```
-->

## Category of lattices

A **lattice homomorphism** is a function which is, at the same time, a
homomorphism for both of the semilattice structures: A function
sending bottom to bottom, top to top, joins to joins, and meets to
meets. Put more concisely, a function which preserves finite meets and
finite joins.

```agda
record
  is-lattice-hom
    {P : Poset o ℓ} {Q : Poset o' ℓ'}
    (f : Monotone P Q) (S : is-lattice P) (T : is-lattice Q) : Type (o ⊔ ℓ')
  where
```

<!--
```agda
  private
    module P = Poset P
    module Q = Order.Reasoning Q
    module S = is-lattice S
    module T = is-lattice T
```
-->

```agda
  field
    top-≤ : T.top Q.≤ f # S.top
    bot-≤ : f # S.bot Q.≤ T.bot
    ∩-≤ : ∀ {x y} → f # x T.∩ f # y Q.≤ f # (x S.∩ y)
    ∪-≤ : ∀ {x y} → f # (x S.∪ y) Q.≤ f # x T.∪ f # y
```

<!--
```agda
unquoteDecl H-Level-is-lattice-hom = declare-record-hlevel 1 H-Level-is-lattice-hom (quote is-lattice-hom)
open is-lattice-hom
```
-->

The identity function is clearly a lattice homomorphism, and lattice
homomorphisms are closed under composition.

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

This allows us to carve out the category of lattices as a [[subcategory]]
of the category of posets.

```agda
Lattices-subcat : ∀ o ℓ → Subcat (Posets o ℓ) _ _
Lattices-subcat o ℓ .Subcat.is-ob = is-lattice
Lattices-subcat o ℓ .Subcat.is-hom = is-lattice-hom
Lattices-subcat o ℓ .Subcat.is-hom-prop _ _ _ = hlevel 1
Lattices-subcat o ℓ .Subcat.is-hom-id = id-lattice-hom
Lattices-subcat o ℓ .Subcat.is-hom-∘ = ∘-lattice-hom

Lattices : ∀ o ℓ → Precategory _ _
Lattices o ℓ = Subcategory (Lattices-subcat o ℓ)

module Lattices {o} {ℓ} = Cat.Reasoning (Lattices o ℓ)

Lattice : ∀ o ℓ → Type _
Lattice o ℓ = Lattices.Ob {o} {ℓ}
```
