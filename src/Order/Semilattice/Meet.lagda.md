<!--
```agda
open import Cat.Functor.Subcategory
open import Cat.Prelude

open import Data.Fin.Base hiding (_≤_)

open import Order.Diagram.Meet
open import Order.Diagram.Glb
open import Order.Diagram.Top
open import Order.Base

import Cat.Reasoning

import Order.Diagram.Meet.Reasoning as Meets
import Order.Reasoning
```
-->

```agda
module Order.Semilattice.Meet where
```

# Meet semilattices {defines=meet-semilattice}

A **meet semilattice** is a [[partially ordered set]] which has all
finite [[meets]]. This means, in particular, that it has a [[top
element]], since that is the meet of the empty family. Note that, even
though meet-semilattices are presented as _being equipped with_ a binary
operation $a \cap b$, this is not actual *structure* on the
partially-ordered set: meets are uniquely determined, so "being a
meet-semilattice" is always a [[proposition]].

```agda
record is-meet-semilattice {o ℓ} (P : Poset o ℓ) : Type (o ⊔ ℓ) where
  field
    _∩_     : ⌞ P ⌟ → ⌞ P ⌟ → ⌞ P ⌟
    ∩-meets : ∀ x y → is-meet P x y (x ∩ y)
    has-top : Top P

  infixr 25 _∩_
```

<!--
```agda
  open Order.Reasoning P
  open Meets ∩-meets public
  open Top has-top using (top; !) public

abstract
  is-meet-semilattice-is-prop
    : ∀ {o ℓ} {P : Poset o ℓ}
    → is-prop (is-meet-semilattice P)
  is-meet-semilattice-is-prop {P = P} p q = path where
    open Order.Diagram.Top P using (H-Level-Top)
    open is-meet-semilattice
    module p = is-meet-semilattice p
    module q = is-meet-semilattice q

    meetp : ∀ x y → x p.∩ y ≡ x q.∩ y
    meetp x y = meet-unique (p.∩-meets x y) (q.∩-meets x y)

    path : p ≡ q
    path i ._∩_ x y     = meetp x y i
    path i .∩-meets x y = is-prop→pathp (λ i → hlevel {T = is-meet P x y (meetp x y i)} 1) (p.∩-meets x y) (q.∩-meets x y) i
    path i .has-top     = hlevel {T = Top P} 1 p.has-top q.has-top i

private variable
  o ℓ o' ℓ' : Level
  P Q R : Poset o ℓ

instance
  H-Level-is-meet-semilattice : ∀ {n} → H-Level (is-meet-semilattice P) (suc n)
  H-Level-is-meet-semilattice = prop-instance is-meet-semilattice-is-prop
```
-->

A homomorphism of meet-semilattices is a monotone function that sends
finite meets to finite meets. In particular, it suffices to have $\top
\le f(\top)$, and

$$
f(a) \cap f(b) \le f(a \cap b)\text{,}
$$

since the converse direction of these inequalities is guaranteed by the
universal properties.

```agda
record
  is-meet-slat-hom
    {P : Poset o ℓ} {Q : Poset o' ℓ'} (f : Monotone P Q)
    (P-slat : is-meet-semilattice P) (Q-slat : is-meet-semilattice Q)
    : Type (o ⊔ ℓ')
  where
```

<!--
```agda
  no-eta-equality
  private
    module P = Poset P
    module Pₗ = is-meet-semilattice P-slat
    module Q = Order.Reasoning Q
    module Qₗ = is-meet-semilattice Q-slat
    open is-meet
```
-->

```agda
  field
    ∩-≤   : ∀ x y → (f # x) Qₗ.∩ (f # y) Q.≤ f # (x Pₗ.∩ y)
    top-≤ : Qₗ.top Q.≤ f # Pₗ.top
```

<!--
```agda
  pres-∩ : ∀ x y → f # (x Pₗ.∩ y) ≡ f # x Qₗ.∩ f # y
  pres-∩ x y =
    Q.≤-antisym
      (Qₗ.∩-universal (f # (x Pₗ.∩ y))
        (f .pres-≤ Pₗ.∩≤l)
        (f .pres-≤ Pₗ.∩≤r))
      (∩-≤ x y)

  pres-top : f # Pₗ.top ≡ Qₗ.top
  pres-top = Q.≤-antisym Qₗ.! top-≤

  pres-meets
    : ∀ {x y m}
    → is-meet P x y m
    → is-meet Q (f # x) (f # y) (f # m)
  pres-meets meet .is-meet.meet≤l = f .pres-≤ (meet .meet≤l)
  pres-meets meet .is-meet.meet≤r = f .pres-≤ (meet .meet≤r)
  pres-meets {x = x} {y = y} {m = m} meet .is-meet.greatest ub ub≤fx ub≤fy =
    ub                   Q.≤⟨ Qₗ.∩-universal ub ub≤fx ub≤fy ⟩
    (f # x) Qₗ.∩ (f # y) Q.≤⟨ ∩-≤ x y ⟩
    f # (x Pₗ.∩ y)       Q.≤⟨ f .pres-≤ (meet .greatest (x Pₗ.∩ y) Pₗ.∩≤l Pₗ.∩≤r) ⟩
    f # m                Q.≤∎

  pres-tops
    : ∀ {t}
    → is-top P t
    → is-top Q (f # t)
  pres-tops {t = t} t-top x =
    x          Q.≤⟨ Qₗ.! ⟩
    Qₗ.top     Q.≤⟨ top-≤ ⟩
    f # Pₗ.top Q.≤⟨ f .pres-≤ (t-top Pₗ.top) ⟩
    f # t      Q.≤∎

open is-meet-slat-hom

abstract
  is-meet-slat-hom-is-prop
    : ∀ {P : Poset o ℓ} {Q : Poset o' ℓ'} {f : Monotone P Q}
        {P-slat Q-slat}
    → is-prop (is-meet-slat-hom f P-slat Q-slat)
  is-meet-slat-hom-is-prop =
    Iso→is-hlevel 1 eqv hlevel!
    where unquoteDecl eqv = declare-record-iso eqv (quote is-meet-slat-hom)

instance
  H-Level-is-meet-slat-hom
    : ∀ {f : Monotone P Q} {P-slat Q-slat n}
    → H-Level (is-meet-slat-hom f P-slat Q-slat) (suc n)
  H-Level-is-meet-slat-hom = prop-instance is-meet-slat-hom-is-prop
```
-->

## The category of meet-semilattices

```agda
id-meet-slat-hom
  : ∀ (Pₗ : is-meet-semilattice P)
  → is-meet-slat-hom idₘ Pₗ Pₗ
id-meet-slat-hom {P = P} _ .∩-≤ _ _ = Poset.≤-refl P
id-meet-slat-hom {P = P} _ .top-≤ = Poset.≤-refl P

∘-meet-slat-hom
  : ∀ {Pₗ Qₗ Rₗ} {f : Monotone Q R} {g : Monotone P Q}
  → is-meet-slat-hom f Qₗ Rₗ
  → is-meet-slat-hom g Pₗ Qₗ
  → is-meet-slat-hom (f ∘ₘ g) Pₗ Rₗ
∘-meet-slat-hom {R = R} {f = f} {g = g} f-pres g-pres .∩-≤ x y =
  R .Poset.≤-trans (f-pres .∩-≤ (g # x) (g # y)) (f .pres-≤ (g-pres .∩-≤ x y))
∘-meet-slat-hom {R = R} {f = f} {g = g} f-pres g-pres .top-≤ =
  R .Poset.≤-trans (f-pres .top-≤) (f .pres-≤ (g-pres .top-≤))
```

```agda
Meet-slats-subcat : ∀ o ℓ → Subcat (Posets o ℓ) (o ⊔ ℓ) (o ⊔ ℓ)
Meet-slats-subcat o ℓ .Subcat.is-ob = is-meet-semilattice
Meet-slats-subcat o ℓ .Subcat.is-hom = is-meet-slat-hom
Meet-slats-subcat o ℓ .Subcat.is-hom-prop = hlevel!
Meet-slats-subcat o ℓ .Subcat.is-hom-id = id-meet-slat-hom
Meet-slats-subcat o ℓ .Subcat.is-hom-∘ = ∘-meet-slat-hom

Meet-slats : ∀ o ℓ → Precategory (lsuc o ⊔ lsuc ℓ) (o ⊔ ℓ)
Meet-slats o ℓ = Subcategory (Meet-slats-subcat o ℓ)
```

```agda
module Meet-slats {o} {ℓ} = Cat.Reasoning (Meet-slats o ℓ)

Meet-semilattice : ∀ o ℓ → Type _
Meet-semilattice o ℓ = Meet-slats.Ob {o} {ℓ}
```
