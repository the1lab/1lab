<!--
```agda
open import Cat.Functor.Subcategory
open import Cat.Prelude

open import Data.Fin.Indexed
open import Data.Fin.Finite
open import Data.Fin.Base hiding (_≤_)

open import Order.Diagram.Bottom
open import Order.Diagram.Join
open import Order.Diagram.Lub
open import Order.Base

import Cat.Reasoning

import Order.Diagram.Join.Reasoning as Joins
import Order.Reasoning
```
-->

```agda
module Order.Semilattice.Join where
```

# Join semilattices {defines=join-semilattice}

```agda
record is-join-semilattice {o ℓ} (P : Poset o ℓ) : Type (o ⊔ ℓ) where
  field
    _∪_     : ⌞ P ⌟ → ⌞ P ⌟ → ⌞ P ⌟
    ∪-joins : ∀ x y → is-join P x y (x ∪ y)
    has-bottom : Bottom P

  infixr 24 _∪_

  open Order.Reasoning P
  open Joins ∪-joins public
  open Bottom has-bottom using (bot; ¡) public

```

```agda
abstract
  is-join-semilattice-is-prop
    : ∀ {o ℓ} {P : Poset o ℓ}
    → is-prop (is-join-semilattice P)
  is-join-semilattice-is-prop {P = P} p q = path where
    open Order.Diagram.Bottom P using (H-Level-Bottom)
    open is-join-semilattice
    module p = is-join-semilattice p
    module q = is-join-semilattice q

    joinp : ∀ x y → x p.∪ y ≡ x q.∪ y
    joinp x y = join-unique (p.∪-joins x y) (q.∪-joins x y)

    path : p ≡ q
    path i ._∪_ x y     = joinp x y i
    path i .∪-joins x y = is-prop→pathp (λ i → hlevel {T = is-join P x y (joinp x y i)} 1) (p.∪-joins x y) (q.∪-joins x y) i
    path i .has-bottom  = hlevel {T = Bottom P} 1 p.has-bottom q.has-bottom i
```

<!--
```agda
private
  variable
    o ℓ o' ℓ' : Level
    P Q R : Poset o ℓ

instance
  H-Level-is-join-semilattice : ∀ {n} → H-Level (is-join-semilattice P) (suc n)
  H-Level-is-join-semilattice = prop-instance is-join-semilattice-is-prop
```
-->

```agda
record is-join-slat-hom
  {P : Poset o ℓ} {Q : Poset o' ℓ'}
  (f : Monotone P Q)
  (P-slat : is-join-semilattice P)
  (Q-slat : is-join-semilattice Q)
  : Type (o ⊔ ℓ')
  where
  no-eta-equality
  private
    module P = Poset P
    module Pₗ = is-join-semilattice P-slat
    module Q = Order.Reasoning Q
    module Qₗ = is-join-semilattice Q-slat
    open is-join
  field
    ∪-≤ : ∀ x y → f # (x Pₗ.∪ y) Q.≤ (f # x) Qₗ.∪ (f # y)
    bot-≤ : f # Pₗ.bot Q.≤ Qₗ.bot

  pres-∪ : ∀ x y → f # (x Pₗ.∪ y) ≡ (f # x) Qₗ.∪ (f # y)
  pres-∪ x y = Q.≤-antisym
    (∪-≤ x y)
    (Qₗ.∪-universal (f # (x Pₗ.∪ y))
      (f .pres-≤ Pₗ.l≤∪)
      (f .pres-≤ Pₗ.r≤∪))

  pres-bot : f # Pₗ.bot ≡ Qₗ.bot
  pres-bot = Q.≤-antisym bot-≤ Qₗ.¡

  pres-joins
    : ∀ {x y m}
    → is-join P x y m
    → is-join Q (f # x) (f # y) (f # m)
  pres-joins join .is-join.l≤join = f .pres-≤ (join .l≤join)
  pres-joins join .is-join.r≤join = f .pres-≤ (join .r≤join)
  pres-joins {x = x} {y = y} {m = m} join .is-join.least lb fx≤lb fy≤lb =
    f # m            Q.≤⟨ f .pres-≤ (join .least (x Pₗ.∪ y) Pₗ.l≤∪ Pₗ.r≤∪) ⟩
    f # (x Pₗ.∪ y)   Q.≤⟨ ∪-≤ x y ⟩
    f # x Qₗ.∪ f # y Q.≤⟨ Qₗ.∪-universal lb fx≤lb fy≤lb ⟩
    lb               Q.≤∎

  pres-bottoms
    : ∀ {b}
    → is-bottom P b
    → is-bottom Q (f # b)
  pres-bottoms {b = b} b-bot x =
    f # b      Q.≤⟨ f .pres-≤ (b-bot Pₗ.bot) ⟩
    f # Pₗ.bot Q.≤⟨ bot-≤ ⟩
    Qₗ.bot     Q.≤⟨ Qₗ.¡ ⟩
    x          Q.≤∎

open is-join-slat-hom
```

<!--
```agda
abstract
  is-join-slat-hom-is-prop
    : ∀ {P : Poset o ℓ} {Q : Poset o' ℓ'} {f : Monotone P Q} {P-slat Q-slat}
    → is-prop (is-join-slat-hom f P-slat Q-slat)
  is-join-slat-hom-is-prop =
    Iso→is-hlevel 1 eqv hlevel!
    where unquoteDecl eqv = declare-record-iso eqv (quote is-join-slat-hom)

instance
  H-Level-is-join-slat-hom
    : ∀ {f : Monotone P Q} {P-slat Q-slat n}
    → H-Level (is-join-slat-hom f P-slat Q-slat) (suc n)
  H-Level-is-join-slat-hom = prop-instance is-join-slat-hom-is-prop
```
-->

## The category of join-semilattices

```agda
id-join-slat-hom
  : ∀ (Pₗ : is-join-semilattice P)
  → is-join-slat-hom idₘ Pₗ Pₗ
id-join-slat-hom {P = P} _ .∪-≤ _ _ = Poset.≤-refl P
id-join-slat-hom {P = P} _ .bot-≤ = Poset.≤-refl P

∘-join-slat-hom
  : ∀ {Pₗ Qₗ Rₗ} {f : Monotone Q R} {g : Monotone P Q}
  → is-join-slat-hom f Qₗ Rₗ
  → is-join-slat-hom g Pₗ Qₗ
  → is-join-slat-hom (f ∘ₘ g) Pₗ Rₗ
∘-join-slat-hom {R = R} {f = f} {g = g} f-pres g-pres .∪-≤ x y =
  R .Poset.≤-trans (f .pres-≤ (g-pres .∪-≤ x y)) (f-pres .∪-≤ (g # x) (g # y))
∘-join-slat-hom {R = R} {f = f} {g = g} f-pres g-pres .bot-≤ =
  R .Poset.≤-trans (f .pres-≤ (g-pres .bot-≤)) (f-pres .bot-≤)
```

```agda
Join-slats-subcat : ∀ o ℓ → Subcat (Posets o ℓ) (o ⊔ ℓ) (o ⊔ ℓ)
Join-slats-subcat o ℓ .Subcat.is-ob = is-join-semilattice
Join-slats-subcat o ℓ .Subcat.is-hom = is-join-slat-hom
Join-slats-subcat o ℓ .Subcat.is-hom-prop = hlevel!
Join-slats-subcat o ℓ .Subcat.is-hom-id = id-join-slat-hom
Join-slats-subcat o ℓ .Subcat.is-hom-∘ = ∘-join-slat-hom

Join-slats : ∀ o ℓ → Precategory (lsuc o ⊔ lsuc ℓ) (o ⊔ ℓ)
Join-slats o ℓ = Subcategory (Join-slats-subcat o ℓ)
```

```agda
module Join-slats {o} {ℓ} = Cat.Reasoning (Join-slats o ℓ)

Forget-join-slat : ∀ {o ℓ} → Functor (Join-slats o ℓ) (Posets o ℓ)
Forget-join-slat = Forget-subcat

Join-semilattice : ∀ o ℓ → Type _
Join-semilattice o ℓ = Join-slats.Ob {o} {ℓ}
```
