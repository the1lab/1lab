<!--
```agda
open import Cat.Functor.Subcategory
open import Cat.Prelude

open import Data.Fin.Base hiding (_≤_)

open import Order.Diagram.Glb
open import Order.Diagram.Lub
open import Order.Base

import Cat.Reasoning

import Order.Reasoning
```
-->

```agda
module Order.Semilattice where
```

# Semilattices {defines=semilattice}

```agda
record is-meet-semilattice {o ℓ} (P : Poset o ℓ) : Type (o ⊔ ℓ) where
  field
    has-meets : ∀ x y → Meet P x y
    has-top : Top P

  module has-meets {x} {y} = Meet (has-meets x y)
  module has-top = Top has-top

  open Order.Reasoning P

  open has-meets renaming
    ( meet≤l to ∩-≤l
    ; meet≤r to ∩-≤r
    ; greatest to ∩-universal)
    public

  open has-top using (top; !) public

  infixr 25 _∩_
  _∩_ : ⌞ P ⌟ → ⌞ P ⌟ → ⌞ P ⌟
  x ∩ y = has-meets.glb {x} {y}

  ∩-idl : ∀ x → top ∩ x ≡ x
  ∩-idl x = ≤-antisym ∩-≤r (∩-universal _ ! ≤-refl)

  ∩-idr : ∀ x → x ∩ top ≡ x
  ∩-idr x = ≤-antisym ∩-≤l (∩-universal _ ≤-refl !)

  ∩-idem : ∀ x → x ∩ x ≡ x
  ∩-idem x = ≤-antisym ∩-≤l (∩-universal _ ≤-refl ≤-refl)

  ∩-comm : ∀ x y → x ∩ y ≡ y ∩ x
  ∩-comm x y =
    ≤-antisym
      (∩-universal _ ∩-≤r ∩-≤l)
      (∩-universal _ ∩-≤r ∩-≤l)

  ∩-assoc : ∀ x y z → x ∩ (y ∩ z) ≡ (x ∩ y) ∩ z
  ∩-assoc x y z =
    ≤-antisym
      (∩-universal _
        (∩-universal _ ∩-≤l (≤-trans ∩-≤r ∩-≤l))
        (≤-trans ∩-≤r ∩-≤r))
      (∩-universal _
        (≤-trans ∩-≤l ∩-≤l)
        (∩-universal _ (≤-trans ∩-≤l ∩-≤r) ∩-≤r))

  ⋂ᶠ : ∀ {n} (f : Fin n → ⌞ P ⌟) → ⌞ P ⌟
  ⋂ᶠ {zero} f  = top
  ⋂ᶠ {suc n} f = f fzero ∩ ⋂ᶠ (λ i → f (fsuc i))

  ⋂ᶠ-≤ : ∀ {n} {f : Fin n → ⌞ P ⌟} → (i : Fin n) → ⋂ᶠ f ≤ f i
  ⋂ᶠ-≤ {n = suc n} fzero = ∩-≤l
  ⋂ᶠ-≤ {n = suc n} (fsuc i) = ≤-trans ∩-≤r (⋂ᶠ-≤ i)

  ⋂ᶠ-universal
    : ∀ {n} {f : Fin n → ⌞ P ⌟}
    → (x : ⌞ P ⌟)
    → (∀ i → x ≤ f i)
    → x ≤ ⋂ᶠ f
  ⋂ᶠ-universal {n = zero} {f = f} x p = !
  ⋂ᶠ-universal {n = suc n} {f = f} x p =
    ∩-universal _ (p fzero) (⋂ᶠ-universal x (p ⊙ fsuc))
```

```agda
record is-join-semilattice {o ℓ} (P : Poset o ℓ) : Type (o ⊔ ℓ) where
  field
    has-joins : ∀ x y → Join P x y
    has-bot : Bottom P

  module has-joins {x} {y} = Join (has-joins x y)
  module has-bot = Bottom has-bot

  open Order.Reasoning P

  open has-joins renaming
    (l≤join to ∪-≤l
    ; r≤join to ∪-≤r
    ; least to ∪-universal)
    public

  open has-bot using (bot; ¡) public

  infixr 24 _∪_
  _∪_ : ⌞ P ⌟ → ⌞ P ⌟ → ⌞ P ⌟
  x ∪ y = has-joins.lub {x} {y}

  ∪-idl : ∀ x → bot ∪ x ≡ x
  ∪-idl x = ≤-antisym (∪-universal _ ¡ ≤-refl) ∪-≤r

  ∪-idr : ∀ x → x ∪ bot ≡ x
  ∪-idr x = ≤-antisym (∪-universal _ ≤-refl ¡) ∪-≤l

  ∪-idem : ∀ x → x ∪ x ≡ x
  ∪-idem x = ≤-antisym  (∪-universal _ ≤-refl ≤-refl) ∪-≤l


  ∪-comm : ∀ x y → x ∪ y ≡ y ∪ x
  ∪-comm x y =
    ≤-antisym
      (∪-universal _ ∪-≤r ∪-≤l)
      (∪-universal _ ∪-≤r ∪-≤l)

  ∪-assoc : ∀ x y z → x ∪ (y ∪ z) ≡ (x ∪ y) ∪ z
  ∪-assoc x y z =
    ≤-antisym
      (∪-universal _
        (≤-trans ∪-≤l ∪-≤l)
        (∪-universal _ (≤-trans ∪-≤r ∪-≤l) ∪-≤r))
      (∪-universal _
        (∪-universal _ ∪-≤l (≤-trans ∪-≤l ∪-≤r))
        (≤-trans ∪-≤r ∪-≤r))

  ⋃ᶠ : ∀ {n} (f : Fin n → ⌞ P ⌟) → ⌞ P ⌟
  ⋃ᶠ {zero} f  = bot
  ⋃ᶠ {suc n} f = f fzero ∪ ⋃ᶠ (λ i → f (fsuc i))

  ⋃ᶠ-≤ : ∀ {n} {f : Fin n → ⌞ P ⌟} → (i : Fin n) → f i ≤ ⋃ᶠ f
  ⋃ᶠ-≤ {n = suc n} fzero = ∪-≤l
  ⋃ᶠ-≤ {n = suc n} (fsuc i) = ≤-trans (⋃ᶠ-≤ i) ∪-≤r

  ⋃ᶠ-universal
    : ∀ {n} {f : Fin n → ⌞ P ⌟}
    → (x : ⌞ P ⌟)
    → (∀ i → f i ≤ x)
    → ⋃ᶠ f ≤ x
  ⋃ᶠ-universal {n = zero} {f = f} x p = ¡
  ⋃ᶠ-universal {n = suc n} {f = f} x p =
    ∪-universal _ (p fzero) (⋃ᶠ-universal x (p ⊙ fsuc))
```

```agda
is-meet-semilattice-is-prop
  : ∀ {o ℓ} {P : Poset o ℓ}
  → is-prop (is-meet-semilattice P)
is-meet-semilattice-is-prop {P = P} =
  Iso→is-hlevel 1 eqv hlevel!
  where
    open Order.Diagram.Glb P
    unquoteDecl eqv = declare-record-iso eqv (quote is-meet-semilattice)

is-join-semilattice-is-prop
  : ∀ {o ℓ} {P : Poset o ℓ}
  → is-prop (is-join-semilattice P)
is-join-semilattice-is-prop {P = P} =
  Iso→is-hlevel 1 eqv hlevel!
  where
    open Order.Diagram.Lub P
    unquoteDecl eqv = declare-record-iso eqv (quote is-join-semilattice)
```

<!--
```agda
private
  variable
    o ℓ o' ℓ' : Level
    P Q R : Poset o ℓ

instance
  H-Level-is-meet-semilattice : ∀ {n} → H-Level (is-meet-semilattice P) (suc n)
  H-Level-is-meet-semilattice = prop-instance is-meet-semilattice-is-prop

  H-Level-is-join-semilattice : ∀ {n} → H-Level (is-join-semilattice P) (suc n)
  H-Level-is-join-semilattice = prop-instance is-join-semilattice-is-prop
```
-->

## Semilattice Homomorphisms


```agda
record is-meet-slat-hom
  {P : Poset o ℓ} {Q : Poset o' ℓ'}
  (f : Monotone P Q)
  (P-slat : is-meet-semilattice P)
  (Q-slat : is-meet-semilattice Q)
  : Type (o ⊔ ℓ')
  where
  no-eta-equality
  private
    module P = Poset P
    module Pₗ = is-meet-semilattice P-slat
    module Q = Order.Reasoning Q
    module Qₗ = is-meet-semilattice Q-slat
    open is-meet
  field
    ∩-≤ : ∀ x y → (f # x) Qₗ.∩ (f # y) Q.≤ f # (x Pₗ.∩ y)
    top-≤ : Qₗ.top Q.≤ f # Pₗ.top

  pres-∩ : ∀ x y → f # (x Pₗ.∩ y) ≡ (f # x) Qₗ.∩ (f # y)
  pres-∩ x y =
    Q.≤-antisym
      (Qₗ.∩-universal (f # (x Pₗ.∩ y))
        (f .pres-≤ Pₗ.∩-≤l)
        (f .pres-≤ Pₗ.∩-≤r))
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
    f # (x Pₗ.∩ y)       Q.≤⟨ f .pres-≤ (meet .greatest (x Pₗ.∩ y) Pₗ.∩-≤l Pₗ.∩-≤r) ⟩
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
```

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
  pres-∪ x y =
    Q.≤-antisym
      (∪-≤ x y)
      (Qₗ.∪-universal (f # (x Pₗ.∪ y))
        (f .pres-≤ Pₗ.∪-≤l)
        (f .pres-≤ Pₗ.∪-≤r))

  pres-bot : f # Pₗ.bot ≡ Qₗ.bot
  pres-bot = Q.≤-antisym bot-≤ Qₗ.¡

  pres-joins
    : ∀ {x y m}
    → is-join P x y m
    → is-join Q (f # x) (f # y) (f # m)
  pres-joins join .is-join.l≤join = f .pres-≤ (join .l≤join)
  pres-joins join .is-join.r≤join = f .pres-≤ (join .r≤join)
  pres-joins {x = x} {y = y} {m = m} join .is-join.least lb fx≤lb fy≤lb =
    f # m            Q.≤⟨ f .pres-≤ (join .least (x Pₗ.∪ y) Pₗ.∪-≤l Pₗ.∪-≤r) ⟩
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
is-meet-slat-hom-is-prop
  : {P : Poset o ℓ} {Q : Poset o' ℓ'}
  → {f : Monotone P Q}
  → {P-slat : is-meet-semilattice P}
  → {Q-slat : is-meet-semilattice Q}
  → is-prop (is-meet-slat-hom f P-slat Q-slat)
is-meet-slat-hom-is-prop =
  Iso→is-hlevel 1 eqv hlevel!
  where unquoteDecl eqv = declare-record-iso eqv (quote is-meet-slat-hom)

is-join-slat-hom-is-prop
  : {P : Poset o ℓ} {Q : Poset o' ℓ'}
  → {f : Monotone P Q}
  → {P-slat : is-join-semilattice P}
  → {Q-slat : is-join-semilattice Q}
  → is-prop (is-join-slat-hom f P-slat Q-slat)
is-join-slat-hom-is-prop =
  Iso→is-hlevel 1 eqv hlevel!
  where unquoteDecl eqv = declare-record-iso eqv (quote is-join-slat-hom)

instance
  H-Level-is-meet-slat-hom
    : ∀ {f : Monotone P Q}
    → {P-slat : is-meet-semilattice P} {Q-slat : is-meet-semilattice Q}
    → ∀ {n} → H-Level (is-meet-slat-hom f P-slat Q-slat) (suc n)
  H-Level-is-meet-slat-hom = prop-instance is-meet-slat-hom-is-prop

  H-Level-is-join-slat-hom
    : ∀ {f : Monotone P Q}
    → {P-slat : is-join-semilattice P} {Q-slat : is-join-semilattice Q}
    → ∀ {n} → H-Level (is-join-slat-hom f P-slat Q-slat) (suc n)
  H-Level-is-join-slat-hom = prop-instance is-join-slat-hom-is-prop
```
-->

## Categories of Semilattices

```agda
id-meet-slat-hom
  : ∀ (Pₗ : is-meet-semilattice P)
  → is-meet-slat-hom idₘ Pₗ Pₗ
id-meet-slat-hom {P = P} _ .∩-≤ _ _ = Poset.≤-refl P
id-meet-slat-hom {P = P} _ .top-≤ = Poset.≤-refl P

id-join-slat-hom
  : ∀ (Pₗ : is-join-semilattice P)
  → is-join-slat-hom idₘ Pₗ Pₗ
id-join-slat-hom {P = P} _ .∪-≤ _ _ = Poset.≤-refl P
id-join-slat-hom {P = P} _ .bot-≤ = Poset.≤-refl P

∘-meet-slat-hom
  : {Pₗ : is-meet-semilattice P}
  → {Qₗ : is-meet-semilattice Q}
  → {Rₗ : is-meet-semilattice R}
  → {f : Monotone Q R} {g : Monotone P Q}
  → is-meet-slat-hom f Qₗ Rₗ
  → is-meet-slat-hom g Pₗ Qₗ
  → is-meet-slat-hom (f ∘ₘ g) Pₗ Rₗ
∘-meet-slat-hom {R = R} {f = f} {g = g} f-pres g-pres .∩-≤ x y =
  Poset.≤-trans R (f-pres .∩-≤ (g # x) (g # y)) (f .pres-≤ (g-pres .∩-≤ x y))
∘-meet-slat-hom {R = R} {f = f} {g = g} f-pres g-pres .top-≤ =
  Poset.≤-trans R (f-pres .top-≤) (f .pres-≤ (g-pres .top-≤))

∘-join-slat-hom
  : {Pₗ : is-join-semilattice P}
  → {Qₗ : is-join-semilattice Q}
  → {Rₗ : is-join-semilattice R}
  → {f : Monotone Q R} {g : Monotone P Q}
  → is-join-slat-hom f Qₗ Rₗ
  → is-join-slat-hom g Pₗ Qₗ
  → is-join-slat-hom (f ∘ₘ g) Pₗ Rₗ
∘-join-slat-hom {R = R} {f = f} {g = g} f-pres g-pres .∪-≤ x y =
  Poset.≤-trans R (f .pres-≤ (g-pres .∪-≤ x y)) (f-pres .∪-≤ (g # x) (g # y))
∘-join-slat-hom {R = R} {f = f} {g = g} f-pres g-pres .bot-≤ =
  Poset.≤-trans R (f .pres-≤ (g-pres .bot-≤)) (f-pres .bot-≤)

Meet-slat-subcat : ∀ o ℓ → Subcat (Posets o ℓ) (o ⊔ ℓ) (o ⊔ ℓ)
Meet-slat-subcat o ℓ .Subcat.is-ob = is-meet-semilattice
Meet-slat-subcat o ℓ .Subcat.is-hom = is-meet-slat-hom
Meet-slat-subcat o ℓ .Subcat.is-hom-prop = hlevel!
Meet-slat-subcat o ℓ .Subcat.is-hom-id = id-meet-slat-hom
Meet-slat-subcat o ℓ .Subcat.is-hom-∘ = ∘-meet-slat-hom

Join-slat-subcat : ∀ o ℓ → Subcat (Posets o ℓ) (o ⊔ ℓ) (o ⊔ ℓ)
Join-slat-subcat o ℓ .Subcat.is-ob = is-join-semilattice
Join-slat-subcat o ℓ .Subcat.is-hom = is-join-slat-hom
Join-slat-subcat o ℓ .Subcat.is-hom-prop = hlevel!
Join-slat-subcat o ℓ .Subcat.is-hom-id = id-join-slat-hom
Join-slat-subcat o ℓ .Subcat.is-hom-∘ = ∘-join-slat-hom

Meet-slats : ∀ o ℓ → Precategory (lsuc o ⊔ lsuc ℓ) (o ⊔ ℓ)
Meet-slats o ℓ = Subcategory (Meet-slat-subcat o ℓ)

Join-slats : ∀ o ℓ → Precategory (lsuc o ⊔ lsuc ℓ) (o ⊔ ℓ)
Join-slats o ℓ = Subcategory (Join-slat-subcat o ℓ)
```

```agda
module Meet-slats {o} {ℓ} = Cat.Reasoning (Meet-slats o ℓ)
module Join-slats {o} {ℓ} = Cat.Reasoning (Join-slats o ℓ)
```

```agda
Meet-semilattice : ∀ o ℓ → Type _
Meet-semilattice o ℓ = Meet-slats.Ob {o} {ℓ}

Join-semilattice : ∀ o ℓ → Type _
Join-semilattice o ℓ = Join-slats.Ob {o} {ℓ}
```

