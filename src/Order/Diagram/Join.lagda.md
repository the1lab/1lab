<!--
```agda
open import Cat.Diagram.Coproduct
open import Cat.Prelude

open import Data.Bool

open import Order.Base
open import Order.Cat

import Order.Diagram.Lub
import Order.Reasoning
```
-->

```agda
module Order.Diagram.Join {o ℓ} (P : Poset o ℓ) where
```

<!--
```agda
open Order.Diagram.Lub P
open Order.Reasoning P
```
-->

# Joins {defines="join"}

In the binary case, a least upper bound is called a **join**. A short
computation shows that being a join is _precisely_ being the lub of a
family of two elements.

```agda
record is-join (a b : Ob) (lub : Ob) : Type (o ⊔ ℓ) where
  no-eta-equality
  field
    l≤join : a ≤ lub
    r≤join : b ≤ lub
    least  : (ub' : Ob) → a ≤ ub' → b ≤ ub' → lub ≤ ub'

record Join (a b : Ob) : Type (o ⊔ ℓ) where
  no-eta-equality
  field
    lub : Ob
    has-join : is-join a b lub
  open is-join has-join public

Has-joins : Type (o ⊔ ℓ)
Has-joins = ∀ x y → Join x y

open is-join
```

<!--
```agda
open is-lub
open Lub
```
-->

```agda
is-join→is-lub : ∀ {a b lub} → is-join a b lub → is-lub (if_then a else b) lub
is-join→is-lub join .fam≤lub true = join .l≤join
is-join→is-lub join .fam≤lub false = join .r≤join
is-join→is-lub join .least ub' x = join .least ub' (x true) (x false)

is-lub→is-join : ∀ {F : Bool → Ob} {lub} → is-lub F lub → is-join (F true) (F false) lub
is-lub→is-join lub .l≤join = lub .fam≤lub true
is-lub→is-join lub .r≤join = lub .fam≤lub false
is-lub→is-join lub .least ub' a<ub' b<ub' = lub .least ub' λ where
  true  → a<ub'
  false → b<ub'
```

<!--
```
private unquoteDecl eqv' = declare-record-iso eqv' (quote is-join)

instance
  H-Level-is-join
    : ∀ {a b lub : Ob} {n}
    → H-Level (is-join a b lub) (suc n)
  H-Level-is-join = prop-instance $ Iso→is-hlevel 1 eqv' hlevel!

join-unique
  : ∀ {a b x y}
  → is-join a b x → is-join a b y
  → x ≡ y
join-unique {a} {b} {x} {y} p q =
  lub-unique (is-join→is-lub p) (is-join→is-lub q)

Join-is-prop : ∀ {a b} → is-prop (Join a b)
Join-is-prop p q i .Join.lub =
  join-unique (Join.has-join p) (Join.has-join q) i
Join-is-prop {a = a} {b = b} p q i .Join.has-join =
  is-prop→pathp {B = λ i → is-join a b (join-unique (Join.has-join p) (Join.has-join q) i)}
    (λ i → hlevel 1)
    (Join.has-join p) (Join.has-join q) i

instance
  H-Level-Join
    : ∀ {a b} {n}
    → H-Level (Join a b) (suc n)
  H-Level-Join = prop-instance Join-is-prop

Join→Lub : ∀ {a b} → Join a b → Lub (if_then a else b)
Join→Lub join .Lub.lub = Join.lub join
Join→Lub join .Lub.has-lub = is-join→is-lub (Join.has-join join)

Lub→Join : ∀ {a b} → Lub (if_then a else b) → Join a b
Lub→Join lub .Join.lub = Lub.lub lub
Lub→Join lub .Join.has-join = is-lub→is-join (Lub.has-lub lub)

is-join≃is-lub : ∀ {a b lub : Ob} → is-equiv (is-join→is-lub {a} {b} {lub})
is-join≃is-lub = prop-ext! _ is-lub→is-join .snd

Join≃Lub : ∀ {a b} → is-equiv (Join→Lub {a} {b})
Join≃Lub = prop-ext! _ Lub→Join .snd
```
-->

An important lemma about joins is that, if $x \le y$, then the least
upper bound of $x$ and $y$ is just $y$:

```agda
gt→is-join : ∀ {a b} → a ≤ b → is-join a b b
gt→is-join a≤b .l≤join = a≤b
gt→is-join a≤b .r≤join = ≤-refl
gt→is-join a≤b .least ub' _ b≤ub' = b≤ub'

gt-join : ∀ {a b l} → a ≤ b → is-join a b l → b ≡ l
gt-join a≤b l = join-unique (gt→is-join a≤b) l
```

### As coproducts

Joins are the “thinning” of [[coproducts]]; Put another way, when we
allow a _set_ of relators, rather than insisting on a propositional
relation, the concept of join needs to be refined to that of coproduct.

```agda
open is-coproduct
open Coproduct

is-join→coproduct : ∀ {a b lub : Ob} → is-join a b lub → Coproduct (poset→category P) a b
is-join→coproduct lub .coapex = _
is-join→coproduct lub .in₀ = lub .is-join.l≤join
is-join→coproduct lub .in₁ = lub .is-join.r≤join
is-join→coproduct lub .has-is-coproduct .[_,_] a<q b<q =
  lub .is-join.least _ a<q b<q
is-join→coproduct lub .has-is-coproduct .in₀∘factor = prop!
is-join→coproduct lub .has-is-coproduct .in₁∘factor = prop!
is-join→coproduct lub .has-is-coproduct .unique _ _ _ = prop!
```
