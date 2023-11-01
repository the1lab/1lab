<!--
```agda
open import Cat.Diagram.Coproduct
open import Cat.Diagram.Initial
open import Cat.Prelude

open import Data.Bool

open import Order.Base
open import Order.Cat

import Order.Reasoning
```
-->

```agda
module Order.Diagram.Lub {o ℓ} (P : Poset o ℓ) where
```

<!--
```agda
open Order.Reasoning P
```
-->

# Least upper bounds {defines="least-upper-bound"}

A **lub** $u$ (short for **least upper bound**) for a family of
elements $(a_i)_{i : I}$ is, as the name implies, a least elemnet among
the upper boudns of the $a_i$. Being an upper bound means that we have
$a_i \le u$ for all $i : I$; Being the _least_ upper bound means that
if we're given some other $l$ satisfying $a_i \le l$ (for each $i$),
then we have $u \le l$.

The same observation about the naming of [glbs vs meets] applies to
lubs, with the binary name being **join**.

[glbs vs meets]: Order.Diagram.Glb.html

```agda
record is-lub
  {ℓᵢ} {I : Type ℓᵢ} (F : I → Ob) (lub : Ob)
  : Type (o ⊔ ℓ ⊔ ℓᵢ)
  where
  no-eta-equality
  field
    fam≤lub : ∀ i → F i ≤ lub
    least   : (ub' : Ob) → (∀ i → F i ≤ ub') → lub ≤ ub'

record Lub {ℓᵢ} {I : Type ℓᵢ} (F : I → Ob) : Type (o ⊔ ℓ ⊔ ℓᵢ) where
  no-eta-equality
  field
    lub : Ob
    has-lub : is-lub F lub
  open is-lub has-lub public

open is-lub
```

<!--
```agda
private unquoteDecl eqv = declare-record-iso eqv (quote is-lub)

is-lub-is-prop
  : ∀ {ℓᵢ} {I : Type ℓᵢ} {F : I → Ob} {lub : Ob}
  → is-prop (is-lub F lub)
is-lub-is-prop = Iso→is-hlevel 1 eqv (hlevel 1)

instance
  H-Level-is-lub
    : ∀ {ℓᵢ} {I : Type ℓᵢ} {F : I → Ob} {lub : Ob} {n}
    → H-Level (is-lub F lub) (suc n)
  H-Level-is-lub = prop-instance is-lub-is-prop

lub-unique
  : ∀ {ℓᵢ} {I : Type ℓᵢ} {F : I → Ob} {x y}
  → is-lub F x → is-lub F y
  → x ≡ y
lub-unique {x = x} {y = y} lub lub' = ≤-antisym
  (lub .least y (lub' .fam≤lub))
  (lub' .least x (lub .fam≤lub))

Lub-is-prop
  : ∀ {ℓᵢ} {I : Type ℓᵢ} {F : I → Ob}
  → is-prop (Lub F)
Lub-is-prop p q i .Lub.lub =
  lub-unique (Lub.has-lub p) (Lub.has-lub q) i
Lub-is-prop {F = F} p q i .Lub.has-lub =
  is-prop→pathp
    (λ i → is-lub-is-prop {lub = lub-unique (Lub.has-lub p) (Lub.has-lub q) i})
    (Lub.has-lub p) (Lub.has-lub q) i

instance
  H-Level-Lub
    : ∀ {ℓᵢ} {I : Type ℓᵢ} {F : I → Ob} {n}
    → H-Level (Lub F) (suc n)
  H-Level-Lub = prop-instance Lub-is-prop

lift-is-lub
  : ∀ {ℓᵢ ℓᵢ'} {I : Type ℓᵢ} {F : I → Ob} {lub}
  → is-lub F lub → is-lub (F ⊙ Lift.lower {ℓ = ℓᵢ'}) lub
lift-is-lub is .fam≤lub (lift ix) = is .fam≤lub ix
lift-is-lub is .least ub' le = is .least ub' (le ⊙ lift)

lift-lub
  : ∀ {ℓᵢ ℓᵢ'} {I : Type ℓᵢ} {F : I → Ob}
  → Lub F → Lub (F ⊙ Lift.lower {ℓ = ℓᵢ'})
lift-lub lub .Lub.lub = Lub.lub lub
lift-lub lub .Lub.has-lub = lift-is-lub (Lub.has-lub lub)

lower-is-lub
  : ∀ {ℓᵢ ℓᵢ'} {I : Type ℓᵢ} {F : I → Ob} {lub}
  → is-lub (F ⊙ Lift.lower {ℓ = ℓᵢ'}) lub → is-lub F lub
lower-is-lub is .fam≤lub ix = is .fam≤lub (lift ix)
lower-is-lub is .least ub' le = is .least ub' (le ⊙ Lift.lower)

lower-lub
  : ∀ {ℓᵢ ℓᵢ'} {I : Type ℓᵢ} {F : I → Ob}
  → Lub (F ⊙ Lift.lower {ℓ = ℓᵢ'}) → Lub F
lower-lub lub .Lub.lub = Lub.lub lub
lower-lub lub .Lub.has-lub = lower-is-lub (Lub.has-lub lub)
```
-->

Let $f : I \to P$ be a family. If there is some $i$ such that
for all $j$, $f(j) < f(i)$, then $f(i)$ is the least upper bound of
$f$.

```agda
fam-bound→is-lub
  : ∀ {ℓᵢ} {I : Type ℓᵢ} {F : I → Ob}
  → (i : I) → (∀ j → F j ≤ F i)
  → is-lub F (F i)
fam-bound→is-lub i ge .fam≤lub = ge
fam-bound→is-lub i ge .least y le = le i
```

If $x$ is the least upper bound of a constant family, then
$x$ must be equal to every member of the family.

```agda
lub-of-const-fam
  : ∀ {ℓᵢ} {I : Type ℓᵢ} {F : I → Ob} {x}
  → (∀ i j → F i ≡ F j)
  → is-lub F x
  → ∀ i → F i ≡ x
lub-of-const-fam {F = F} is-const x-lub i =
  ≤-antisym
    (fam≤lub x-lub i)
    (least x-lub (F i) λ j → path→≥ (is-const i j))
```

Furthermore, if $f : I \to A$ is a constant family and $I$ is merely
inhabited, then $f$ has a least upper bound.

```agda
const-inhabited-fam→is-lub
  : ∀ {ℓᵢ} {I : Type ℓᵢ} {F : I → Ob} {x}
  → (∀ i → F i ≡ x)
  → ∥ I ∥
  → is-lub F x
const-inhabited-fam→is-lub {I = I} {F = F} {x = x} is-const =
  ∥-∥-rec is-lub-is-prop mk-is-lub where
    mk-is-lub : I → is-lub F x
    mk-is-lub i .is-lub.fam≤lub j = path→≤ (is-const j)
    mk-is-lub i .is-lub.least y le =
      x   =˘⟨ is-const i ⟩
      F i ≤⟨ le i ⟩
      y ≤∎

const-inhabited-fam→lub
  : ∀ {ℓᵢ} {I : Type ℓᵢ} {F : I → Ob}
  → (∀ i j → F i ≡ F j)
  → ∥ I ∥
  → Lub F
const-inhabited-fam→lub {I = I} {F = F} is-const =
  ∥-∥-rec Lub-is-prop mk-lub where
    mk-lub : I → Lub F
    mk-lub i .Lub.lub = F i
    mk-lub i .Lub.has-lub =
      const-inhabited-fam→is-lub (λ j → is-const j i) (inc i)
```

## Joins

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

open is-join

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
  H-Level-is-join = prop-instance $ Iso→is-hlevel 1 eqv' (hlevel 1)

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

## Bottom elements

A **bottom element** in a partial order $(P, \le)$ is an element $\bot :
P$ that is smaller than any other element of $P$. This is the same as
being a least upper upper bound for the empty family $\bot \to P$.

```agda
is-bottom : Ob → Type _
is-bottom bot = ∀ x → bot ≤ x

record Bottom : Type (o ⊔ ℓ) where
  no-eta-equality
  field
    bot : Ob
    has-bottom : is-bottom bot

  ¡ : ∀ {x} → bot ≤ x
  ¡ = has-bottom _

is-bottom→is-lub : ∀ {lub} → is-bottom lub → is-lub absurd lub
is-bottom→is-lub is-bot .least x _ = is-bot x

is-lub→is-bottom : ∀ {lub} → is-lub absurd lub → is-bottom lub
is-lub→is-bottom lub x = lub .least x λ ()
```

<!--
```agda
is-bottom-is-prop : ∀ x → is-prop (is-bottom x)
is-bottom-is-prop _ = hlevel 1

bottom-unique : ∀ {x y} → is-bottom x → is-bottom y → x ≡ y
bottom-unique p q = ≤-antisym (p _) (q _)

Bottom-is-prop : is-prop Bottom
Bottom-is-prop p q i .Bottom.bot =
  bottom-unique (Bottom.has-bottom p) (Bottom.has-bottom q) i
Bottom-is-prop p q i .Bottom.has-bottom =
  is-prop→pathp
    (λ i → is-bottom-is-prop (bottom-unique (Bottom.has-bottom p) (Bottom.has-bottom q) i))
    (Bottom.has-bottom p) (Bottom.has-bottom q) i

instance
  H-Level-Bottom
    : ∀ {n}
    → H-Level Bottom (suc n)
  H-Level-Bottom = prop-instance Bottom-is-prop

Bottom→Lub : Bottom → Lub absurd
Bottom→Lub bottom .Lub.lub = Bottom.bot bottom
Bottom→Lub bottom .Lub.has-lub = is-bottom→is-lub (Bottom.has-bottom bottom)

Lub→Bottom : Lub absurd → Bottom
Lub→Bottom lub .Bottom.bot = Lub.lub lub
Lub→Bottom lub .Bottom.has-bottom = is-lub→is-bottom (Lub.has-lub lub)

is-bottom≃is-lub : ∀ {lub} → is-equiv (is-bottom→is-lub {lub})
is-bottom≃is-lub = prop-ext! _ is-lub→is-bottom .snd

Bottom≃Lub : is-equiv Bottom→Lub
Bottom≃Lub = prop-ext! _ Lub→Bottom .snd
```
-->

### As initial objects

Bottoms are the decategorifcation of [[initial objects]]; we don't need to
require the uniqueness of the universal morphism, as we've replaced our
hom-sets with hom-props!

```agda
is-bottom→initial : ∀ {x} → is-bottom x → is-initial (poset→category P) x
is-bottom→initial is-bot x .centre = is-bot x
is-bottom→initial is-bot x .paths _ = ≤-thin _ _

initial→is-bottom : ∀ {x} → is-initial (poset→category P) x → is-bottom x
initial→is-bottom initial x = initial x .centre
```
