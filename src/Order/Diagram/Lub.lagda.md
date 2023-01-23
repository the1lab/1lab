```agda
open import Cat.Diagram.Coproduct
open import Cat.Prelude

open import Data.Bool

open import Order.Base
open import Order.Cat

import Order.Reasoning as Poset

module Order.Diagram.Lub where
```

# Least upper bounds

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
module _ {ℓ ℓ′} (P : Poset ℓ ℓ′) where
  private module P = Poset P

  record is-lub {ℓᵢ} {I : Type ℓᵢ} (F : I → P.Ob) (lub : P.Ob)
          : Type (ℓ ⊔ ℓ′ ⊔ ℓᵢ) where
    field
      fam≤lub : ∀ i → F i P.≤ lub
      least   : (ub′ : P.Ob) → (∀ i → F i P.≤ ub′) → lub P.≤ ub′
```

<!--
```agda
  open is-lub

  Lub : ∀ {ℓ′} {I : Type ℓ′} (F : I → ⌞ P ⌟) → Type _
  Lub F = Σ P.Ob (is-lub F)

  Bot : Type _
  Bot = Σ P.Ob λ bot → ∀ x → bot P.≤ x

  private unquoteDecl eqv = declare-record-iso eqv (quote is-lub)

  instance
    H-Level-is-lub
      : ∀ {ℓᵢ} {I : Type ℓᵢ} {F : I → P.Ob} {lub : P.Ob} {n}
      → H-Level (is-lub F lub) (suc n)
    H-Level-is-lub = prop-instance $ Iso→is-hlevel 1 eqv (hlevel 1)

  lub-unique : ∀ {ℓᵢ} {I : Type ℓᵢ} {F : I → P.Ob}
             → is-prop (Lub F)
  lub-unique (lub , is) (lub′ , is′) = Σ-prop-path! $ P.≤-antisym
    (is .least lub′ (is′ .fam≤lub))
    (is′ .least lub (is .fam≤lub))
```
-->

In the binary case, a least upper bound is called a **join**. A short
computation shows that being a join is _precisely_ being the lub of a
family of two elements.

```agda
  record is-join (a b : P.Ob) (lub : P.Ob) : Type (ℓ ⊔ ℓ′) where
    field
      l≤join : a P.≤ lub
      r≤join : b P.≤ lub
      least  : (ub′ : P.Ob) → a P.≤ ub′ → b P.≤ ub′ → lub P.≤ ub′

  open is-join

  is-join→is-lub : ∀ {a b lub} → is-join a b lub → is-lub (if_then a else b) lub
  is-join→is-lub join .fam≤lub true = join .l≤join
  is-join→is-lub join .fam≤lub false = join .r≤join
  is-join→is-lub join .least ub′ x = join .least ub′ (x true) (x false)

  is-lub→is-join : ∀ {F : Bool → P.Ob} {lub} → is-lub F lub → is-join (F true) (F false) lub
  is-lub→is-join lub .l≤join = lub .fam≤lub true
  is-lub→is-join lub .r≤join = lub .fam≤lub false
  is-lub→is-join lub .least ub′ a<ub′ b<ub′ = lub .least ub′ λ where
    true  → a<ub′
    false → b<ub′
```

<!--
```
  private unquoteDecl eqv′ = declare-record-iso eqv′ (quote is-join)

  Join : ⌞ P ⌟ → ⌞ P ⌟ → Type _
  Join a b = Σ P.Ob (is-join a b)

  instance
    H-Level-is-join
      : ∀ {a b lub : P.Ob} {n}
      → H-Level (is-join a b lub) (suc n)
    H-Level-is-join = prop-instance $ Iso→is-hlevel 1 eqv′ (hlevel 1)

  open is-iso
  is-join≃is-lub : ∀ {a b lub : P.Ob} → is-equiv (is-join→is-lub {a} {b} {lub})
  is-join≃is-lub = prop-ext! _ is-lub→is-join .snd

  join-unique : ∀ {a b} → is-prop (Join a b)
  join-unique {a} {b} = transport
    (λ i → is-prop (Σ P.Ob λ x → ua (_ , is-join≃is-lub {a} {b} {x}) (~ i)))
    lub-unique
```
-->

## As coproducts

Joins are the “thinning” of coproducts; Put another way, when we allow a
_set_ of relators rather than insisting on a propositional relation, the
concept of join needs to be refined to that of coproduct.

```agda
  open is-coproduct
  open Coproduct

  is-join→coproduct : ∀ {a b lub : P.Ob} → is-join a b lub → Coproduct (poset→category P) a b
  is-join→coproduct lub .coapex = _
  is-join→coproduct lub .in₀ = lub .is-join.l≤join
  is-join→coproduct lub .in₁ = lub .is-join.r≤join
  is-join→coproduct lub .has-is-coproduct .[_,_] a<q b<q =
    lub .is-join.least _ a<q b<q
  is-join→coproduct lub .has-is-coproduct .in₀∘factor = prop!
  is-join→coproduct lub .has-is-coproduct .in₁∘factor = prop!
  is-join→coproduct lub .has-is-coproduct .unique _ _ _ = prop!
```
