```agda
open import Cat.Order.Base
open import Cat.Prelude

open import Data.Bool

module Cat.Order.Diagram.Lub where
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

[glbs vs meets]: Cat.Order.Diagram.Glb.html

```agda
module _ {ℓ ℓ′} (P : Poset ℓ ℓ′) where
  private module P = Poset P

  record is-lub {ℓᵢ} {I : Type ℓᵢ} (F : I → P.Ob) (lub : P.Ob)
          : Type (ℓ ⊔ ℓ′ ⊔ ℓᵢ) where
    field
      fam≤lub : ∀ i → F i P.≤ lub
      least   : (ub′ : P.Ob) → (∀ i → F i P.≤ ub′) → lub P.≤ ub′

  open is-lub

  private unquoteDecl eqv = declare-record-iso eqv (quote is-lub)

  instance
    H-Level-is-lub
      : ∀ {ℓᵢ} {I : Type ℓᵢ} {F : I → P.Ob} {lub : P.Ob} {n}
      → H-Level (is-lub F lub) (suc n)
    H-Level-is-lub = prop-instance $ Iso→is-hlevel 1 eqv (hlevel 1)

  lub-unique : ∀ {ℓᵢ} {I : Type ℓᵢ} {F : I → P.Ob}
             → is-prop (Σ P.Ob (is-lub F))
  lub-unique (lub , is) (lub′ , is′) = Σ-prop-path! $ P.≤-antisym
    (is .least lub′ (is′ .fam≤lub))
    (is′ .least lub (is .fam≤lub))

  record is-join (a b : P.Ob) (lub : P.Ob) : Type (ℓ ⊔ ℓ′) where
    field
      l≤join : a P.≤ lub
      r≤join : b P.≤ lub
      least  : (ub′ : P.Ob) → a P.≤ ub′ → b P.≤ ub′ → lub P.≤ ub′

  open is-join

  private unquoteDecl eqv′ = declare-record-iso eqv′ (quote is-join)

  instance
    H-Level-is-join
      : ∀ {a b lub : P.Ob} {n}
      → H-Level (is-join a b lub) (suc n)
    H-Level-is-join = prop-instance $ Iso→is-hlevel 1 eqv′ (hlevel 1)

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

  open is-iso
  is-join≃is-lub : ∀ {a b lub : P.Ob} → is-equiv (is-join→is-lub {a} {b} {lub})
  is-join≃is-lub = prop-ext! _ is-lub→is-join .snd

  join-unique : ∀ {a b} → is-prop (Σ P.Ob (is-join a b))
  join-unique {a} {b} = transport
    (λ i → is-prop (Σ P.Ob λ x → ua (_ , is-join≃is-lub {a} {b} {x}) (~ i)))
    lub-unique
```
