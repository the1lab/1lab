```agda
open import Cat.Prelude

open import Data.Bool

open import Order.Base

import Order.Reasoning as Poset

module Order.Diagram.Glb where
```

# Greatest lower bounds

A **glb** $g$ (short for **greatest lower bound**) for a family of
elements $(a_i)_{i : I}$ is, as the name implies, a greatest element
among the lower bounds of the $a_i$. Being a lower bound means that we
have $g \le a_i$ for all $i : I$; Being the _greatest_ lower bound means
that if we're given some other $m$ satisfying $m \le a_i$ (for each
$i$), then we have $m \le u$.

A more common _word_ to use for "greatest lower bound" is "meet". But
since "meet" is a fairly uninformative name, and "glb" (pronounced
"glib") is just plain fun to say, we stick with the non-word for the
indexed concept. However, if we're talking about the glb of a binary
family, _then_ we use the word "meet". The distinction here is entirely
artificial, and it's just because we can't reuse the identifier
`is-glb`{.Agda} for these two slightly different cases. Summing up: to
us, a meet is a glb of two elements.

```agda
module _ {ℓ ℓ′} (P : Poset ℓ ℓ′) where
  private module P = Poset P

  record is-glb {ℓᵢ} {I : Type ℓᵢ} (F : I → P.Ob) (glb : P.Ob)
          : Type (ℓ ⊔ ℓ′ ⊔ ℓᵢ) where
    field
      glb≤fam  : ∀ i → glb P.≤ F i
      greatest : (lb′ : P.Ob) → (∀ i → lb′ P.≤ F i) → lb′ P.≤ glb

  open is-glb

  private unquoteDecl eqv = declare-record-iso eqv (quote is-glb)

  instance
    H-Level-is-glb
      : ∀ {ℓᵢ} {I : Type ℓᵢ} {F : I → P.Ob} {glb : P.Ob} {n}
      → H-Level (is-glb F glb) (suc n)
    H-Level-is-glb = prop-instance $ Iso→is-hlevel 1 eqv (hlevel 1)

  glb-unique : ∀ {ℓᵢ} {I : Type ℓᵢ} {F : I → P.Ob}
             → is-prop (Σ P.Ob (is-glb F))
  glb-unique (glb , is) (glb′ , is′) = Σ-prop-path! $ P.≤-antisym
    (is′ .greatest glb (is .glb≤fam))
    (is .greatest glb′ (is′ .glb≤fam))

  record is-meet (a b : P.Ob) (glb : P.Ob) : Type (ℓ ⊔ ℓ′) where
    field
      meet≤l   : glb P.≤ a
      meet≤r   : glb P.≤ b
      greatest : (lb′ : P.Ob) → lb′ P.≤ a → lb′ P.≤ b → lb′ P.≤ glb

  open is-meet

  private unquoteDecl eqv′ = declare-record-iso eqv′ (quote is-meet)

  instance
    H-Level-is-meet
      : ∀ {a b glb : P.Ob} {n}
      → H-Level (is-meet a b glb) (suc n)
    H-Level-is-meet = prop-instance $ Iso→is-hlevel 1 eqv′ (hlevel 1)

  is-meet→is-glb : ∀ {a b glb} → is-meet a b glb → is-glb (if_then a else b) glb
  is-meet→is-glb meet .glb≤fam true = meet .meet≤l
  is-meet→is-glb meet .glb≤fam false = meet .meet≤r
  is-meet→is-glb meet .greatest glb′ x = meet .greatest glb′ (x true) (x false)

  is-glb→is-meet : ∀ {F : Bool → P.Ob} {glb} → is-glb F glb → is-meet (F true) (F false) glb
  is-glb→is-meet glb .meet≤l = glb .glb≤fam true
  is-glb→is-meet glb .meet≤r = glb .glb≤fam false
  is-glb→is-meet glb .greatest lb′ lb′<a lb′<b = glb .greatest lb′ λ where
    true  → lb′<a
    false → lb′<b

  open is-iso
  is-meet≃is-glb : ∀ {a b glb : P.Ob} → is-equiv (is-meet→is-glb {a} {b} {glb})
  is-meet≃is-glb = prop-ext! _ is-glb→is-meet .snd

  meet-unique : ∀ {a b} → is-prop (Σ P.Ob (is-meet a b))
  meet-unique {a} {b} = transport
    (λ i → is-prop (Σ P.Ob λ x → ua (_ , is-meet≃is-glb {a} {b} {x}) (~ i)))
    glb-unique
```
