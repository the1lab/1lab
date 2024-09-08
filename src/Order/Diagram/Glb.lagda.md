<!--
```agda
open import Cat.Diagram.Terminal
open import Cat.Diagram.Product
open import Cat.Prelude

open import Data.Bool

open import Order.Base
open import Order.Cat

import Order.Reasoning
```
-->

```agda
module Order.Diagram.Glb where
```

<!--
```agda
module _ {o ℓ} (P : Poset o ℓ) where
  open Poset P
```
-->

# Greatest lower bounds {defines="greatest-lower-bound"}

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
  record is-glb {ℓᵢ} {I : Type ℓᵢ} (F : I → Ob) (glb : Ob)
          : Type (o ⊔ ℓ ⊔ ℓᵢ) where
    no-eta-equality
    field
      glb≤fam  : ∀ i → glb ≤ F i
      greatest : (lb' : Ob) → (∀ i → lb' ≤ F i) → lb' ≤ glb

  record Glb {ℓᵢ} {I : Type ℓᵢ} (F : I → Ob) : Type (o ⊔ ℓ ⊔ ℓᵢ) where
    no-eta-equality
    field
      glb : Ob
      has-glb : is-glb F glb
    open is-glb has-glb public
```

<!--
```agda
unquoteDecl H-Level-is-glb = declare-record-hlevel 1 H-Level-is-glb (quote is-glb)

module _ {o ℓ} {P : Poset o ℓ} where
  open Poset P
  open is-glb

  glb-unique
    : ∀ {ℓᵢ} {I : Type ℓᵢ} {F : I → Ob} {x y}
    → is-glb P F x → is-glb P F y
    → x ≡ y
  glb-unique is is' = ≤-antisym
    (is' .greatest _ (is .glb≤fam))
    (is .greatest _ (is' .glb≤fam))

  Glb-is-prop
    : ∀ {ℓᵢ} {I : Type ℓᵢ} {F : I → Ob}
    → is-prop (Glb P F)
  Glb-is-prop p q i .Glb.glb =
    glb-unique (Glb.has-glb p) (Glb.has-glb q) i
  Glb-is-prop {F = F} p q i .Glb.has-glb =
    is-prop→pathp {B = λ i → is-glb P F (glb-unique (Glb.has-glb p) (Glb.has-glb q) i)}
      (λ i → hlevel 1)
      (Glb.has-glb p) (Glb.has-glb q) i

  instance
    H-Level-Glb
      : ∀ {ℓᵢ} {I : Type ℓᵢ} {F : I → Ob} {n}
      → H-Level (Glb P F) (suc n)
    H-Level-Glb = prop-instance Glb-is-prop

  lift-is-glb
    : ∀ {ℓᵢ ℓᵢ'} {I : Type ℓᵢ} {F : I → Ob} {glb}
    → is-glb P F glb → is-glb P (F ⊙ lower {ℓ = ℓᵢ'}) glb
  lift-is-glb is .glb≤fam (lift ix) = is .glb≤fam ix
  lift-is-glb is .greatest ub' le = is .greatest ub' (le ⊙ lift)

  lift-glb
    : ∀ {ℓᵢ ℓᵢ'} {I : Type ℓᵢ} {F : I → Ob}
    → Glb P F → Glb P (F ⊙ lower {ℓ = ℓᵢ'})
  lift-glb glb .Glb.glb = Glb.glb glb
  lift-glb glb .Glb.has-glb = lift-is-glb (Glb.has-glb glb)

  lower-is-glb
    : ∀ {ℓᵢ ℓᵢ'} {I : Type ℓᵢ} {F : I → Ob} {glb}
    → is-glb P (F ⊙ lower {ℓ = ℓᵢ'}) glb → is-glb P F glb
  lower-is-glb is .glb≤fam ix = is .glb≤fam (lift ix)
  lower-is-glb is .greatest ub' le = is .greatest ub' (le ⊙ lower)

  lower-glb
    : ∀ {ℓᵢ ℓᵢ'} {I : Type ℓᵢ} {F : I → Ob}
    → Glb P (F ⊙ lower {ℓ = ℓᵢ'}) → Glb P F
  lower-glb glb .Glb.glb = Glb.glb glb
  lower-glb glb .Glb.has-glb = lower-is-glb (Glb.has-glb glb)
```
-->

<!--
```agda
  module _
    {ℓᵢ ℓᵢ'} {Ix : Type ℓᵢ} {Im : Type ℓᵢ'}
    {f : Ix → Im}
    {F : Im → Ob}
    (surj : is-surjective f)
    where
      cover-preserves-is-glb : ∀ {glb} → is-glb P F glb → is-glb P (F ⊙ f) glb
      cover-preserves-is-glb g .glb≤fam i = g .glb≤fam (f i)
      cover-preserves-is-glb g .greatest lb' le = g .greatest lb' λ i → ∥-∥-out! do
        (i' , p) ← surj i
        pure (≤-trans (le i') (≤-refl' (ap F p)))

      cover-preserves-glb : Glb P F → Glb P (F ⊙ f)
      cover-preserves-glb g .Glb.glb = _
      cover-preserves-glb g .Glb.has-glb = cover-preserves-is-glb (g .Glb.has-glb)

      cover-reflects-is-glb : ∀ {glb} → is-glb P (F ⊙ f) glb → is-glb P F glb
      cover-reflects-is-glb g .glb≤fam i = ∥-∥-out! do
        (y , p) ← surj i
        pure (≤-trans (g .glb≤fam y) (≤-refl' (ap F p)))
      cover-reflects-is-glb g .greatest lb' le = g .greatest lb' λ i → le (f i)

      cover-reflects-glb : Glb P (F ⊙ f) → Glb P F
      cover-reflects-glb g .Glb.glb = _
      cover-reflects-glb g .Glb.has-glb = cover-reflects-is-glb (g .Glb.has-glb)
```
-->
