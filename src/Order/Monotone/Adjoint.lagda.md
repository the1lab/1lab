```agda
open import Cat.Prelude

open import Order.Diagram.Glb
open import Order.Base

import Order.Reasoning as Poset

module Order.Monotone.Adjoint where
```

# Adjunctions in posets

In this module we define a notion of [adjunction] for monotone maps
between posets, restricting the full definition to something a bit
simpler in this special case. Rather than going with the definition in
terms of units and counits, we directly adopt the [hom-isomorphism]
definition of adjunction: $f \dashv g$ is defined to mean $f(a) \le b
\equiv a \le g(b)$.

[adjunction]: Cat.Functor.Adjoint.html
[hom-isomorphism]: Cat.Functor.Adjoint.Hom.html

```agda
module _ {o ℓ o′ ℓ′} {P : Poset o ℓ} {Q : Poset o′ ℓ′} where
  private
    module P = Poset P
    module Q = Poset Q

  record _⊣_ (f : Monotone-map P Q) (g : Monotone-map Q P) : Type (o ⊔ ℓ ⊔ o′ ⊔ ℓ′) where
    no-eta-equality

    field hom-iso : ∀ {a b} → (f .map a Q.≤ b) ≃ (a P.≤ g .map b)

    module hom-iso {a} {b} = Equiv (hom-iso {a} {b})
```

But note that we can, just as in the case for 1-categories, recover the
"unit and counit maps" by plugging the "identity" of each poset into the
equivalence.

```agda
    unit : ∀ {a} → a P.≤ g .map (f .map a)
    unit = hom-iso.to Q.≤-refl

    counit : ∀ {a} → f .map (g .map a) Q.≤ a
    counit = hom-iso.from P.≤-refl
```

<!--
```agda
  unit-counit→adjoint
    : {f : Monotone-map P Q} {g : Monotone-map Q P}
    → (∀ {a} → a P.≤ g .map (f .map a))
    → (∀ {a} → f .map (g .map a) Q.≤ a)
    → f ⊣ g
  unit-counit→adjoint {f = f} {g} η ε ._⊣_.hom-iso = prop-ext!
    (λ e → P.≤-trans η (g .monotone e))
    (λ e → Q.≤-trans (f .monotone e) ε)
```
-->

## The AFT

In the posetal case, the adjoint functor theorem takes a very pleasant
form: if $f : A \to B$ is a monotone map from a complete lattice which
preserves greatest lower bounds, it has a left adjoint. This is unlike
the situation for general 1-categories, because the existence of
non-posetal 1-categories with limits for every diagram is a taboo.

```agda
module
  _ {o ℓ o′ ℓ′} {P : Poset o ℓ} {Q : Poset o′ ℓ′}
    (P-complete : is-complete P)
    (f : Monotone-map P Q)
    (f-preserves
      : ∀ {I : Type o} (F : I → ⌞ P ⌟) {X}
      → is-glb P F X
      → is-glb Q (λ i → f .map (F i)) (f .map X))
    where
```

<!--
```
  open is-glb

  private
    module P = Poset P
    module Pc = Complete P P-complete
    module Q = Poset Q
```
-->

We define the left adjoint by $g(x) = \bigcap_{i : P} x \le f(i)$; Three
steps of calculation show that (a) this is indeed a monotone map and (b)
it's a left adjoint to $f$, which takes two steps.


```agda
  aft→map : Monotone-map Q P
  aft→map .map x = Pc.subset-⋂ λ i → elΩ (x Q.≤ f .map i)
  aft→map .monotone {x} {y} x≤y =
    Pc.subset.glb≤S (λ z → elΩ (x Q.≤ f .map z)) $ □.inc $
    f-preserves fst (P-complete _ .snd) .greatest _ λ i → Q.≤-trans x≤y (out! (i .snd))

  aft→left-adjoint : aft→map ⊣ f
  aft→left-adjoint = unit-counit→adjoint
    (λ {a} → f-preserves fst (P-complete _ .snd) .greatest a λ i → out! (i .snd))
    (λ {a} → Pc.subset.glb≤S (λ z → elΩ _) (inc Q.≤-refl))
```
