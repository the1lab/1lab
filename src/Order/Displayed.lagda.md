<!--
```agda
open import Cat.Prelude

open import Order.Base

import Order.Reasoning as Pr
```
-->

```agda
module Order.Displayed where
```

# Displayed posets {defines="displayed-order"}

As a special case of [[displayed categories]], we can construct
displayed [[_posets_]]: a poset $P$ displayed over $A$, written $P
\liesover A$, is a type-theoretic repackaging --- so that fibrewise
information is easier to recover --- of the data of a poset $P$ and a
monotone map $P \to A$.

```agda
record Displayed {ℓₒ ℓᵣ} ℓ ℓ' (P : Poset ℓₒ ℓᵣ) : Type (lsuc (ℓ ⊔ ℓ') ⊔ ℓₒ ⊔ ℓᵣ) where
  no-eta-equality

  private module P = Pr P

  field
    Ob[_]   : P.Ob → Type ℓ
    Rel[_]  : ∀ {x y} → x P.≤ y → Ob[ x ] → Ob[ y ] → Type ℓ'
    ≤-refl' : ∀ {x} {x' : Ob[ x ]} → Rel[ P.≤-refl ] x' x'
    ≤-thin' : ∀ {x y} (f : x P.≤ y) {x' y'} → is-prop (Rel[ f ] x' y')
    ≤-trans'
      : ∀ {x y z} {x' : Ob[ x ]} {y' : Ob[ y ]} {z' : Ob[ z ]}
      → {f : x P.≤ y} {g : y P.≤ z}
      → Rel[ f ] x' y' → Rel[ g ] y' z'
      → Rel[ P.≤-trans f g ] x' z'
    ≤-antisym'
      : ∀ {x} {x' y' : Ob[ x ]}
      → Rel[ P.≤-refl ] x' y' → Rel[ P.≤-refl ] y' x' → x' ≡ y'
```

<!--
```agda
  ≤-antisym-over
    : ∀ {x y} {f : x P.≤ y} {g : y P.≤ x} {x' y'}
    → Rel[ f ] x' y' → Rel[ g ] y' x'
    → PathP (λ i → Ob[ P.≤-antisym f g i ]) x' y'
  ≤-antisym-over {x = x} {f = f} {g} {x'} =
    transport
      (λ i → {f : x P.≤ p i} {g : p i P.≤ x} {y' : Ob[ p i ]}
           → Rel[ f ] x' y' → Rel[ g ] y' x'
           → PathP (λ j → Ob[ P.≤-antisym f g j ]) x' y')
      λ r s → transport
        (λ i → {f g : x P.≤ x} {y' : Ob[ x ]}
             → Rel[ P.≤-thin P.≤-refl f i ] x' y' → Rel[ P.≤-thin P.≤-refl g i ] y' x'
             → PathP (λ j → Ob[ P.Ob-is-set _ _ refl (P.≤-antisym f g) i j ]) x' y')
        ≤-antisym' r s
    where p = P.≤-antisym f g
```
-->

Analogously to a displayed category, where we can take pairs of an
object $x$ and an object $x'$ over $x$ to make a _new_ category (the
total space $\int P$), we can take total spaces of displayed _posets_ to
make a new poset.

```agda
∫ : ∀ {ℓ ℓ' ℓₒ ℓᵣ} {P : Poset ℓₒ ℓᵣ} → Displayed ℓ ℓ' P → Poset _ _
∫ {P = P} D = po where
  module D = Displayed D
  module P = Pr P

  po : Poset _ _
  po .Poset.Ob = Σ ⌞ P ⌟ D.Ob[_]
  po .Poset._≤_ (x , x') (y , y') = Σ (x P.≤ y) λ f → D.Rel[ f ] x' y'
  po .Poset.≤-thin = Σ-is-hlevel 1 P.≤-thin λ f → D.≤-thin' f
  po .Poset.≤-refl = P.≤-refl , D.≤-refl'
  po .Poset.≤-trans (p , p') (q , q') = P.≤-trans p q , D.≤-trans' p' q'
  po .Poset.≤-antisym (p , p') (q , q') =
    Σ-pathp (P.≤-antisym p q) (D.≤-antisym-over p' q')

open Displayed
```
