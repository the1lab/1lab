```agda
open import Order.Base
open import Cat.Prelude

import Order.Reasoning as Pr

module Order.Displayed where
```

# Displayed posets

As a special case of [displayed categories], we can construct displayed
_posets_: a poset $P$ displayed over $A$, written $P \liesover A$, is a
type-theoretic repackaging --- so that fibrewise information is easier
to recover --- of the data of a poset $P$ and a monotone map $P \to A$.

[displayed categories]: Cat.Displayed.Base.html

```agda
record Displayed {ℓₒ ℓᵣ} ℓ ℓ′ (P : Poset ℓₒ ℓᵣ) : Type (lsuc (ℓ ⊔ ℓ′) ⊔ ℓₒ ⊔ ℓᵣ) where
  no-eta-equality

  private module P = Pr P

  field
    Ob[_]   : P.Ob → Type ℓ
    Rel[_]  : ∀ {x y} → x P.≤ y → Ob[ x ] → Ob[ y ] → Type ℓ′
    ≤-refl′ : ∀ {x} {x′ : Ob[ x ]} → Rel[ P.≤-refl ] x′ x′
    ≤-thin′ : ∀ {x y} (f : x P.≤ y) {x′ y′} → is-prop (Rel[ f ] x′ y′)
    ≤-trans′
      : ∀ {x y z} {x′ : Ob[ x ]} {y′ : Ob[ y ]} {z′ : Ob[ z ]}
      → {f : x P.≤ y} {g : y P.≤ z}
      → Rel[ f ] x′ y′ → Rel[ g ] y′ z′
      → Rel[ P.≤-trans f g ] x′ z′
    ≤-antisym′
      : ∀ {x} {x′ y′ : Ob[ x ]}
      → Rel[ P.≤-refl ] x′ y′ → Rel[ P.≤-refl ] y′ x′ → x′ ≡ y′
```

<!--
```agda
  ≤-antisym-over
    : ∀ {x y} {f : x P.≤ y} {g : y P.≤ x} {x′ y′}
    → Rel[ f ] x′ y′ → Rel[ g ] y′ x′
    → PathP (λ i → Ob[ P.≤-antisym f g i ]) x′ y′
  ≤-antisym-over {x = x} {f = f} {g} {x′} =
    transport
      (λ i → {f : x P.≤ p i} {g : p i P.≤ x} {y′ : Ob[ p i ]}
           → Rel[ f ] x′ y′ → Rel[ g ] y′ x′
           → PathP (λ j → Ob[ P.≤-antisym f g j ]) x′ y′)
      λ r s → transport
        (λ i → {f g : x P.≤ x} {y′ : Ob[ x ]}
             → Rel[ P.≤-thin P.≤-refl f i ] x′ y′ → Rel[ P.≤-thin P.≤-refl g i ] y′ x′
             → PathP (λ j → Ob[ P.has-is-set _ _ refl (P.≤-antisym f g) i j ]) x′ y′)
        ≤-antisym′ r s
    where p = P.≤-antisym f g
```
-->

Analogously to a displayed category, where we can take pairs of an
object $x$ and an object $x'$ over $x$ to make a _new_ category (the
total space $\int P$), we can take total spaces of displayed _posets_ to
make a new poset.

```agda
∫ : ∀ {ℓ ℓ′ ℓₒ ℓᵣ} {P : Poset ℓₒ ℓᵣ} → Displayed ℓ ℓ′ P → Poset _ _
∫ {P = P} D = to-poset (Σ ⌞ P ⌟ D.Ob[_]) mk-∫ where
  module D = Displayed D
  module P = Pr P
  mk-∫ : make-poset _ _
  mk-∫ .make-poset.rel (x , x′) (y , y′) = Σ (x P.≤ y) λ f → D.Rel[ f ] x′ y′
  mk-∫ .make-poset.id = P.≤-refl , D.≤-refl′
  mk-∫ .make-poset.thin = Σ-is-hlevel 1 P.≤-thin λ f → D.≤-thin′ f
  mk-∫ .make-poset.trans (p , p′) (q , q′) = P.≤-trans p q , D.≤-trans′ p′ q′
  mk-∫ .make-poset.antisym (p , p′) (q , q′) =
    Σ-pathp (P.≤-antisym p q) (D.≤-antisym-over p′ q′)

open Displayed
```

A special case of displayed posets are sub-partial orders, or, (ab)using
categorical terminology, _full subposets_: These are (the total spaces)
that result from attaching a proposition to the objects, and leaving the
order relation alone.

```agda
Full-subposet′
  : ∀ {ℓₒ ℓᵣ ℓ} (P : Poset ℓₒ ℓᵣ) (S : ⌞ P ⌟ → Prop ℓ)
  → Displayed ℓ lzero P
Full-subposet′ P S .Ob[_] x = ∣ S x ∣
Full-subposet′ P S .Rel[_] f x y = ⊤
Full-subposet′ P S .≤-refl′ = tt
Full-subposet′ P S .≤-thin′ f x y = refl
Full-subposet′ P S .≤-trans′ _ _ = tt
Full-subposet′ P S .≤-antisym′ _ _ = is-prop→pathp (λ i → S _ .is-tr) _ _

Full-subposet
  : ∀ {ℓₒ ℓᵣ ℓ} (P : Poset ℓₒ ℓᵣ) (S : ⌞ P ⌟ → Prop ℓ)
  → Poset (ℓₒ ⊔ ℓ) ℓᵣ
Full-subposet P S = ∫ (Full-subposet′ P S)
```
