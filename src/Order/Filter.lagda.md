---
description: |
  Filters.
---

<!--
```agda
open import Cat.Prelude

open import Data.Fin.Finite

open import Order.Instances.Elements.Covariant
open import Order.Semilattice.Meet
open import Order.Instances.Props
open import Order.Instances.Upper
open import Order.Diagram.Meet
open import Order.Diagram.Glb
open import Order.Diagram.Top
open import Order.Directed
open import Order.Base
```
-->

```agda
module Order.Filter where
```

<!--
```agda
open is-downwards-directed
```
-->

# Filters

:::{.definition #filter}
A subset $F \subseteq P$ is a **filter** when it is upwards closed and [[downwards directed]].
Explicitly:

1. If $x \leq y$ and $x \in F$, then $y \in F$.
2. There [[merely]] exists some $x : P$ with $x \in F$.
3. If $x \in F$ and $y \in F$, then there merely exists some $z \in F$
   with $z \leq x$ and $z \leq y$.

More abstractly, an [[upper set]] $F \subseteq P$ is a filter if its
[[poset of elements|covariant-poset-of-elements]] is [[downwards directed]].
:::

```agda
is-filter : ∀ {o ℓ} {P : Poset o ℓ} → (F : Upper-set P) → Type (o ⊔ ℓ)
is-filter F = is-downwards-directed (∫ F)

record Filter {o ℓ} (P : Poset o ℓ) : Type (o ⊔ ℓ) where
  no-eta-equality
  field
    F : Upper-set P
    has-is-filter : is-filter F

  open Monotone F
    renaming
    ( pres-≤ to F-≤
    )
    public

open Filter
```

<!--
```agda
module _ {o ℓ} {P : Poset o ℓ} where
  open Poset P
  private module ↑P = Poset (Upper-sets P)

  instance
    Membership-Filter : Membership ⌞ P ⌟ (Filter P) lzero
    Membership-Filter = record { _∈_ = λ x F → x ∈ Filter.F F }

    Underlying-Filter : Underlying (Filter P)
    Underlying-Filter = record { ⌞_⌟ = λ F → ∫ₚ F }

    Funlike-Filter : Funlike (Filter P) ⌞ P ⌟ λ _ → Ω
    Funlike-Filter = record { _·_ = λ F x → Filter.F F · x }
```
-->

Intuitively, filters are predicates on $P$ that classify elements
that are "sufficiently large". Upwards closure dictates
that filters recognize increasingly large elements, and directedness
requires that two large elements must contain some large degree of overlap.

We can also turn this thinking on its head, and view of a filter on $P$ as
classifying a potentially non-existent element of $P$ by describing all of the elements
that lie above it. This perspective is highlighted by the following definition.

:::{.definition #principal-filter}
Let $x : P$. The **principal filter** on $x$, denoted $\uparrow x$, consists
of the set $\left\{ a : P \mid x \leq a \right\}$.
:::

```agda
  ↑-is-filter : ∀ x → is-filter (↑ P x)
  ↑-is-filter x .inhab = pure (x , pure ≤-refl)
  ↑-is-filter x .lower-bound (a , x≤a) (b , x≤b) = pure ((x , pure ≤-refl) , □-out! x≤a , □-out! x≤b)

  ↑ᶠ : ⌞ P ⌟ → Filter P
  ↑ᶠ x .Filter.F = ↑ P x
  ↑ᶠ x .Filter.has-is-filter = ↑-is-filter x
```

Principal filters classify the elements of $P$ lower bounded by a bona-fide
element of $P$, but this is not always the case.

## Filters and meets

<!--
```agda
module _ {o ℓ} {P : Poset o ℓ} where
  open Poset P
```
-->

Filters are closed under [[binary meets|meet]] and contain [[top elements]] (if they exist).

```agda
  is-filter→meet-closed
    : {F : Upper-set P} {x y x∧y : ⌞ P ⌟}
    → is-filter F
    → is-meet P x y x∧y
    → x ∈ F → y ∈ F → x∧y ∈ F
  is-filter→meet-closed {F = F} {x = x} {y = y} F-filter x∧y-meet x∈F y∈F =
    case F-filter .lower-bound (x , x∈F) (y , y∈F) of λ where
      z z∈F z≤x z≤y → F .pres-≤ (greatest z z≤x z≤y) z∈F
    where open is-meet x∧y-meet

  is-filter→contains-top
    : {F : Upper-set P} {t : ⌞ P ⌟}
    → is-filter F
    → is-top P t
    → t ∈ F
  is-filter→contains-top {F = F} F-filter t-top =
    case F-filter .inhab of λ where
      x x∈F → F .pres-≤ (t-top x) x∈F
```

In particular, this means that filters are closed under [[finite]] meets.

```agda
  is-filter→finite-glb-closed
    : ∀ {κ} {Ix : Type κ} ⦃ _ : Finite Ix ⦄
    → {F : Upper-set P} {xᵢ : Ix → ⌞ P ⌟} {⋀xᵢ : ⌞ P ⌟}
    → is-filter F
    → is-glb P xᵢ ⋀xᵢ
    → (∀ i → xᵢ i ∈ F) → ⋀xᵢ ∈ F
  is-filter→finite-glb-closed {F = F} {xᵢ = xᵢ} F-filter ⋀xᵢ-glb xᵢ∈F =
    case finite-lower-bound F-filter (λ i → xᵢ i , xᵢ∈F i) of λ where
      z z∈F z≤xᵢ → F .pres-≤ (greatest z z≤xᵢ) z∈F
    where open is-glb ⋀xᵢ-glb
```

This means that filters preserves finite meets when viewed as monotone maps
into the poset of propositions. In particular, this means a filter
$F \subseteq L$ on a [[meet semilattice]] $L$ induces a meet semilattice
homomorphism $F : L \to \Omega$.

<!--
```agda
module _ {o ℓ} {L : Poset o ℓ} (L-slat : is-meet-semilattice L) where
  open Poset L
  open is-meet-semilattice L-slat
  open is-meet-slat-hom

  is-filter→∩-closed
    : {F : Upper-set L} {x y : ⌞ L ⌟}
    → is-filter F
    → x ∈ F → y ∈ F → (x ∩ y) ∈ F
  is-filter→∩-closed {x = x} {y = y} F-filter x∈F y∈F =
    is-filter→meet-closed F-filter (∩-meets x y) x∈F y∈F
```
-->

```agda
  is-filter→is-meet-slat-hom
    : {F : Upper-set L}
    → is-filter F
    → is-meet-slat-hom F L-slat Props-is-meet-slat
  {-# INLINE is-filter→is-meet-slat-hom #-}
  is-filter→is-meet-slat-hom F-filter .∩-≤ x y (x∈F , y∈F) =
    is-filter→∩-closed F-filter x∈F y∈F
  is-filter→is-meet-slat-hom F-filter .top-≤ _ =
    is-filter→contains-top F-filter (Top.has-top has-top)
```

Moreover, every filter on a meet semilattice arises this way.

```agda
  is-meet-slat-hom→is-filter
    : {F : Monotone L Props}
    → is-meet-slat-hom F L-slat Props-is-meet-slat
    → is-filter F
  {-# INLINE is-meet-slat-hom→is-filter #-}
  is-meet-slat-hom→is-filter F-meet-hom = record
    { inhab = inc (top , F-meet-hom .top-≤ tt)
    ; lower-bound = λ (x , x∈F) (y , y∈F) →
      inc ((x ∩ y , F-meet-hom .∩-≤ x y (x∈F , y∈F)) , ∩≤l , ∩≤r)
    }
```

## Filter bases

<!--
```agda
module _ {o ℓ} {P : Poset o ℓ} where
  open Poset P
```
-->

:::{.definition #filter-base}
An $I$-indexed family $x_i : I \to P$ is a **filter base** of a filter
$F \subseteq P$ if:

- $x_i \in F$ for every $i : I$, and
- if $y \in F$ then there [[merely]] exists some $i : I$ such that $x_i \leq y$.
:::


```agda
  record is-filter-base {κ : Level} {Ix : Type κ} (F : Filter P) (xᵢ : Ix → ⌞ P ⌟) : Type (o ⊔ ℓ ⊔ κ) where
    no-eta-equality
    private
      module F = Filter F
    field
      base∈F : ∀ (i : Ix) → xᵢ i ∈ F
      up-closed : ∀ (y : ⌞ P ⌟) → y ∈ F → ∃[ i ∈ Ix ] (xᵢ i ≤ y)
```

More succinctly, $x_i$ is a filter base of $F$ if $F$ is the upwards closure of $x_i$.

```agda
    F-is-up-closure : ∀ y → y ∈ F ≃ (∃[ i ∈ Ix ] (xᵢ i ≤ y))
    F-is-up-closure y = prop-ext! (up-closed y) (rec! λ i xᵢ≤y → F.F-≤ xᵢ≤y (base∈F i))
```

<!--
```agda
  {-# INLINE is-filter-base.constructor #-}
  unquoteDecl H-Level-is-filter-base =
    declare-record-hlevel 1 H-Level-is-filter-base (quote is-filter-base)
```
-->

```agda
  is-up-closure→is-filter-base
    : ∀ {κ} {Ix : Type κ} {F : Filter P}
    → (xᵢ : Ix → ⌞ P ⌟)
    → (∀ y → y ∈ F ≃ (∃[ i ∈ Ix ] (xᵢ i ≤ y)))
    → is-filter-base F xᵢ
  {-# INLINE is-up-closure→is-filter-base #-}
  is-up-closure→is-filter-base xᵢ F-is-up = record
    { base∈F = λ i → F-is-up.from (xᵢ i) (pure (i , ≤-refl))
    ; up-closed = λ y y∈F → F-is-up.to y y∈F
    }
    where
      module F-is-up y = Equiv (F-is-up y)
```

<!--
```agda
  is-up-closure≃is-filter-base
    : ∀ {κ} {Ix : Type κ} {F : Filter P}
    → (xᵢ : Ix → ⌞ P ⌟)
    → (∀ y → y ∈ F ≃ (∃[ i ∈ Ix ] (xᵢ i ≤ y))) ≃ is-filter-base F xᵢ
  is-up-closure≃is-filter-base xᵢ = prop-ext!
      (is-up-closure→is-filter-base xᵢ)
      is-filter-base.F-is-up-closure
```
-->

Every principal filter $\uparrow x$ has a filter base that consists only of $x$.

```agda
  ↑ᶠ-filter-base : ∀ (x : ⌞ P ⌟) → is-filter-base {Ix = ⊤} (↑ᶠ x) (λ _ → x)
  ↑ᶠ-filter-base x .is-filter-base.base∈F _ = inc ≤-refl
  ↑ᶠ-filter-base x .is-filter-base.up-closed = elim! λ y x≤y → inc (tt , x≤y)
```
