<!--
```agda
open import Cat.Functor.Subcategory
open import Cat.Prelude

open import Order.Diagram.Lub.Reasoning
open import Order.Instances.Pointwise
open import Order.Semilattice.Join
open import Order.Semilattice.Meet
open import Order.Instances.Props
open import Order.Diagram.Meet
open import Order.Diagram.Lub
open import Order.Diagram.Top
open import Order.Base

import Cat.Reasoning

import Order.Diagram.Meet.Reasoning as Meets
import Order.Reasoning
```
-->

```agda
module Order.Frame where
```

# Frames {defines="frame"}

```agda
record is-frame {o ℓ} (P : Poset o ℓ) : Type (lsuc o ⊔ ℓ) where
  no-eta-equality
  open Order.Reasoning P
  field
    has-meets : Has-meets P
    has-top  : Top P
    has-lubs : ∀ {I : Type o} (k : I → Ob) → Lub P k

  module has-lubs {I} {k : I → Ob} = Lub (has-lubs k)

  open Meets has-meets public
  open Top has-top using (top; !) public
  open Lubs P has-lubs public

  field
    ⋃-distribl : ∀ {I} x (f : I → Ob) → x ∩ ⋃ f ≡ ⋃ λ i → x ∩ f i

  has-meet-slat : is-meet-semilattice P
  has-meet-slat .is-meet-semilattice.has-meets = has-meets
  has-meet-slat .is-meet-semilattice.has-top = has-top

  has-join-slat : is-join-semilattice P
  has-join-slat .is-join-semilattice.has-joins = has-joins
  has-join-slat .is-join-semilattice.has-bottom = has-bottom
```

<!--
```agda
private
  variable
    o ℓ o' ℓ' : Level
    P Q R : Poset o ℓ

is-frame-is-prop : is-prop (is-frame P)
is-frame-is-prop {P = P} = Iso→is-hlevel 1 eqv hlevel! where
  open Order.Diagram.Lub P using (H-Level-Lub)
  open Order.Diagram.Meet P using (H-Level-Meet)
  open Order.Diagram.Top P using (H-Level-Top)
  unquoteDecl eqv = declare-record-iso eqv (quote is-frame)

instance
  H-Level-is-frame : ∀ {n} → H-Level (is-frame P) (suc n)
  H-Level-is-frame = prop-instance is-frame-is-prop
```
-->

```agda
record
  is-frame-hom
    {P : Poset o ℓ} {Q : Poset o ℓ'}
    (f : Monotone P Q)
    (P-frame : is-frame P)
    (Q-frame : is-frame Q)
    : Type (lsuc o ⊔ ℓ') where
  private
    module P = Poset P
    module Pᶠ = is-frame P-frame
    module Q = Order.Reasoning Q
    module Qᶠ = is-frame Q-frame
    open is-lub
  field
    ∩-≤ : ∀ x y → (f # x) Qᶠ.∩ (f # y) Q.≤ f # (x Pᶠ.∩ y)
    top-≤ : Qᶠ.top Q.≤ f # Pᶠ.top
    ⋃-≤ : ∀ {I : Type o} (k : I → ⌞ P ⌟) → (f # Pᶠ.⋃ k) Q.≤ Qᶠ.⋃ (apply f ⊙ k)

  has-meet-slat-hom : is-meet-slat-hom f Pᶠ.has-meet-slat Qᶠ.has-meet-slat
  has-meet-slat-hom .is-meet-slat-hom.∩-≤ = ∩-≤
  has-meet-slat-hom .is-meet-slat-hom.top-≤ = top-≤

  open is-meet-slat-hom has-meet-slat-hom hiding (∩-≤; top-≤) public

  pres-⋃ : ∀ {I : Type o} (k : I → ⌞ P ⌟) → (f # Pᶠ.⋃ k) ≡ Qᶠ.⋃ (apply f ⊙ k)
  pres-⋃ k =
    Q.≤-antisym
      (⋃-≤ k)
      (Qᶠ.⋃-universal _ (λ i → f .pres-≤ (Pᶠ.⋃-inj i)))

  pres-lubs
    : ∀ {I : Type o} {k : I → ⌞ P ⌟} {l}
    → is-lub P k l
    → is-lub Q (apply f ⊙ k) (f # l)
  pres-lubs {k = k} {l = l} l-lub .fam≤lub i = f .pres-≤ (l-lub .fam≤lub i)
  pres-lubs {k = k} {l = l} l-lub .least ub p =
    f # l              Q.≤⟨ f .pres-≤ (l-lub .least _ Pᶠ.⋃-inj) ⟩
    f # Pᶠ.⋃ k         Q.≤⟨ ⋃-≤ k ⟩
    Qᶠ.⋃ (apply f ⊙ k) Q.≤⟨ Qᶠ.⋃-universal ub p ⟩
    ub                 Q.≤∎

  opaque
    unfolding Lubs.has-joins Lubs.has-bottom

    has-join-slat-hom : is-join-slat-hom f Pᶠ.has-join-slat Qᶠ.has-join-slat
    has-join-slat-hom .is-join-slat-hom.∪-≤ x y =
      Q.≤-trans (⋃-≤ _) $ Qᶠ.⋃-universal _ λ where
        (lift true) → Qᶠ.⋃-inj (lift true)
        (lift false) → Qᶠ.⋃-inj (lift false)
    has-join-slat-hom .is-join-slat-hom.bot-≤ =
      Q.≤-trans (⋃-≤ _) (Qᶠ.⋃-universal _ (λ ()))

  open is-join-slat-hom has-join-slat-hom public

open is-frame-hom
```

<!--
```agda
is-frame-hom-is-prop
  : ∀ {f : Monotone P Q} {P-frame Q-frame}
  → is-prop (is-frame-hom f P-frame Q-frame)
is-frame-hom-is-prop = Iso→is-hlevel 1 eqv hlevel!
  where unquoteDecl eqv = declare-record-iso eqv (quote is-frame-hom)

instance
  H-Level-is-frame-hom
    : ∀ {f : Monotone P Q} {P-frame Q-frame}
    → ∀ {n} → H-Level (is-frame-hom f P-frame Q-frame) (suc n)
  H-Level-is-frame-hom = prop-instance is-frame-hom-is-prop
```
-->

```agda
id-frame-hom
  : ∀ (Pᶠ : is-frame P)
  → is-frame-hom idₘ Pᶠ Pᶠ
id-frame-hom {P = P} Pᶠ .∩-≤ x y =
  Poset.≤-refl P
id-frame-hom {P = P} Pᶠ .top-≤ =
  Poset.≤-refl P
id-frame-hom {P = P} Pᶠ .⋃-≤ k =
  Poset.≤-refl P

∘-frame-hom
  : ∀ {Pₗ Qₗ Rₗ} {f : Monotone Q R} {g : Monotone P Q}
  → is-frame-hom f Qₗ Rₗ
  → is-frame-hom g Pₗ Qₗ
  → is-frame-hom (f ∘ₘ g) Pₗ Rₗ
∘-frame-hom {R = R} {f = f} {g = g} f-pres g-pres .∩-≤ x y =
  R .Poset.≤-trans (f-pres .∩-≤ (g # x) (g # y)) (f .pres-≤ (g-pres .∩-≤ x y))
∘-frame-hom {R = R} {f = f} {g = g} f-pres g-pres .top-≤ =
  R .Poset.≤-trans (f-pres .top-≤) (f .pres-≤ (g-pres .top-≤))
∘-frame-hom {R = R} {f = f} {g = g} f-pres g-pres .⋃-≤ k =
  R .Poset.≤-trans (f .pres-≤ (g-pres .⋃-≤ k)) (f-pres .⋃-≤ (λ i → g # k i))

Frame-subcat : ∀ o ℓ → Subcat (Posets o ℓ) _ _
Frame-subcat o ℓ .Subcat.is-ob = is-frame
Frame-subcat o ℓ .Subcat.is-hom = is-frame-hom
Frame-subcat o ℓ .Subcat.is-hom-prop = hlevel!
Frame-subcat o ℓ .Subcat.is-hom-id = id-frame-hom
Frame-subcat o ℓ .Subcat.is-hom-∘ = ∘-frame-hom

Frames : ∀ o ℓ → Precategory _ _
Frames o ℓ = Subcategory (Frame-subcat o ℓ)

module Frames {o} {ℓ} = Cat.Reasoning (Frames o ℓ)

Frame : ∀ o ℓ → Type _
Frame o ℓ = Frames.Ob {o} {ℓ}
```

<!--
```agda
module Frame {o ℓ} (F : Frame o ℓ) where
  open Order.Reasoning (F .fst) public
  open is-frame (F .snd) public

  po : Poset o ℓ
  po = F .fst
```
-->

# Power frames

A canonical source of frames are power sets: The power set of any type
is a frame, because it is a complete lattice satisfying the infinite
distributive law; This can be seen by some computation, as is done
below.

```agda
open is-frame
open is-meet-semilattice

Power-frame : ∀ {ℓ} (A : Type ℓ) → Frame ℓ ℓ
Power-frame {ℓ = ℓ} A .fst = Subsets A
Power-frame A .snd .has-meets =
  Pointwise-has-meets (λ _ → Props-has-meets)
Power-frame A .snd .has-top =
  Pointwise-has-top (λ _ → Props-has-top)
Power-frame A .snd .has-lubs =
  Pointwise-has-lubs (λ _ → Props-has-lubs)
Power-frame A .snd .⋃-distribl x f = funext λ i → Ω-ua
    (λ (x , i) → □-map (λ (y , z) → _ , x , z) i)
    (λ r → □-rec! (λ { (x , y , z) → y , inc (_ , z) }) r)
```
