<!--
```agda
open import 1Lab.Reflection.Record
open import 1Lab.Prelude

open import Data.Wellfounded.Properties hiding (<-wf)
open import Data.Wellfounded.Base

open import Order.Instances.Nat
open import Order.Univalent using (Poset-path)
open import Order.Subposet
open import Order.Base using (Poset)

import 1Lab.Reflection as Reflection

import Data.Nat.Order as Nat
import Data.Nat.Base as Nat
```
-->

```agda
module Order.Ordinal.Base where
```

# Ordinals {defines="well-order ordinal"}

An **ordinal** captures the concept of a [[well-founded]] order.
Such an order is necessarily a *strict* order (like `_<_`, not `_≤_`),
since a well-founded relation cannot be reflexive.

The conditions for a well-order an be expressed fairly concisely.
A relation `_<_ : X → X → Type` is a well order
if all of the following hold:

* It is propositional.

* It is well-founded.

* It is transitive.

* Whenever `{z | z < x} ≡ {z | z < y}`, we have `x ≡ y`.

Every ordinal is in fact a poset,
where `x ≤ y` iff `∀ {z} → z < x → z < y`.
We choose to use a somewhat redundant definition of ordinal,
where this poset is part of the *structure*,
since it often lines up with a preexisting order.

```agda
record Ordinal (ℓ : Level) : Type (lsuc ℓ) where
  no-eta-equality
  field
    poset : Poset ℓ ℓ
  open Poset poset public
  field
    _<_ : Ob → Ob → Type ℓ
    <-thin : ∀ {x y} → is-prop (x < y)
    <-wf : Wf _<_
    <→≤ : ∀ {x y} → x < y → x ≤ y
    <→≤→< : ∀ {x y z} → x < y → y ≤ z → x < z
    [<→<]→≤ : ∀ {x y} → (∀ {z} → z < x → z < y) → (x ≤ y)
  <-trans : ∀ {x y z} → x < y → y < z → x < z
  <-trans x<y y<z = <→≤→< x<y (<→≤ y<z)
```

<!--
```agda
  <-irrefl : ∀ {x} → ¬ (x < x)
  <-irrefl {x} x<x = go (<-wf x) where
    go : ¬ Acc _<_ x
    go (acc h) = go (h x x<x)

  <-asym : ∀ {x y} → x < y → y < x → ⊥
  <-asym x<y y<x = <-irrefl (<-trans x<y y<x)

private variable
  ℓ ℓ₁ ℓ₂ ℓ₃ : Level


module _ where
  instance
    Underlying-Ordinal : Underlying (Ordinal ℓ)
    Underlying-Ordinal = record { ⌞_⌟ = Ordinal.Ob }

    open Reflection
    open hlevel-projection
    open hlevel-projection
    Ordinal-<-hlevel-proj : hlevel-projection (quote Ordinal._<_)
    Ordinal-<-hlevel-proj .has-level   = quote Ordinal.<-thin
    Ordinal-<-hlevel-proj .get-level _ = pure (lit (nat 1))
    Ordinal-<-hlevel-proj .get-argument (_ ∷ arg _ t ∷ _) = pure t
    Ordinal-<-hlevel-proj .get-argument _                     = typeError []
```
-->

For example, the ordinal `ω` is given by the natural numbers,
under their standard ordering.

```agda
ω : Ordinal lzero
ω = record where
  poset = Nat-poset
  _<_ = Nat._<_
  <-thin = Nat.≤-is-prop
  <→≤ = Nat.<-weaken
  <→≤→< = Nat.≤-trans
  [<→<]→≤ {x} {y} h =
    let
      h' : {z : Nat} → z Nat.≤ x → z Nat.≤ y
      h' = λ { {zero} _ → 0≤x; {suc z} → h {z} }
    in h' Nat.≤-refl
  <-wf = Data.Wellfounded.Properties.<-wf
```

As mentioned above, this representation is rather redundant.
We confirm that ordinals are determined
by their underlying type and strict order,
and can be constructed from the same.

```agda
record _≃ₒ_ (α : Ordinal ℓ₁) (β : Ordinal ℓ₂) : Type (ℓ₁ ⊔ ℓ₂) where
  field
    equiv : ⌞ α ⌟ ≃ ⌞ β ⌟
    pres-< : ∀ {x y} → Ordinal._<_ α x y ≃ Ordinal._<_ β (equiv · x) (equiv · y)
```
<!--
```agda
instance
  Funlike-≃ₒ : {α : Ordinal ℓ₁} {β : Ordinal ℓ₂} → Funlike (α ≃ₒ β) ⌞ α ⌟ λ _ → ⌞ β ⌟
  Funlike-≃ₒ = record { _·_ = fst ∘ _≃ₒ_.equiv }
```
-->
```agda
≃ₒ→≡ : {α β : Ordinal ℓ} → α ≃ₒ β → α ≡ β
≃ₒ→≡ {ℓ} {α} {β} e = p where
```
<details>
<summary>Long proof.</summary>
```agda
  module α = Ordinal α
  module β = Ordinal β
  open _≃ₒ_ e
  p₀ : ⌞ α ⌟ ≡ ⌞ β ⌟
  p₀ = ua equiv

  p₁ : PathP (λ i → p₀ i → p₀ i → Type ℓ) α._<_ β._<_
  p₁ = ua→ λ x → ua→ λ y → ua pres-<

  p₂ : PathP
    (λ i → (x y : p₀ i) →
       Σ (Type ℓ) λ le → (∀ {z : p₀ i} → p₁ i z x → p₁ i z y) ≃ le)
    (λ x y → x α.≤ y , prop-ext (hlevel 1) (hlevel 1)
      α.[<→<]→≤ (λ h₁ h₂ → α.<→≤→< h₂ h₁))
    (λ x y → x β.≤ y , prop-ext (hlevel 1) (hlevel 1)
      β.[<→<]→≤ (λ h₁ h₂ → β.<→≤→< h₂ h₁))
  p₂ = is-prop→pathp (λ i →
    is-contr→is-prop $ Π-is-hlevel 0 λ _ → Π-is-hlevel 0 λ _ →
    is-contr-ΣR univalence-identity-system) _ _

  p₃ : PathP (λ i → ∀ {x y} → is-prop (fst (p₂ i x y))) α.≤-thin β.≤-thin
  p₃ = is-prop→pathp (λ _ → hlevel 1) _ _

  p₄ : PathP (λ i → ∀ {x} → fst (p₂ i x x)) α.≤-refl β.≤-refl
  p₄ = is-prop→pathp (λ i → Π-is-hlevel' 1 λ x → p₃ i {x} {x}) _ _

  p₅ : PathP (λ i → ∀ {x y z} → fst (p₂ i x y) → fst (p₂ i y z) → fst (p₂ i x z))
    α.≤-trans β.≤-trans
  p₅ = is-prop→pathp (λ i →
    Π-is-hlevel' 1 λ x → Π-is-hlevel' 1 λ y → Π-is-hlevel' 1 λ z →
    Π-is-hlevel 1 λ _ → Π-is-hlevel 1 λ _ → p₃ i {x} {z}) _ _

  p₆ : PathP (λ i → ∀ {x y} → fst (p₂ i x y) → fst (p₂ i y x) → x ≡ y)
    α.≤-antisym β.≤-antisym
  p₆ = is-prop-i0→pathp (
    Π-is-hlevel' 1 λ x → Π-is-hlevel' 1 λ y →
    Π-is-hlevel 1 λ _ → Π-is-hlevel 1 λ _ → α.Ob-is-set x y) _ _

  p₇ : PathP (λ i → ∀ {x y} → is-prop (p₁ i x y)) α.<-thin β.<-thin
  p₇ = is-prop→pathp (λ _ → hlevel 1) _ _

  p₈ : PathP (λ i → ∀ {x y} → p₁ i x y → fst (p₂ i x y)) α.<→≤ β.<→≤
  p₈ = is-prop→pathp (λ i →
    Π-is-hlevel' 1 λ x → Π-is-hlevel' 1 λ y → Π-is-hlevel 1 λ _ → p₃ i {x} {y}) _ _

  p₉ : PathP (λ i → Wf (p₁ i)) α.<-wf β.<-wf
  p₉ = is-prop→pathp (λ _ → Π-is-hlevel 1 Acc-is-prop) _ _

  p : α ≡ β
  p i .Ordinal.poset .Poset.Ob = p₀ i
  p i .Ordinal.poset .Poset._≤_ x y = fst (p₂ i x y)
  p i .Ordinal.poset .Poset.≤-thin {x} {y} = p₃ i {x} {y}
  p i .Ordinal.poset .Poset.≤-refl {x} = p₄ i {x}
  p i .Ordinal.poset .Poset.≤-trans {x} {y} {z} = p₅ i {x} {y} {z}
  p i .Ordinal.poset .Poset.≤-antisym {x} {y} = p₆ i {x} {y}
  p i .Ordinal._<_ = p₁ i
  p i .Ordinal.<-thin {x} {y} = p₇ i {x} {y}
  p i .Ordinal.<→≤ {x} {y} = p₈ i {x} {y}
  p i .Ordinal.<→≤→< {z} {x} {y} h₁ h₂ = Equiv.from (snd (p₂ i x y)) h₂ {z} h₁
  p i .Ordinal.[<→<]→≤ {x} {y} = Equiv.to (snd (p₂ i x y))
  p i .Ordinal.<-wf = p₉ i
```
</details>
```agda
record make-ordinal (ℓ : Level) : Type (lsuc ℓ) where
  no-eta-equality
  field
    Ob : Type ℓ
    _<_ : Ob → Ob → Type ℓ
    <-thin : ∀ {x y} → is-prop (x < y)
    <-wf : Wf _<_
    <-trans : ∀ {x y z} → x < y → y < z → x < z
    <-extensional : ∀ {x y} → (∀ {z} → (z < x → z < y) × (z < y → z < x)) → x ≡ y

  to-ordinal : Ordinal ℓ
  to-ordinal = record where
    poset = record where
      Ob = Ob
      _≤_ x y = ∀ {z} → z < x → z < y
      ≤-thin = Π-is-hlevel' 1 λ _ → Π-is-hlevel 1 λ _ → <-thin
      ≤-refl = id
      ≤-trans h₁ h₂ = h₂ ∘ h₁
      ≤-antisym h₁ h₂ = <-extensional (h₁ , h₂)
    _<_ = _<_
    <-thin = <-thin
    <→≤ x<y z<x = <-trans z<x x<y
    <→≤→< x<y y≤z = y≤z x<y
    [<→<]→≤ = id
    <-wf = <-wf
```

The `_≃ₒ_` relation in fact defines an identity system,
but we'll prove that later.
For now, we show it's reflexive, symmetric, and transitive.

```agda
≃ₒ-refl : {α : Ordinal ℓ} → α ≃ₒ α
≃ₒ-refl = record { equiv = id≃ ; pres-< = id≃ }

≃ₒ-trans : {α : Ordinal ℓ₁} {β : Ordinal ℓ₂} {γ : Ordinal ℓ₃}
  → α ≃ₒ β → β ≃ₒ γ → α ≃ₒ γ
≃ₒ-trans e₁ e₂ =
  let module e₁ = _≃ₒ_ e₁; module e₂ = _≃ₒ_ e₂
  in record { equiv = e₁.equiv ∙e e₂.equiv ; pres-< = e₁.pres-< ∙e e₂.pres-< }

≃ₒ-sym : {α : Ordinal ℓ₁} {β : Ordinal ℓ₂} → α ≃ₒ β → β ≃ₒ α
≃ₒ-sym {_} {_} {α} {β} e =
  let
    open _≃ₒ_ e
    equiv' = equiv e⁻¹
    counit = equiv→counit (snd equiv)
  in record {
    equiv = equiv';
    pres-< = λ {x} {y} → transport
      (λ i →
        Ordinal._<_ β (counit x i) (counit y i) ≃
        Ordinal._<_ α (fst equiv' x) (fst equiv' y))
    (pres-< {equiv' · x} {equiv' · y} e⁻¹)
  }
```

## Subordinals

Given any element of an ordinal,
the elements below it form an ordinal of their own.

```agda
module _ (α : Ordinal ℓ) (a : ⌞ α ⌟) where
  open Ordinal α
  Subordinal : Ordinal ℓ
  Subordinal .Ordinal.poset = Subposet poset λ x → el (x < a) <-thin
  Subordinal .Ordinal._<_ (x , _) (y , _) = x < y
  Subordinal .Ordinal.<-thin = <-thin
  Subordinal .Ordinal.<→≤ = <→≤
  Subordinal .Ordinal.<→≤→< = <→≤→<
  Subordinal .Ordinal.[<→<]→≤ {x , x<a} {y , y<a} h =
    [<→<]→≤ (λ {z} z<x → h {z , <-trans z<x x<a} z<x)
  Subordinal .Ordinal.<-wf (x , x<a) = Wf-induction _<_ <-wf
    (λ x → (x<a : x < a)
      → Acc (λ (x y : Σ ⌞ α ⌟ (_< a)) → fst x < fst y) (x , x<a))
    (λ x ih x<a → acc λ (y , y<a) y<x → ih y y<x y<a)
    x x<a
```

## Simulations {defines="simulation"}

The correct notion of map between ordinals, called a **simulation**,
is a strictly monotone function
that induces an equivalence on subordinals.

```agda
record is-simulation (α : Ordinal ℓ₁) (β : Ordinal ℓ₂)
  (f : ⌞ α ⌟ → ⌞ β ⌟) : Type (ℓ₁ ⊔ ℓ₂) where
  no-eta-equality
  private
    module α = Ordinal α
    module β = Ordinal β
  field
    pres-< : ∀ {x y} → x α.< y → f x β.< f y
  segment : (x : α.Ob) → ⌞ Subordinal α x ⌟ → ⌞ Subordinal β (f x) ⌟
  segment x (y , y<x) = f y , pres-< y<x
  field
    segment-is-equiv : ∀ {x} → is-equiv (segment x)
  sim : ∀ {x y} → y β.< f x → ⌞ α ⌟
  sim h = fst (equiv→inverse segment-is-equiv (_ , h))
  simulates : ∀ {x y} → (y<fx : y β.< f x) → f (sim y<fx) ≡ y
  simulates h = ap fst (equiv→counit segment-is-equiv (_ , h))
  sim-< : ∀ {x y} → (y<fx : y β.< f x) → sim y<fx α.< x
  sim-< h = snd (equiv→inverse segment-is-equiv (_ , h))
```

Simulations are injective, and monotone in every reasonable sense.
```agda
  pres-≤ : ∀ {x y} → x α.≤ y → f x β.≤ f y
  pres-≤ {x} {y} x≤y = β.[<→<]→≤ λ {z} z<fx →
    transport (λ i → simulates z<fx i β.< f y) (pres-< (α.<→≤→< (sim-< z<fx) x≤y))

  reflect-≤ : ∀ {x y} → f x β.≤ f y → x α.≤ y
  reflect-≤ = go (α.<-wf _) (α.<-wf _) where
    go : ∀ {x y} → Acc α._<_ x → Acc α._<_ y → f x β.≤ f y → x α.≤ y
    go {x} {y} (acc hx) (acc hy) fx≤fy =
      α.[<→<]→≤ λ {z} z<x →
      let
        fz<fx = pres-< z<x
        fz<fy = β.<→≤→< fz<fx fx≤fy
        w = sim fz<fy
        w<y = sim-< fz<fy
        fw≡fz = simulates fz<fy
        w≤z = go (hy w w<y) (hx z z<x) (β.≤-refl' fw≡fz)
        z≤w = go (hx z z<x) (hy w w<y) (β.≤-refl' (sym fw≡fz))
        w≡z = α.≤-antisym w≤z z≤w
      in transport (λ i → w≡z i α.< y) w<y

  has-injective : injective f
  has-injective p = α.≤-antisym
    (reflect-≤ (β.≤-refl' p))
    (reflect-≤ (β.≤-refl' (sym p)))

  has-is-embedding : is-embedding f
  has-is-embedding = injective→is-embedding β.Ob-is-set f has-injective

  reflect-< : ∀ {x y} → f x β.< f y → x α.< y
  reflect-< {x} {y} fx<fy =
    transport (λ i → has-injective (simulates fx<fy) i α.< y) (sim-< fx<fy)

  Subordinal-≃ : (x : α.Ob) → Subordinal α x ≃ₒ Subordinal β (f x)
  Subordinal-≃ x = record where
    equiv = segment x , segment-is-equiv
    pres-< = prop-ext α.<-thin β.<-thin pres-< reflect-<
```

<!--
```agda
is-simulation-is-prop : ∀ {α β f} → is-prop (is-simulation {ℓ₁} {ℓ₂} α β f)
is-simulation-is-prop {_} {_} {α} {β} {f} s₁ s₂ = p where
  open is-simulation
  p₁ : ∀ {x y} → pres-< s₁ {x} {y} ≡ pres-< s₂ {x} {y}
  p₁ = hlevel 1 _ _
  p₂ : ∀ {x} → PathP
    (λ i → is-equiv {A = ⌞ Subordinal α x ⌟} {B = ⌞ Subordinal β (f x) ⌟}
      λ (y , y<x) → f y , p₁ i y<x)
    (segment-is-equiv s₁ {x})
    (segment-is-equiv s₂ {x})
  p₂ = is-prop→pathp (λ _ → is-equiv-is-prop _) _ _
  p : s₁ ≡ s₂
  p i .pres-< = p₁ i
  p i .segment-is-equiv = p₂ i

instance
  H-Level-is-simulation
    : ∀ {n} {ℓ} {α β : Ordinal ℓ} {f} → H-Level (is-simulation α β f) (suc n)
  H-Level-is-simulation = prop-instance is-simulation-is-prop
```
-->

If a simulation is also an equivalence, it forces the ordinals to be equal.

```agda
is-simulation→is-equiv→≃ₒ : {α : Ordinal ℓ₁} {β : Ordinal ℓ₂} {f : ⌞ α ⌟ → ⌞ β ⌟}
  (sim : is-simulation α β f) (e : is-equiv f) → α ≃ₒ β
is-simulation→is-equiv→≃ₒ _ e ._≃ₒ_.equiv = _ , e
is-simulation→is-equiv→≃ₒ {_} {_} {α} {β} sim _ ._≃ₒ_.pres-< = prop-ext
  (Ordinal.<-thin α) (Ordinal.<-thin β)
  (is-simulation.pres-< sim) (is-simulation.reflect-< sim)
```

## Ordering

Intriguingly, simulations are *unique*.

```agda
simulation-unique : {α : Ordinal ℓ₁} {β : Ordinal ℓ₂} {f g : ⌞ α ⌟ → ⌞ β ⌟} →
  is-simulation α β f → is-simulation α β g → f ≡ g
simulation-unique {_} {_} {α} {β} {f} {g} f-sim g-sim =
  let
    module α = Ordinal α
    module β = Ordinal β
    open is-simulation
  in ext $ Wf-induction α._<_ α.<-wf (λ x → f x ≡ g x) λ x ih →
    β.≤-antisym
      (β.[<→<]→≤ λ z<fx →
        subst (λ z → z β.< g x)
          (sym (ih (sim f-sim z<fx) (sim-< f-sim z<fx)) ∙ simulates f-sim z<fx)
          (pres-< g-sim (sim-< f-sim z<fx)))
      (β.[<→<]→≤ λ z<gx →
        subst (λ z → z β.< f x)
          (ih (sim g-sim z<gx) (sim-< g-sim z<gx) ∙ simulates g-sim z<gx)
          (pres-< f-sim (sim-< g-sim z<gx)))
```

So they induce an *ordering* on ordinals.
```agda
_≤ₒ_ : (α : Ordinal ℓ₁) (β : Ordinal ℓ₂) → Type (ℓ₁ ⊔ ℓ₂)
α ≤ₒ β = Σ (⌞ α ⌟ → ⌞ β ⌟) (is-simulation α β)

≤ₒ-thin : {ℓ₁ ℓ₂ : Level} {α : Ordinal ℓ₁} {β : Ordinal ℓ₂} → is-prop (α ≤ₒ β)
≤ₒ-thin (_ , f-sim) (_ , g-sim) =
  Σ-path (simulation-unique f-sim g-sim) (is-simulation-is-prop _ _)

≤ₒ-refl : {α : Ordinal ℓ} → α ≤ₒ α
≤ₒ-refl = id , record { pres-< = id ; segment-is-equiv = id-equiv }

≤ₒ-trans : {α : Ordinal ℓ₁} {β : Ordinal ℓ₂} {γ : Ordinal ℓ₃}
  → α ≤ₒ β → β ≤ₒ γ → α ≤ₒ γ
≤ₒ-trans (f , f-sim) (g , g-sim) = g ∘ f , record where
  open is-simulation
  pres-< = pres-< g-sim ∘ pres-< f-sim
  segment-is-equiv = ∘-is-equiv (segment-is-equiv g-sim) (segment-is-equiv f-sim)

≤ₒ-antisym : {α : Ordinal ℓ₁} {β : Ordinal ℓ₂} → α ≤ₒ β → β ≤ₒ α → α ≃ₒ β
≤ₒ-antisym {_} {_} {α} {β} α≤β β≤α =
  is-simulation→is-equiv→≃ₒ (snd α≤β)
  $ is-iso→is-equiv
  $ iso (fst β≤α)
    (happly (ap fst (≤ₒ-thin (≤ₒ-trans β≤α α≤β) ≤ₒ-refl)))
    (happly (ap fst (≤ₒ-thin (≤ₒ-trans α≤β β≤α) ≤ₒ-refl)))

≃ₒ→≤ₒ : {α : Ordinal ℓ₁} {β : Ordinal ℓ₂} → α ≃ₒ β → α ≤ₒ β
≃ₒ→≤ₒ e =
  let open _≃ₒ_ e
  in fst equiv , record {
    pres-< = fst pres-<;
    segment-is-equiv = snd (Σ-ap equiv λ _ → pres-<)
  }

Ordinal-poset : (ℓ : Level) → Poset (lsuc ℓ) ℓ
Ordinal-poset ℓ .Poset.Ob = Ordinal ℓ
Ordinal-poset ℓ .Poset._≤_ = _≤ₒ_
Ordinal-poset ℓ .Poset.≤-thin = ≤ₒ-thin
Ordinal-poset ℓ .Poset.≤-refl = ≤ₒ-refl
Ordinal-poset ℓ .Poset.≤-trans = ≤ₒ-trans
Ordinal-poset ℓ .Poset.≤-antisym h₁ h₂ = ≃ₒ→≡ (≤ₒ-antisym h₁ h₂)
```

In particular, the type of ordinals is a set, and `_≃ₒ_` forms an identity system.

```agda
Ordinal-is-set : is-set (Ordinal ℓ)
Ordinal-is-set {ℓ} = Poset.Ob-is-set (Ordinal-poset ℓ)

private unquoteDecl ≃ₒ-path = declare-record-path ≃ₒ-path (quote _≃ₒ_)

≃ₒ-thin : {α : Ordinal ℓ₁} {β : Ordinal ℓ₂} → is-prop (α ≃ₒ β)
≃ₒ-thin {_} {_} {α} {β} = retract→is-prop
  {A = (α ≤ₒ β) × (β ≤ₒ α)}
  (λ (α≤β , β≤α) → ≤ₒ-antisym α≤β β≤α)
  (λ e → ≃ₒ→≤ₒ e , ≃ₒ→≤ₒ (≃ₒ-sym e))
  (λ e → ≃ₒ-path (ext λ x → refl))
  (×-is-hlevel 1 ≤ₒ-thin ≤ₒ-thin)

≃ₒ-identity-system : is-identity-system {A = Ordinal ℓ} _≃ₒ_ λ _ → ≃ₒ-refl
≃ₒ-identity-system = set-identity-system {r = λ _ → ≃ₒ-refl} (λ _ _ → ≃ₒ-thin) ≃ₒ→≡
```

<!--
```agda
instance
  H-Level-Ordinal
    : ∀ {n} {ℓ} → H-Level (Ordinal ℓ) (suc (suc n))
  H-Level-Ordinal = basic-instance 2 Ordinal-is-set

  H-Level-≃ₒ
    : ∀ {n ℓ₁ ℓ₂} {α : Ordinal ℓ₁} {β : Ordinal ℓ₂} → H-Level (α ≃ₒ β) (suc n)
  H-Level-≃ₒ = basic-instance 1 ≃ₒ-thin
```
-->


We conclude with the ways in which subordinals interact with the order.

```agda
module _ {α : Ordinal ℓ} {x : ⌞ α ⌟} {y : ⌞ Subordinal α x ⌟} where
  open Ordinal α
  Subsubordinal : Subordinal (Subordinal α x) y ≃ₒ Subordinal α (fst y)
  Subsubordinal ._≃ₒ_.equiv = Iso→Equiv
    $ (λ ((z , z<x) , z<y) → z , z<y)
    , iso
      (λ (z , z<y) → (z , <-trans z<y (snd y)) , z<y)
      (λ _ → refl)
      (λ ((z , z<x) , z<y) → Σ-pathp (Σ-pathp refl (<-thin _ _)) refl)
  Subsubordinal ._≃ₒ_.pres-< = id≃

Subordinal-≤ₒ : {α : Ordinal ℓ₁} {x : ⌞ α ⌟} → Subordinal α x ≤ₒ α
Subordinal-≤ₒ {α = α} {x} = fst , record where
  pres-< = id
  segment-is-equiv {y} = Subsubordinal {α = α} {x} {y} ._≃ₒ_.equiv .snd 

is-subordinal-simulation→is-identity : ∀ {α : Ordinal ℓ} {x y f}
  → is-simulation (Subordinal α x) (Subordinal α y) f
  → fst ∘ f ≡ fst
is-subordinal-simulation→is-identity {α = α} {x} {y} {f} sim =
  simulation-unique (snd (≤ₒ-trans (f , sim) Subordinal-≤ₒ)) (snd Subordinal-≤ₒ)

Subordinal-preserves-≤ₒ : {α : Ordinal ℓ} {x y : ⌞ α ⌟}
  → Ordinal._≤_ α x y → Subordinal α x ≤ₒ Subordinal α y
Subordinal-preserves-≤ₒ {α = α} {x} {y} h =
  let open Ordinal α
  in (λ (z , z<x) → z , <→≤→< z<x h) , record where
    pres-< = id
    segment-is-equiv {z , z<x} = is-iso→is-equiv record where
      from ((w , w<y) , w<z) = (w , <-trans w<z z<x) , w<z
      rinv _ = Σ-path (Σ-path refl (<-thin _ _)) (<-thin _ _)
      linv _ = Σ-path (Σ-path refl (<-thin _ _)) (<-thin _ _)

Subordinal-reflects-≤ₒ : {α : Ordinal ℓ} {x y : ⌞ α ⌟}
  → Subordinal α x ≤ₒ Subordinal α y → Ordinal._≤_ α x y
Subordinal-reflects-≤ₒ {α = α} {x} {y} h =
  let open Ordinal α
  in [<→<]→≤ λ {z} z<x → subst (_< y)
    (happly (is-subordinal-simulation→is-identity (snd h)) (z , z<x))
    (snd (h · (z , z<x)))

Subordinal-injective : {α : Ordinal ℓ} {x y : ⌞ α ⌟}
  → Subordinal α x ≃ₒ Subordinal α y → x ≡ y
Subordinal-injective {α = α} e = Ordinal.≤-antisym α
  (Subordinal-reflects-≤ₒ (≃ₒ→≤ₒ e))
  (Subordinal-reflects-≤ₒ (≃ₒ→≤ₒ (≃ₒ-sym e)))
```

## The ordinal of ordinals {defines="ord transfinite-induction"}

The collection of ordinals is itself well-ordered,
with the strict inequality coming from the notion of subordinal.
Induction over this ordering is known as **transfinite induction**.

```agda
_<ₒ_ : Ordinal ℓ₁ → Ordinal ℓ₂ → Type (ℓ₁ ⊔ ℓ₂)
α <ₒ β = Σ ⌞ β ⌟ λ x → α ≃ₒ Subordinal β x

<ₒ-thin : {α : Ordinal ℓ₁} {β : Ordinal ℓ₂} → is-prop (α <ₒ β)
<ₒ-thin {ℓ₁} {ℓ₂} {α} {β} (x , e₁) (y , e₂) =
  Σ-path (Subordinal-injective (≃ₒ-trans (≃ₒ-sym e₁) e₂)) (≃ₒ-thin _ _)

<ₒ→≤ₒ : {α : Ordinal ℓ₁} {β : Ordinal ℓ₂} → α <ₒ β → α ≤ₒ β
<ₒ→≤ₒ (x , e) = ≤ₒ-trans (≃ₒ→≤ₒ e) Subordinal-≤ₒ

≃ₒ→<ₒ→<ₒ : {α : Ordinal ℓ₁} {β : Ordinal ℓ₂} {γ : Ordinal ℓ₃}
  → α ≃ₒ β → β <ₒ γ → α <ₒ γ
≃ₒ→<ₒ→<ₒ e₁ (x , e₂) = x , ≃ₒ-trans e₁ e₂

<ₒ→≤ₒ→<ₒ : {α : Ordinal ℓ₁} {β : Ordinal ℓ₂} {γ : Ordinal ℓ₃}
  → α <ₒ β → β ≤ₒ γ → α <ₒ γ
<ₒ→≤ₒ→<ₒ (x , e) (f , sim) = f x , ≃ₒ-trans e (is-simulation.Subordinal-≃ sim x)

<ₒ-trans : {α : Ordinal ℓ₁} {β : Ordinal ℓ₂} {γ : Ordinal ℓ₃}
  → α <ₒ β → β <ₒ γ → α <ₒ γ
<ₒ-trans h₁ h₂ = <ₒ→≤ₒ→<ₒ h₁ (<ₒ→≤ₒ h₂)

<ₒ-wf : Wf (_<ₒ_ {ℓ} {ℓ})
<ₒ-wf {ℓ} α = acc λ β β<α → go β β<α (<-wf (fst β<α)) where
  open Ordinal α
  go : (β : Ordinal ℓ) → (β<α : β <ₒ α) → Acc _<_ (fst β<α) → Acc _<ₒ_ β
  go β β<α (acc h) = acc λ γ γ<β → go γ
    (<ₒ-trans γ<β β<α)
    (h _ (snd (_≃ₒ_.equiv (snd β<α) · fst γ<β)))

Subordinal-preserves-<ₒ : {α : Ordinal ℓ} {x y : ⌞ α ⌟}
  → Ordinal._<_ α x y → Subordinal α x <ₒ Subordinal α y
Subordinal-preserves-<ₒ {α = α} {x} {y} x<y = (x , x<y) , ≃ₒ-sym Subsubordinal

Subordinal-reflects-<ₒ : {α : Ordinal ℓ} {x y : ⌞ α ⌟}
  → Subordinal α x <ₒ Subordinal α y → Ordinal._<_ α x y
Subordinal-reflects-<ₒ {α = α} {x} {y} ((z , z<y) , e) =
  let
    x≡z : x ≡ z
    x≡z = Subordinal-injective (≃ₒ-trans e Subsubordinal)
  in transport (λ i → Ordinal._<_ α (x≡z (~ i)) y) z<y

[<ₒ→<ₒ]→≤ₒ : {α β : Ordinal ℓ} → (∀ {γ : Ordinal ℓ} → γ <ₒ α → γ <ₒ β) → α ≤ₒ β
[<ₒ→<ₒ]→≤ₒ {α = α} {β} h =
  let
    f : ⌞ α ⌟ → ⌞ β ⌟
    f x = fst (h (x , ≃ₒ-refl))
    hf : ∀ x → Subordinal α x ≃ₒ Subordinal β (f x)
    hf x = snd (h (x , ≃ₒ-refl))
  in f , record where
    open Ordinal β
    pres-< {x} {y} h = Subordinal-reflects-<ₒ
      (<ₒ→≤ₒ→<ₒ
        (≃ₒ→<ₒ→<ₒ (≃ₒ-sym (hf x)) (Subordinal-preserves-<ₒ h))
        (≃ₒ→≤ₒ (hf y)))
    segment-is-hf : ∀ x → Path (⌞ Subordinal α x ⌟ → ⌞ Subordinal β (f x) ⌟)
      (λ (y , y<x) → f y , pres-< y<x)
      (hf x ._≃ₒ_.equiv .fst)
    segment-is-hf x = funext λ (y , y<x) → Σ-path
      (Subordinal-injective
      $ ≃ₒ-trans (≃ₒ-sym (hf y))
      $ ≃ₒ-trans (≃ₒ-sym Subsubordinal)
      $ ≃ₒ-trans (is-simulation.Subordinal-≃ (snd (≃ₒ→≤ₒ (hf x))) (y , y<x))
      $ Subsubordinal)
      (<-thin _ _)
    segment-is-equiv {x} =
      transport (λ i → is-equiv (segment-is-hf x (~ i))) (hf x ._≃ₒ_.equiv .snd)
```

We have everything we need to assemble the ordinal of ordinals,
but the construction is complicated
by the need to shift universe levels.

```agda
Ord : (ℓ : Level) → Ordinal (lsuc ℓ)
Ord ℓ = record where
  poset = record where
    Ob = Ordinal ℓ
    _≤_ α β = Lift _ (α ≤ₒ β)
    ≤-thin (lift h₁) (lift h₂) = ap lift (≤ₒ-thin h₁ h₂)
    ≤-refl = lift ≤ₒ-refl
    ≤-trans (lift h₁) (lift h₂) = lift (≤ₒ-trans h₁ h₂)
    ≤-antisym (lift h₁) (lift h₂) = ≃ₒ→≡ (≤ₒ-antisym h₁ h₂)
  _<_ α β = Lift _ (α <ₒ β)
  <-thin (lift h₁) (lift h₂) = ap lift (<ₒ-thin h₁ h₂)
  <-wf = Wf-induction _<ₒ_ <ₒ-wf (Acc _<_) λ α ih → acc (λ y (lift h) → ih y h)
  <→≤→< (lift h₁) (lift h₂) = lift (<ₒ→≤ₒ→<ₒ h₁ h₂)
  [<→<]→≤ h = lift ([<ₒ→<ₒ]→≤ₒ (λ h' → lower (h (lift h'))))
  <→≤ (lift h) = lift (<ₒ→≤ₒ h)
```

### Subordinals of `Ord` {defines="burali-forti"}

Every ordinal at level `ℓ` is a subordinal of `Ord`.

```agda
Subordinal-Ord : {α : Ordinal ℓ} → Subordinal (Ord ℓ) α ≃ₒ α
Subordinal-Ord {α = α} = record where
  equiv = (λ (_ , lift (x , _)) → x) , is-iso→is-equiv record where
    from x = Subordinal α x , lift (x , ≃ₒ-refl)
    rinv x = refl
    linv (β , lift (x , e)) =
      Σ-pathp (sym (≃ₒ→≡ e)) (apd (λ _ → lift)
        (Σ-pathp refl (is-prop→pathp (λ _ → ≃ₒ-thin) _ _)))
  pres-< {β₁ , lift (x₁ , e₁)} {β₂ , lift (x₂ , e₂)} = prop-ext
    (Lift-is-hlevel 1 <ₒ-thin) (Ordinal.<-thin α)
    (λ h →
      Subordinal-reflects-<ₒ (≃ₒ→<ₒ→<ₒ (≃ₒ-sym e₁) (<ₒ→≤ₒ→<ₒ (lower h) (≃ₒ→≤ₒ e₂))))
    (λ h →
      lift (≃ₒ→<ₒ→<ₒ e₁ (<ₒ→≤ₒ→<ₒ (Subordinal-preserves-<ₒ h) (≃ₒ→≤ₒ (≃ₒ-sym e₂)))))

<ₒ-Ord : (α : Ordinal ℓ) → α <ₒ Ord ℓ
<ₒ-Ord α = α , ≃ₒ-sym Subordinal-Ord
```

As a consequence, `Ord` is a *large* ordinal —
it is not equivalent to any ordinal in the previous universe. 
In naïve set theory, this leads to the Burali-Forti paradox.

```agda
Ord-large : (ℓ : Level) → ¬ Σ (Ordinal ℓ) (Ord ℓ ≃ₒ_)
Ord-large ℓ (Ω , e) = Ordinal.<-irrefl (Ord ℓ) (lift Ω<Ω) where
  Ω<Ω : Ω <ₒ Ω
  Ω<Ω = <ₒ→≤ₒ→<ₒ (<ₒ-Ord Ω) (≃ₒ→≤ₒ e)
```
