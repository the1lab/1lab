<!--
```agda
open import 1Lab.Reflection.Record
open import 1Lab.Prelude

open import Data.Wellfounded.Properties hiding (<-wf)
open import Data.Wellfounded.Base

open import Order.Instances.Nat
open import Order.Base using (Poset)

import Data.Nat.Order as Nat
import Data.Nat.Base as Nat
```
-->

```agda
module Data.Ordinal.Base where
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
    ≤-transforms-< : ∀ {x y} → (x ≤ y) ≃ ∀ {z} → z < x → z < y
  <-trans : ∀ {x y z} → x < y → y < z → x < z
  <-trans x<y y<z = fst ≤-transforms-< (<→≤ y<z) x<y
```

<!--
```agda
  <-irrefl : ∀ {x} → ¬ (x < x)
  <-irrefl {x} x<x = go (<-wf x) where
    go : ¬ Acc _<_ x
    go (acc h) = go (h x x<x)
  <-asym : ∀ {x y} → x < y → y < x → ⊥
  <-asym x<y y<x = <-irrefl (<-trans x<y y<x)

private variable ℓ ℓ₁ ℓ₂ ℓ₃ : Level

instance
  Underlying-Ordinal : Underlying (Ordinal ℓ)
  Underlying-Ordinal = record { ⌞_⌟ = Ordinal.Ob }
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
  ≤-transforms-< {x} {y} = prop-ext
    Nat.≤-is-prop (hlevel 1)
    (λ x≤y z≤x → Nat.≤-trans z≤x x≤y)
    λ h →
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
  p₁ = funext-dep λ {a} {x} p → funext-dep λ {b} {y} q →
    let
      fa≡x = ua-pathp→path equiv p
      fb≡y = ua-pathp→path equiv q
      a<b≡fa<fb : a α.< b ≡ equiv · a β.< equiv · b
      a<b≡fa<fb = ua pres-<
      fa<fb≡x<y : equiv · a β.< equiv · b ≡ x β.< y
      fa<fb≡x<y i = fa≡x i β.< fb≡y i
    in a<b≡fa<fb ∙ fa<fb≡x<y
  p₂ : PathP
    (λ i → (x y : p₀ i) →
       Σ (Type ℓ) λ le → le ≃ ∀ {z : p₀ i} → p₁ i z x → p₁ i z y)
    (λ x y → x α.≤ y , α.≤-transforms-<)
    (λ x y → x β.≤ y , β.≤-transforms-<)
  p₂ = is-prop→pathp (λ i →
    is-contr→is-prop $ Π-is-hlevel 0 λ _ → Π-is-hlevel 0 λ _ →
    is-contr-ΣR (flip-identity-system univalence-identity-system)) _ _
  p₃ : PathP (λ i → ∀ {x y} → is-prop (fst (p₂ i x y))) α.≤-thin β.≤-thin
  p₃ = is-prop→pathp (λ _ → hlevel 1) _ _
  p₄ : PathP (λ i → ∀ {x} → fst (p₂ i x x)) α.≤-refl β.≤-refl
  p₄ = is-prop→pathp (λ i → Π-is-hlevel' 1 λ x → p₃ i {x} {x}) _ _
  p₅ : PathP (λ i → ∀ {x y z} → fst (p₂ i x y) → fst (p₂ i y z) → fst (p₂ i x z))
    α.≤-trans β.≤-trans
  p₅ = is-prop→pathp (λ i →
    Π-is-hlevel' 1 λ x →
    Π-is-hlevel' 1 λ y →
    Π-is-hlevel' 1 λ z →
    Π-is-hlevel 1 λ _ →
    Π-is-hlevel 1 λ _ →
    p₃ i {x} {z}) _ _
  p₆ : PathP (λ i → ∀ {x y} → fst (p₂ i x y) → fst (p₂ i y x) → x ≡ y)
    α.≤-antisym β.≤-antisym
  p₆ = is-prop-i0→pathp (
    Π-is-hlevel' 1 λ x →
    Π-is-hlevel' 1 λ y →
    Π-is-hlevel 1 λ _ →
    Π-is-hlevel 1 λ _ →
    α.Ob-is-set x y) _ _
  p₇ : PathP (λ i → ∀ {x y} → is-prop (p₁ i x y)) α.<-thin β.<-thin
  p₇ = is-prop→pathp (λ _ → hlevel 1) _ _
  p₈ : PathP (λ i → ∀ {x y} → p₁ i x y → fst (p₂ i x y)) α.<→≤ β.<→≤
  p₈ = is-prop→pathp (λ i →
    Π-is-hlevel' 1 λ x →
    Π-is-hlevel' 1 λ y →
    Π-is-hlevel 1 λ _ →
    p₃ i {x} {y}) _ _
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
  p i .Ordinal.≤-transforms-< {x} {y} = snd (p₂ i x y)
  p i .Ordinal.<-wf = p₉ i
```
</details>
```agda
module _
  (X : Type ℓ) (_<_ : X → X → Type ℓ)
  (<-thin : ∀ {x y} → is-prop (x < y))
  (<-wf : Wf _<_)
  (<-trans : ∀ {x y z} → x < y → y < z → x < z)
  (ext : ∀ {x y} → (∀ {z} → (z < x) ≃ (z < y)) → x ≡ y)
  where

  ordinal : Ordinal ℓ
  ordinal = record where
    poset = record where
      Ob = X
      _≤_ x y = ∀ {z} → z < x → z < y
      ≤-thin = Π-is-hlevel' 1 λ _ → Π-is-hlevel 1 λ _ → <-thin
      ≤-refl = id
      ≤-trans h₁ h₂ = h₂ ∘ h₁
      ≤-antisym h₁ h₂ = ext (prop-ext <-thin <-thin h₁ h₂)
    _<_ = _<_
    <-thin = <-thin
    <→≤ x<y z<x = <-trans z<x x<y
    ≤-transforms-< = id≃
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
  Subordinal .Ordinal.poset .Poset.Ob = Σ ⌞ α ⌟ (_< a)
  Subordinal .Ordinal.poset .Poset._≤_ (x , _) (y , _) = x ≤ y
  Subordinal .Ordinal.poset .Poset.≤-thin = ≤-thin
  Subordinal .Ordinal.poset .Poset.≤-refl = ≤-refl
  Subordinal .Ordinal.poset .Poset.≤-trans = ≤-trans
  Subordinal .Ordinal.poset .Poset.≤-antisym x≤y y≤x =
    Σ-path (≤-antisym x≤y y≤x) (<-thin _ _)
  Subordinal .Ordinal._<_ (x , _) (y , _) = x < y
  Subordinal .Ordinal.<-thin = <-thin
  Subordinal .Ordinal.<→≤ = <→≤
  Subordinal .Ordinal.≤-transforms-< {x , x<a} {y , y<a} =
    ≤-transforms-< ∙e prop-ext
      (Π-is-hlevel' 1 λ _ → Π-is-hlevel 1 λ _ → <-thin)
      (Π-is-hlevel' 1 λ _ → Π-is-hlevel 1 λ _ → <-thin)
      (λ h {z} z<x → h {fst z} z<x)
      (λ h {z} z<x → h {z , <-trans z<x x<a} z<x)
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
  restriction : (x : α.Ob) → ⌞ Subordinal α x ⌟ → ⌞ Subordinal β (f x) ⌟
  restriction x (y , y<x) = f y , pres-< y<x
  field
    restriction-is-equiv : ∀ {x} → is-equiv (restriction x)
```

Simulations are injective, and monotone in every reasonable sense.
```agda
  pres-≤ : ∀ {x y} → x α.≤ y → f x β.≤ f y
  pres-≤ {x} {y} x≤y = equiv→inverse (snd β.≤-transforms-<) λ {z} z<fx →
    let
      (w , w<x) , p = restriction-is-equiv .is-eqv (z , z<fx) .centre
      fw≡z = ap fst p
    in transport (λ i → fw≡z i β.< f y) (pres-< (fst α.≤-transforms-< x≤y w<x))

  reflects-≤ : ∀ {x y} → f x β.≤ f y → x α.≤ y
  reflects-≤ = go (α.<-wf _) (α.<-wf _) where
    go : ∀ {x y} → Acc α._<_ x → Acc α._<_ y → f x β.≤ f y → x α.≤ y
    go {x} {y} (acc hx) (acc hy) fx≤fy =
      equiv→inverse (snd α.≤-transforms-<) λ {z} z<x →
      let
        fz<fx = pres-< z<x
        fz<fy = fst β.≤-transforms-< fx≤fy fz<fx
        (w , w<y) , p = restriction-is-equiv .is-eqv (f z , fz<fy) .centre
        fw≡fz = ap fst p
        w≤z = go (hy w w<y) (hx z z<x) (β.≤-refl' fw≡fz)
        z≤w = go (hx z z<x) (hy w w<y) (β.≤-refl' (sym fw≡fz))
        w≡z = α.≤-antisym w≤z z≤w
      in transport (λ i → w≡z i α.< y) w<y

  has-injective : injective f
  has-injective p = α.≤-antisym
    (reflects-≤ (β.≤-refl' p))
    (reflects-≤ (β.≤-refl' (sym p)))

  has-is-embedding : is-embedding f
  has-is-embedding = injective→is-embedding β.Ob-is-set f has-injective

  reflects-< : ∀ {x y} → f x β.< f y → x α.< y
  reflects-< {x} {y} fx<fy =
    let
      (z , z<y) , p = restriction-is-equiv .is-eqv (f x , fx<fy) .centre
      z≡x = has-injective (ap fst p)
    in transport (λ i → z≡x i α.< y) z<y

  Subordinal-≃ : (x : α.Ob) → Subordinal α x ≃ₒ Subordinal β (f x)
  Subordinal-≃ x = record where
    equiv = restriction x , restriction-is-equiv
    pres-< = prop-ext α.<-thin β.<-thin pres-< reflects-<
```

<!--
```agda
is-simulation-is-prop : ∀ {α β f} → is-prop (is-simulation {ℓ₁} {ℓ₂} α β f)
is-simulation-is-prop {_} {_} {α} {β} {f} s₁ s₂ = p where
  p₁ : ∀ {x y} → is-simulation.pres-< s₁ {x} {y} ≡ is-simulation.pres-< s₂ {x} {y}
  p₁ = (Π-is-hlevel 1 λ _ → Ordinal.<-thin β) _ _
  p₂ : ∀ {x} → PathP
    (λ i → is-equiv {A = ⌞ Subordinal α x ⌟} {B = ⌞ Subordinal β (f x) ⌟}
      λ (y , y<x) → f y , p₁ i y<x)
    (is-simulation.restriction-is-equiv s₁ {x})
    (is-simulation.restriction-is-equiv s₂ {x})
  p₂ = is-prop→pathp (λ _ → is-equiv-is-prop _) _ _
  p : s₁ ≡ s₂
  p i .is-simulation.pres-< = p₁ i
  p i .is-simulation.restriction-is-equiv = p₂ i

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
  (is-simulation.pres-< sim) (is-simulation.reflects-< sim)
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
      (equiv→inverse (snd β.≤-transforms-<) λ z<fx →
        let (w , w<x) , p = restriction-is-equiv f-sim .is-eqv (_ , z<fx) .centre
        in subst (λ z → z β.< g x) (sym (ih w w<x) ∙ ap fst p) (pres-< g-sim w<x))
      (equiv→inverse (snd β.≤-transforms-<) λ z<gx →
        let (w , w<x) , p = restriction-is-equiv g-sim .is-eqv (_ , z<gx) .centre
        in subst (λ z → z β.< f x) (ih w w<x ∙ ap fst p) (pres-< f-sim w<x))
```

So they induce an *ordering* on ordinals.
```agda
_≤ₒ_ : (α : Ordinal ℓ₁) (β : Ordinal ℓ₂) → Type (ℓ₁ ⊔ ℓ₂)
α ≤ₒ β = Σ (⌞ α ⌟ → ⌞ β ⌟) (is-simulation α β)

≤ₒ-thin : {ℓ₁ ℓ₂ : Level} {α : Ordinal ℓ₁} {β : Ordinal ℓ₂} → is-prop (α ≤ₒ β)
≤ₒ-thin (_ , f-sim) (_ , g-sim) =
  Σ-path (simulation-unique f-sim g-sim) (is-simulation-is-prop _ _)

≤ₒ-refl : {α : Ordinal ℓ} → α ≤ₒ α
≤ₒ-refl = id , record { pres-< = id ; restriction-is-equiv = id-equiv }

≤ₒ-trans : {α : Ordinal ℓ₁} {β : Ordinal ℓ₂} {γ : Ordinal ℓ₃}
  → α ≤ₒ β → β ≤ₒ γ → α ≤ₒ γ
≤ₒ-trans (f , f-sim) (g , g-sim) = g ∘ f , record {
  pres-< = is-simulation.pres-< g-sim ∘ is-simulation.pres-< f-sim;
  restriction-is-equiv = ∘-is-equiv
    (is-simulation.restriction-is-equiv g-sim)
    (is-simulation.restriction-is-equiv f-sim)}

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
    restriction-is-equiv = snd (Σ-ap equiv λ _ → pres-<)
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
  (λ e → ≃ₒ-path
    (ext λ x → refl)
    (is-prop→pathp (λ _ →
      Π-is-hlevel' 1 λ _ →
      Π-is-hlevel' 1 λ _ →
      ≃-is-hlevelˡ 0 (Ordinal.<-thin α)) _ _))
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
  restriction-is-equiv {y} = Subsubordinal {α = α} {x} {y} ._≃ₒ_.equiv .snd 

is-subordinal-simulation→is-identity : ∀ {α : Ordinal ℓ} {x y f}
  → is-simulation (Subordinal α x) (Subordinal α y) f
  → fst ∘ f ≡ fst
is-subordinal-simulation→is-identity {α = α} {x} {y} {f} sim =
  simulation-unique (snd (≤ₒ-trans (f , sim) Subordinal-≤ₒ)) (snd Subordinal-≤ₒ)

Subordinal-preserves-≤ₒ : {α : Ordinal ℓ} {x y : ⌞ α ⌟}
  → Ordinal._≤_ α x y → Subordinal α x ≤ₒ Subordinal α y
Subordinal-preserves-≤ₒ {α = α} {x} {y} h =
  let open Ordinal α
  in (λ (z , z<x) → z , fst ≤-transforms-< h z<x) , record where
    pres-< = id
    restriction-is-equiv {z , z<x} = is-iso→is-equiv record where
      from ((w , w<y) , w<z) = (w , <-trans w<z z<x) , w<z
      rinv _ = Σ-path (Σ-path refl (<-thin _ _)) (<-thin _ _)
      linv _ = Σ-path (Σ-path refl (<-thin _ _)) (<-thin _ _)

Subordinal-reflects-≤ₒ : {α : Ordinal ℓ} {x y : ⌞ α ⌟}
  → Subordinal α x ≤ₒ Subordinal α y → Ordinal._≤_ α x y
Subordinal-reflects-≤ₒ {α = α} {x} {y} h =
  let open Ordinal α
  in equiv→inverse (snd ≤-transforms-<) λ {z} z<x →
  subst (_< y)
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
    restriction-is-hf : ∀ x → Path (⌞ Subordinal α x ⌟ → ⌞ Subordinal β (f x) ⌟)
      (λ (y , y<x) → f y , pres-< y<x)
      (hf x ._≃ₒ_.equiv .fst)
    restriction-is-hf x = funext λ (y , y<x) → Σ-path
      (Subordinal-injective
      $ ≃ₒ-trans (≃ₒ-sym (hf y))
      $ ≃ₒ-trans (≃ₒ-sym Subsubordinal)
      $ ≃ₒ-trans (is-simulation.Subordinal-≃ (snd (≃ₒ→≤ₒ (hf x))) (y , y<x))
      $ Subsubordinal)
      (<-thin _ _)
    restriction-is-equiv {x} =
      transport (λ i → is-equiv (restriction-is-hf x (~ i))) (hf x ._≃ₒ_.equiv .snd)
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
  ≤-transforms-< = prop-ext
    (Poset.≤-thin poset) (Π-is-hlevel' 1 λ _ → Π-is-hlevel 1 λ _ → <-thin)
    (λ (lift h₁) (lift h₂) → lift (<ₒ→≤ₒ→<ₒ h₂ h₁))
    λ h → lift ([<ₒ→<ₒ]→≤ₒ (λ h' → lower (h (lift h'))))
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
