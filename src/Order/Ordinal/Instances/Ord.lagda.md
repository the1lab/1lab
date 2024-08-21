---
description: |
  The ordinal of all ordinals.
---
<!--
```agda
open import Cat.Prelude

open import Order.Ordinal

import Order.Ordinal.Reasoning
```
-->
```agda
module Order.Ordinal.Instances.Ord where
```

# The ordinal of all ordinals.

```agda
record Simulation
  {o o' ℓ ℓ'}
  (X : Ordinal o ℓ)
  (Y : Ordinal o' ℓ')
  : Type (o ⊔ o' ⊔ ℓ ⊔ ℓ')
  where
  no-eta-equality
  private
    module X = Order.Ordinal.Reasoning X
    module Y = Order.Ordinal.Reasoning Y
  field
    hom : X.Ob → Y.Ob
    pres-≺ : ∀ {x y} → x X.≺ y → hom x Y.≺ hom y
    sim : ∀ {x y} → y Y.≺ hom x → X.Ob
    sim-≺ : ∀ {x y} {p : y Y.≺ hom x} → sim p X.≺ x
    simulates : ∀ {x y} {p : y Y.≺ hom x} → hom (sim p) ≡ y

  injective : is-injective hom
  injective {a} {b} =
    X.≺-elim₂ (λ a b → hom a ≡ hom b → a ≡ b)
      (λ x y recl recr rec fx=fy → X.≺-ext
        (λ a a≺x → X.≺-whiskerl (rec a (sim (map-whiskerr a≺x fx=fy)) a≺x sim-≺ (sym simulates)) sim-≺)
        (λ a a≺y → X.≺-whiskerl (sym $ rec (sim (map-whiskerr a≺y (sym fx=fy))) a sim-≺ a≺y simulates) sim-≺))
      a b
    where
      map-whiskerr : ∀ {x y a} → a X.≺ x → hom x ≡ hom y → hom a Y.≺ hom y
      map-whiskerr a≺x fx=fy = Y.≺-whiskerr (pres-≺ a≺x) fx=fy

  sim-unique
    : ∀ {x y a} {p : y Y.≺ hom x}
    → hom a ≡ y
    → a ≡ sim p
  sim-unique fa=y = injective (fa=y ∙ sym simulates)

instance
  Funlike-Simulation
    : ∀ {o ℓ o' ℓ'} {X : Ordinal o ℓ} {Y : Ordinal o' ℓ'}
    → Funlike (Simulation X Y) ⌞ X ⌟ (λ _ → ⌞ Y ⌟)
  Funlike-Simulation = record { _#_ = Simulation.hom }

private variable
  o ℓ o' ℓ' o'' ℓ'' : Level
  X Y Z : Ordinal o ℓ

Simulation-is-prop : is-prop (Simulation X Y)
Simulation-is-prop {X = X} {Y = Y} f g = path where
  module X = Order.Ordinal.Reasoning X
  module Y = Order.Ordinal.Reasoning Y
  module f = Simulation f
  module g = Simulation g

  map-path : ∀ (x : ⌞ X ⌟) → f # x ≡ g # x
  map-path x =
    X.≺-elim (λ x → f # x ≡ g # x)
      (λ x rec → Y.≺-ext
        (λ a a≺fx → Y.begin-≺
          a Y.=˘⟨ f.simulates ⟩
          f # f.sim a≺fx Y.=⟨ rec (f.sim a≺fx) f.sim-≺ ⟩
          g # f.sim a≺fx Y.≺⟨ g.pres-≺ f.sim-≺ ⟩
          g # x          Y.≺∎)
        λ a a≺gx → Y.begin-≺
          a              Y.=˘⟨ g.simulates ⟩
          g # g.sim a≺gx Y.=˘⟨ rec (g.sim a≺gx) g.sim-≺ ⟩
          f # g.sim a≺gx Y.≺⟨ f.pres-≺ g.sim-≺ ⟩
          f # x          Y.≺∎)
      x

  sim-path : ∀ {x y} → PathP (λ i → y Y.≺ map-path x i → X.Ob) f.sim g.sim
  sim-path {x} {y} = funext-dep λ p → f.injective $
    f.hom (f.sim (p i0)) ≡⟨ f.simulates ⟩
    y                    ≡˘⟨ g.simulates ⟩
    g.hom (g.sim (p i1)) ≡˘⟨ map-path (g.sim (p i1)) ⟩
    f.hom (g.sim (p i1)) ∎

  path : f ≡ g
  path i .Simulation.hom x = map-path x i
  path i .Simulation.pres-≺ {x} {y} x≺y =
    is-prop→pathp (λ i → Y.≺-is-prop {x = map-path x i} {y = map-path y i})
      (f.pres-≺ x≺y) (g.pres-≺ x≺y) i
  path i .Simulation.sim {x} {y} y≺px = sim-path i y≺px
  path i .Simulation.sim-≺ {x = x} {y = y} {p = y≺px} =
    is-prop→pathp (λ i →
        Π-is-hlevel {A = y Y.≺ map-path x i} 1 λ y≺px →
        X.≺-is-prop {x = sim-path i y≺px} {y = x})
      (λ p → f.sim-≺ {p = p})
      (λ p → g.sim-≺ {p = p})
      i y≺px
  path i .Simulation.simulates {x = x} {y = y} {p = y≺px} =
    is-prop→pathp (λ i →
        Π-is-hlevel {A = y Y.≺ map-path x i} 1 λ y≺px →
        Y.Ob-is-set (map-path (sim-path i y≺px) i) y)
      (λ p → f.simulates {p = p})
      (λ p → g.simulates {p = p})
      i y≺px
```

```agda
Ord : ∀ o ℓ → Ordinal (lsuc o ⊔ lsuc ℓ) (o ⊔ {!!})
Ord o ℓ .Ordinal.Ob = Ordinal o ℓ
Ord o ℓ .Ordinal._≺_ X Y = Σ[ y ∈ Y ] ⌞ X ⌟ ≃ {!!}
Ord o ℓ .Ordinal.≺-wf = {!!}
Ord o ℓ .Ordinal.≺-ext = {!!}
Ord o ℓ .Ordinal.≺-trans = {!!}
Ord o ℓ .Ordinal.≺-is-prop = {!!}
```
