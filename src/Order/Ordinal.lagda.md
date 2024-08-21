---
description: |
  Ordinals.
---
<!--
```agda
open import 1Lab.Reflection hiding (absurd)
open import 1Lab.Prelude

open import Data.Wellfounded.Base
open import Data.Sum
open import Data.Fin using (Fin; fsuc; fzero)

import Data.Fin as Fin
import Data.Nat as Nat
import Data.Wellfounded.Base as Wf

```
-->
```agda
module Order.Ordinal where
```

# Ordinals {defines="ordinal"}

```agda
record Ordinal (o ℓ : Level) : Type (lsuc o ⊔ lsuc ℓ) where
  no-eta-equality
  field
    Ob : Type o
    _≺_ : Ob → Ob → Type ℓ

    ≺-wf : ∀ x → Acc _≺_ x
    ≺-ext : ∀ {x y} → (∀ a → a ≺ x → a ≺ y) → (∀ a → a ≺ y → a ≺ x) → x ≡ y
    ≺-trans : ∀ {x y z} → x ≺ y → y ≺ z → x ≺ z
    ≺-is-prop : ∀ {x y} → is-prop (x ≺ y)


  -- Left and right whiskerings by equality types.
  ≺-whiskerl : ∀ {x y z} → x ≡ y → y ≺ z → x ≺ z
  ≺-whiskerl {z = z} x=y y≺z = subst (_≺ z) (sym x=y) y≺z

  ≺-whiskerr : ∀ {x y z} → x ≺ y → y ≡ z → x ≺ z
  ≺-whiskerr {x = x} x≺y y=z = subst (x ≺_) y=z x≺y

  opaque
    Ob-is-set : is-set Ob
    Ob-is-set = constant-map→is-set rectify-const
      where
        rectify : ∀ {x y : Ob} → x ≡ y → x ≡ y
        rectify p = ≺-ext (λ a a≺x → ≺-whiskerr a≺x p) (λ a a≺y → ≺-whiskerr a≺y (sym p))

        rectify-const : ∀ {x y} → (p q : x ≡ y) → rectify p ≡ rectify q
        rectify-const _ _ = ap₂ ≺-ext (ext λ a a≺x → ≺-is-prop _ _) (ext λ a a≺y → ≺-is-prop _ _)


instance
  Underlying-Ordinal : ∀ {o ℓ} → Underlying (Ordinal o ℓ)
  Underlying-Ordinal .Underlying.ℓ-underlying = _
  Underlying-Ordinal .Underlying.⌞_⌟ = Ordinal.Ob

  open hlevel-projection

  Ordinal-ob-hlevel-proj : hlevel-projection (quote Ordinal.Ob)
  Ordinal-ob-hlevel-proj .has-level = quote Ordinal.Ob-is-set
  Ordinal-ob-hlevel-proj .get-level _ = pure (lit (nat 2))
  Ordinal-ob-hlevel-proj .get-argument (_ ∷ _ ∷ arg _ t ∷ _) = pure t
  {-# CATCHALL #-}
  Ordinal-ob-hlevel-proj .get-argument _                     = typeError []

  Ordinal-≺-hlevel-proj : hlevel-projection (quote Ordinal.Ob)
  Ordinal-≺-hlevel-proj .has-level = quote Ordinal.≺-is-prop
  Ordinal-≺-hlevel-proj .get-level _ = pure (lit (nat 1))
  Ordinal-≺-hlevel-proj .get-argument (_ ∷ _ ∷ arg _ t ∷ _) = pure t
  {-# CATCHALL #-}
  Ordinal-≺-hlevel-proj .get-argument _                     = typeError []
```

## Simple examples

```agda
Finₒ : Nat → Ordinal lzero lzero
Finₒ n = ord where
  <-wf : Wf (Fin._<_ {n})
  <-wf i = go i i Nat.≤-refl where
    go : ∀ {m n} (i : Fin m) (j : Fin n) → .((Fin.to-nat j) Nat.≤ (Fin.to-nat i)) → Acc Fin._<_ j
    go i fzero j≤i = acc λ _ ()
    go (fsuc i) (fsuc j) j≤i = acc λ k k<j →
      go i k (Nat.≤-trans (Nat.≤-peel k<j) (Nat.≤-peel j≤i))

  <-ext
    : ∀ {n} {i j : Fin n}
    → (∀ k → k Fin.< i → k Fin.< j)
    → (∀ k → k Fin.< j → k Fin.< i)
    → i ≡ j
  <-ext {i = fzero} {j = fzero} i≼j j≼i = refl
  <-ext {i = fzero} {j = fsuc j} i≼j j≼i =
    absurd (Nat.<-irrefl refl (j≼i fzero Nat.0<s))
  <-ext {i = fsuc i} {j = fzero} i≼j j≼i =
    absurd (Nat.<-irrefl refl (i≼j fzero Nat.0<s))
  <-ext {i = fsuc i} {j = fsuc j} i≼j j≼i =
    ap fsuc $ <-ext
      (λ k k<i → Nat.≤-peel (i≼j (fsuc k) (Nat.s≤s k<i)))
      (λ k k<j → Nat.≤-peel (j≼i (fsuc k) (Nat.s≤s k<j)))

  ord : Ordinal lzero lzero
  ord .Ordinal.Ob = Fin n
  ord .Ordinal._≺_ = Fin._<_
  ord .Ordinal.≺-wf = <-wf
  ord .Ordinal.≺-ext = <-ext
  ord .Ordinal.≺-trans = Nat.<-trans
  ord .Ordinal.≺-is-prop = hlevel 1
```

<!--
```agda
instance
  Number-Ordinal : Number (Ordinal lzero lzero)
  Number-Ordinal .Number.Constraint _ = Lift _ ⊤
  Number-Ordinal .Number.fromNat n = Finₒ n
```
-->

```agda
ωₒ : Ordinal lzero lzero
ωₒ .Ordinal.Ob = Nat
ωₒ .Ordinal._≺_ = Nat._<_
ωₒ .Ordinal.≺-wf = Nat.<-wf
ωₒ .Ordinal.≺-ext p q = Nat.≤-antisym (Nat.<-below p) (Nat.<-below q)
ωₒ .Ordinal.≺-trans = Nat.<-trans
ωₒ .Ordinal.≺-is-prop = hlevel 1
```


-- ```agda
-- module Reasoning {o ℓ} (X : Ordinal o ℓ) where
--   open Ordinal X public

--   data ≺-Reasoning (x y : Ob) : Type (o ⊔ ℓ) where
--     strong : x ≺ y → ≺-Reasoning x y
--     weak : x ≡ y → ≺-Reasoning x y

--   is-strong : ∀ {x y} → ≺-Reasoning x y → Type
--   is-strong (strong _) = ⊤
--   is-strong (weak _) = ⊥

--   begin-≺_ : ∀ {x y} → (x≺y : ≺-Reasoning x y) → { is-strong x≺y } → x ≺ y
--   begin-≺ (strong x≺y) = x≺y

--   step-≺ : ∀ x {y z} → ≺-Reasoning y z → x ≺ y → ≺-Reasoning x z
--   step-≺ x (strong y≺z) x≺y = strong (≺-trans x≺y y≺z)
--   step-≺ x (weak y=z) x≺y = strong (≺-whiskerr x≺y y=z)

--   step-≡ : ∀ x {y z} → ≺-Reasoning y z → x ≡ y → ≺-Reasoning x z
--   step-≡ x (strong y≺z) x=y = strong (≺-whiskerl x=y y≺z)
--   step-≡ x (weak y=z) x=y = weak (x=y ∙ y=z)

--   step-≡˘ : ∀ x {y z} → ≺-Reasoning y z → y ≡ x → ≺-Reasoning x z
--   step-≡˘ x y p = step-≡ x y (sym p)

--   _≺∎ : ∀ x → ≺-Reasoning x x
--   _≺∎ x = weak refl

--   infix  1 begin-≺_
--   infixr 2 step-≺
--   infixr 2 step-≡
--   infixr 2 step-≡˘

--   syntax step-≺ x q p = x ≺⟨ p ⟩ q
--   syntax step-≡ x q p = x =⟨ p ⟩ q
--   syntax step-≡˘ x q p = x =˘⟨ p ⟩ q
--   infix  3 _≺∎
-- ```


-- ```agda
-- record Simulation
--   {o o' ℓ ℓ'}
--   (X : Ordinal o ℓ)
--   (Y : Ordinal o' ℓ')
--   : Type (o ⊔ o' ⊔ ℓ ⊔ ℓ')
--   where
--   no-eta-equality
--   private
--     module X = Ordinal X
--     module Y = Ordinal Y
--   field
--     map : X.Ob → Y.Ob
--     pres-≺ : ∀ {x y} → x X.≺ y → map x Y.≺ map y
--     sim : ∀ {x y} → y Y.≺ map x → X.Ob
--     sim-≺ : ∀ {x y} {p : y Y.≺ map x} → sim p X.≺ x
--     simulates : ∀ {x y} {p : y Y.≺ map x} → map (sim p) ≡ y

-- --   injective : is-injective map
-- --   injective {a} {b} =
-- --     Wf-induction₂ X._≺_ X.≺-wf (λ a b → map a ≡ map b → a ≡ b)
-- --       (λ x y rec fx=fy → X.≺-ext
-- --         (λ a a≺x → X.≺-whiskerl (rec a (sim (map-whiskerr a≺x fx=fy)) a≺x sim-≺ (sym simulates)) sim-≺)
-- --         (λ a a≺y → X.≺-whiskerl (sym $ rec (sim (map-whiskerr a≺y (sym fx=fy))) a sim-≺ a≺y simulates) sim-≺))
-- --       a b
-- --     where
-- --       map-whiskerr : ∀ {x y a} → a X.≺ x → map x ≡ map y → map a Y.≺ map y
-- --       map-whiskerr a≺x fx=fy = Y.≺-whiskerr (pres-≺ a≺x) fx=fy

-- --   sim-unique
-- --     : ∀ {x y a} {p : y Y.≺ map x}
-- --     → map a ≡ y
-- --     → a ≡ sim p
-- --   sim-unique fa=y = injective (fa=y ∙ sym simulates)

-- -- instance
-- --   Funlike-Simulation
-- --     : ∀ {o ℓ o' ℓ'} {X : Ordinal o ℓ} {Y : Ordinal o' ℓ'}
-- --     → Funlike (Simulation X Y) ⌞ X ⌟ (λ _ → ⌞ Y ⌟)
-- --   Funlike-Simulation = record { _#_ = Simulation.map }

-- -- private variable
-- --   o ℓ o' ℓ' o'' ℓ'' : Level
-- --   X Y Z : Ordinal o ℓ

-- -- Simulation-is-prop : is-prop (Simulation X Y)
-- -- Simulation-is-prop {X = X} {Y = Y} f g = {!!} where
-- --   module X = Reasoning X
-- --   module Y = Reasoning Y
-- --   module f = Simulation f
-- --   module g = Simulation g

-- --   map-path : ∀ (x : ⌞ X ⌟) → f # x ≡ g # x
-- --   map-path x =
-- --     Wf-induction X._≺_ X.≺-wf (λ x → f # x ≡ g # x)
-- --       (λ x rec → Y.≺-ext
-- --         (λ a a≺fx → Y.begin-≺
-- --           a Y.=˘⟨ f.simulates ⟩
-- --           f # f.sim a≺fx Y.=⟨ rec (f.sim a≺fx) f.sim-≺ ⟩
-- --           g # f.sim a≺fx Y.≺⟨ g.pres-≺ f.sim-≺ ⟩
-- --           g # x          Y.≺∎)
-- --         λ a a≺gx → Y.begin-≺
-- --           a              Y.=˘⟨ g.simulates ⟩
-- --           g # g.sim a≺gx Y.=˘⟨ rec (g.sim a≺gx) g.sim-≺ ⟩
-- --           f # g.sim a≺gx Y.≺⟨ f.pres-≺ g.sim-≺ ⟩
-- --           f # x          Y.≺∎)
-- --       x

-- --   -- path : f ≡ g
-- --   -- path i .Simulation.map x = map-path x i
-- --   -- path i .Simulation.pres-≺ x≺y =
-- --   --   is-prop→pathp (λ i → Y.≺-is-prop) (f.pres-≺ x≺y) (g.pres-≺ x≺y) i
-- --   -- path i .Simulation.sim y≺px =
-- --   --   {!!}
-- --   -- path i .Simulation.sim-≺ {p = y≺px} =
-- --   --   {!!}
-- --   -- path i .Simulation.simulates {p = y≺px} = {!!}
```

  -- ≺-elim
  --   : ∀ {κ} (P : Ob → Type κ)
  --   → (∀ x₀ → (∀ y → y ≺ x₀ → P y) → P x₀)
  --   → ∀ x₀ → P x₀
  -- ≺-elim = Wf-induction _≺_ ≺-wf

  -- ≺-bounded-elim
  --   : ∀ {κ} {x : Ob}
  --   → (P : Ob → Type κ)
  --   → (∀ x₀ → x₀ ≺ x → (∀ y → y ≺ x₀ → P y) → P x₀)
  --   → ∀ x₀ → x₀ ≺ x → P x₀
  -- ≺-bounded-elim {x = x} P work =
  --   ≺-elim (λ x₀ → x₀ ≺ x → P x₀) λ x₀ rec x₀≺x →
  --     work x₀ x₀≺x (λ y y≺x₀ → rec y y≺x₀ (≺-trans y≺x₀ x₀≺x))

  -- ≺-irrefl : ∀ {x} → x ≺ x → ⊥
  -- ≺-irrefl {x} x≺x =
  --   ≺-elim (λ x₀ → x ≺ x₀ → ⊥)
  --     (λ x₀ rec x≺x₀ → rec x x≺x₀ x≺x)
  --     x x≺x

  -- ≺-asym : ∀ {x y} → x ≺ y → y ≺ x → ⊥
  -- ≺-asym x≺y y≺x = ≺-irrefl (≺-trans x≺y y≺x)

  -- -- Poset structure.
  -- _≼_ : Ob → Ob → Type (o ⊔ ℓ)
  -- x ≼ y = ∀ a → a ≺ x → a ≺ y

  -- ≼-refl : ∀ {x} → x ≼ x
  -- ≼-refl a a≺x = a≺x

  -- ≼-trans : ∀ {x y z} → x ≼ y → y ≼ z → x ≼ z
  -- ≼-trans x≼y y≼z a a≺x = y≼z a (x≼y a a≺x)

  -- ≼-antisym : ∀ {x y} → x ≼ y → y ≼ x → x ≡ y
  -- ≼-antisym = ≺-ext

  -- ≺-weaken : ∀ {x y} → x ≺ y → x ≼ y
  -- ≺-weaken x≺y a a≺x = ≺-trans a≺x x≺y

  -- ≼-transr : ∀ {x y z} → x ≺ y → y ≼ z → x ≺ z
  -- ≼-transr x≺y y≼z = y≼z _ x≺y

  -- path→≼ : ∀ {x y} → x ≡ y → x ≼ y
  -- path→≼ p a a≺x = subst (a ≺_) p a≺x
