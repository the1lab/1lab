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

  Ordinal-≺-hlevel-proj : hlevel-projection (quote Ordinal._≺_)
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
