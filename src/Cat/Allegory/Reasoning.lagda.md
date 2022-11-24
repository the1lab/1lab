```agda
{-# OPTIONS --allow-unsolved-metas #-}
open import Cat.Allegory.Base
open import Cat.Prelude

import Cat.Reasoning

module Cat.Allegory.Reasoning {o ℓ ℓ′} (A : Allegory o ℓ ℓ′) where
```

<!--
```agda
open Allegory A public
open Cat.Reasoning (A .Allegory.cat)
  hiding (module HLevel-instance ; Ob ; Hom ; id ; idl ; idr ; assoc ; _∘_)
  public
```

-->

# Combinators for allegories

For reasoning about morphisms in allegories, the first thing we need is
a convenient syntax for piecing together long arguments by transitivity.
The following operators allow us to interweave throwing in an
inequality, and rewriting by an equality:

```agda
private variable
  w x y z : Ob
  f f′ g g′ h : Hom x y

_≤⟨_⟩_ : ∀ (f : Hom x y) → f ≤ g → g ≤ h → f ≤ h
_=⟨_⟩_ : ∀ (f : Hom x y) → f ≡ g → g ≤ h → f ≤ h
_=˘⟨_⟩_ : ∀ (f : Hom x y) → g ≡ f → g ≤ h → f ≤ h
_≤∎    : ∀ (f : Hom x y) → f ≤ f

f ≤⟨ p ⟩ q = ≤-trans p q
f =⟨ p ⟩ q = subst (_≤ _) (sym p) q
f =˘⟨ p ⟩ q = subst (_≤ _) p q
f ≤∎ = ≤-refl

infixr 40 _◀_ _▶_
infixr 2 _=⟨_⟩_ _=˘⟨_⟩_ _≤⟨_⟩_
infix  3 _≤∎
```

Additionally, we have whiskering operations, derived from the horizontal
composition operation by holding one of the operands constant:

```agda
_▶_ : (f : Hom x y) → g ≤ h → f ∘ g ≤ f ∘ h
_◀_ : f ≤ g → (h : Hom x y) → f ∘ h ≤ g ∘ h

f ▶ g = ≤-refl ◆ g
g ◀ f = g ◆ ≤-refl
```

A few lemmas about the meet operation are also in order. It,
unsurprisingly, behaves like the binary operation of a meet-semilattice:
We have that $f \le g$ is equivalently $f = f \cap g$, and $f \cap g$ is
a commutative, associative idempotent binary operation, which preserves
ordering in both of its arguments.

```agda
∩-pres-r     : g ≤ g′ → f ∩ g ≤ f ∩ g′
∩-pres-l     : f ≤ f′ → f ∩ g ≤ f′ ∩ g
∩-distribl   : f ∘ (g ∩ h) ≤ (f ∘ g) ∩ (f ∘ h)
∩-distribr   : (g ∩ h) ∘ f ≤ (g ∘ f) ∩ (h ∘ f)
∩-assoc      : (f ∩ g) ∩ h ≡ f ∩ (g ∩ h)
∩-comm       : f ∩ g ≡ g ∩ f
∩-idempotent : f ∩ f ≡ f
```

<!--
```agda
∩-pres-r w = ∩-univ ∩-le-l (≤-trans ∩-le-r w)
∩-pres-l w = ∩-univ (≤-trans ∩-le-l w) ∩-le-r
∩-distribl = ∩-univ (_ ▶ ∩-le-l) (_ ▶ ∩-le-r)
∩-distribr = ∩-univ (∩-le-l ◀ _) (∩-le-r ◀ _)
∩-assoc = ≤-antisym
  (∩-univ (≤-trans ∩-le-l ∩-le-l)
          (∩-univ (≤-trans ∩-le-l ∩-le-r) ∩-le-r))
  (∩-univ (∩-univ ∩-le-l (≤-trans ∩-le-r ∩-le-l))
          (≤-trans ∩-le-r ∩-le-r))
∩-comm = ≤-antisym (∩-univ ∩-le-r ∩-le-l) (∩-univ ∩-le-r ∩-le-l)
∩-idempotent = ≤-antisym ∩-le-l (∩-univ ≤-refl ≤-refl)
```
-->

```agda
modular′
  : ∀ {x y z} (f : Hom x y) (g : Hom y z) (h : Hom x z)
  → (g ∘ f) ∩ h ≤ (g ∩ (h ∘ f †)) ∘ f
modular′ f g h =
  (g ∘ f) ∩ h                     =˘⟨ dual _ ⟩
  ⌜ ((g ∘ f) ∩ h) † ⌝ †           =⟨ ap! (dual-∩ A) ⟩
  (⌜ (g ∘ f) † ⌝ ∩ h †) †         =⟨ ap! dual-∘ ⟩
  ⌜ ((f † ∘ g †) ∩ h †) ⌝ †       ≤⟨ dual-≤ (modular (g †) (f †) (h †)) ⟩
  (f † ∘ (g † ∩ (f † † ∘ h †))) † =⟨ dual-∘ ⟩
  (g † ∩ (f † † ∘ h †)) † ∘ f † † =⟨ ap₂ _∘_ (dual-∩ A) (dual f) ⟩
  (g † † ∩ (f † † ∘ h †) †) ∘ f   =⟨ ap₂ _∘_ (ap₂ _∩_ (dual g) (ap _† (ap₂ _∘_ (dual f) refl) ·· dual-∘ ·· ap (_∘ f †) (dual h))) refl ⟩
  (g ∩ h ∘ f †) ∘ f               ≤∎
```
