<!--
```agda
open import Cat.Allegory.Base
open import Cat.Prelude

import Cat.Reasoning
```
-->

```agda
module Cat.Allegory.Reasoning {o ℓ ℓ'} (A : Allegory o ℓ ℓ') where
```

<!--
```agda
open Allegory A public
open Cat.Reasoning (A .Allegory.cat)
  hiding (module HLevel-instance ; Ob ; Hom ; Hom-set ; id ; idl ; idr ; assoc ; _∘_)
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
  a b c d f f' g g' h i : Hom x y

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
∩-pres-r     : g ≤ g' → f ∩ g ≤ f ∩ g'
∩-pres-l     : f ≤ f' → f ∩ g ≤ f' ∩ g
∩-pres     : f ≤ f' → g ≤ g' → f ∩ g ≤ f' ∩ g'
∩-distribl   : f ∘ (g ∩ h) ≤ (f ∘ g) ∩ (f ∘ h)
∩-distribr   : (g ∩ h) ∘ f ≤ (g ∘ f) ∩ (h ∘ f)
∩-distrib   : (f ∩ g) ∘ (h ∩ i) ≤ (f ∘ h ∩ g ∘ h) ∩ (f ∘ i ∩ g ∘ i)
∩-assoc      : (f ∩ g) ∩ h ≡ f ∩ (g ∩ h)
∩-comm       : f ∩ g ≡ g ∩ f
∩-idempotent : f ∩ f ≡ f
```

<!--
```agda
∩-pres-r w = ∩-univ ∩-le-l (≤-trans ∩-le-r w)
∩-pres-l w = ∩-univ (≤-trans ∩-le-l w) ∩-le-r
∩-pres w v = ∩-univ (≤-trans ∩-le-l w) (≤-trans ∩-le-r v)
∩-distribl = ∩-univ (_ ▶ ∩-le-l) (_ ▶ ∩-le-r)
∩-distribr = ∩-univ (∩-le-l ◀ _) (∩-le-r ◀ _)
∩-distrib = ≤-trans ∩-distribl (∩-pres ∩-distribr ∩-distribr)
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
modular'
  : ∀ {x y z} (f : Hom x y) (g : Hom y z) (h : Hom x z)
  → (g ∘ f) ∩ h ≤ (g ∩ (h ∘ f †)) ∘ f
modular' f g h =
  (g ∘ f) ∩ h                     =˘⟨ dual _ ⟩
  ⌜ ((g ∘ f) ∩ h) † ⌝ †           =⟨ ap! (dual-∩ A) ⟩
  (⌜ (g ∘ f) † ⌝ ∩ h †) †         =⟨ ap! dual-∘ ⟩
  ⌜ ((f † ∘ g †) ∩ h †) ⌝ †       ≤⟨ dual-≤ (modular (g †) (f †) (h †)) ⟩
  (f † ∘ (g † ∩ (f † † ∘ h †))) † =⟨ dual-∘ ⟩
  (g † ∩ (f † † ∘ h †)) † ∘ f † † =⟨ ap₂ _∘_ (dual-∩ A) (dual f) ⟩
  (g † † ∩ (f † † ∘ h †) †) ∘ f   =⟨ ap₂ _∘_ (ap₂ _∩_ (dual g) (ap _† (ap₂ _∘_ (dual f) refl) ·· dual-∘ ·· ap (_∘ f †) (dual h))) refl ⟩
  (g ∩ h ∘ f †) ∘ f               ≤∎
```

## Identities

```agda
abstract
  ≤-eliml : f ≤ id → f ∘ g ≤ g
  ≤-eliml {f = f} {g = g} w =
    f ∘ g  ≤⟨ w ◀ g ⟩
    id ∘ g =⟨ idl _ ⟩
    g ≤∎

  ≤-elimr : g ≤ id → f ∘ g ≤ f
  ≤-elimr {g = g} {f = f} w =
    f ∘ g  ≤⟨ f ▶ w ⟩
    f ∘ id =⟨ idr _ ⟩
    f ≤∎

  ≤-introl : id ≤ f → g ≤ f ∘ g
  ≤-introl {f = f} {g = g} w =
    g      =⟨ sym (idl _) ⟩
    id ∘ g ≤⟨ w ◀ g ⟩
    f ∘ g  ≤∎

  ≤-intror : id ≤ g → f ≤ f ∘ g
  ≤-intror {g = g} {f = f} w =
    f      =⟨ sym (idr _) ⟩
    f ∘ id ≤⟨ f ▶ w ⟩
    f ∘ g  ≤∎
```

## Associations

```agda
  ≤-pushl : a ≤ b ∘ c → a ∘ f ≤ b ∘ c ∘ f
  ≤-pushl {a = a} {b = b} {c = c} {f = f} w =
    a ∘ f       ≤⟨ w ◀ f ⟩
    (b ∘ c) ∘ f =⟨ sym (assoc b c f) ⟩
    b ∘ c ∘ f   ≤∎

  ≤-pushr : a ≤ b ∘ c → f ∘ a ≤ (f ∘ b) ∘ c
  ≤-pushr {a = a} {b = b} {c = c} {f = f}  w =
    f ∘ a       ≤⟨ f ▶ w ⟩
    f ∘ b ∘ c   =⟨ assoc f b c ⟩
    (f ∘ b) ∘ c ≤∎

  ≤-pulll : a ∘ b ≤ c → a ∘ b ∘ f ≤ c ∘ f
  ≤-pulll {a = a} {b = b} {c = c} {f = f} w =
    a ∘ b ∘ f   =⟨ assoc a b f ⟩
    (a ∘ b) ∘ f ≤⟨ w ◀ f ⟩
    c ∘ f       ≤∎

  ≤-pullr : a ∘ b ≤ c → (f ∘ a) ∘ b ≤ f ∘ c
  ≤-pullr {a = a} {b = b} {c = c} {f = f} w =
    (f ∘ a) ∘ b   =⟨ sym (assoc f a b) ⟩
    f ∘ a ∘ b     ≤⟨ f ▶ w ⟩
    f ∘ c         ≤∎

  ≤-extendl : a ∘ b ≤ c ∘ d → a ∘ b ∘ f ≤ c ∘ d ∘ f
  ≤-extendl {a = a} {b = b} {c = c} {d = d} {f = f} w =
    a ∘ b ∘ f   ≤⟨ ≤-pulll w ⟩
    (c ∘ d) ∘ f =⟨ sym (assoc c d f) ⟩
    c ∘ d ∘ f   ≤∎

  ≤-extendr : a ∘ b ≤ c ∘ d → (f ∘ a) ∘ b ≤ (f ∘ c) ∘ d
  ≤-extendr {a = a} {b = b} {c = c} {d = d} {f = f} w =
    (f ∘ a) ∘ b ≤⟨ ≤-pullr w ⟩
    f ∘ c ∘ d   =⟨ assoc f c d ⟩
    (f ∘ c) ∘ d ≤∎

  ≤-pull-inner : a ∘ b ≤ c → (f ∘ a) ∘ (b ∘ g) ≤ f ∘ c ∘ g
  ≤-pull-inner w = ≤-pullr (≤-pulll w)

  ≤-pull-outer : a ∘ b ≤ f → c ∘ d ≤ g → a ∘ (b ∘ c) ∘ d ≤ f ∘ g
  ≤-pull-outer w v = ≤-trans (≤-pulll (≤-pulll w)) (≤-pullr v)

  ≤-extend-inner : a ∘ b ≤ c ∘ d → (f ∘ a) ∘ (b ∘ g) ≤ (f ∘ c) ∘ (d ∘ g)
  ≤-extend-inner w = ≤-extendr (≤-extendl w)
```

## Cancellations

```agda
  ≤-cancell : a ∘ b ≤ id → a ∘ b ∘ f ≤ f
  ≤-cancell w = ≤-trans (≤-pulll w) (≤-eliml ≤-refl)

  ≤-cancelr : a ∘ b ≤ id → (f ∘ a) ∘ b ≤ f
  ≤-cancelr w = ≤-trans (≤-pullr w) (≤-elimr ≤-refl)
```


## Duals

```agda
  ≤-conj : ∀ (f : Hom x x) → f ≤ f ∘ f † ∘ f
  ≤-conj f =
    f                    ≤⟨ ∩-univ (≤-introl ≤-refl) ≤-refl ⟩
    (id ∘ f) ∩ f         ≤⟨ modular' f id f ⟩
    (id ∩ (f ∘ f †)) ∘ f ≤⟨ ≤-pushl ∩-le-r ⟩
    f ∘ f † ∘ f ≤∎

  †-pulll : a ∘ b † ≤ c → a ∘ (f ∘ b) † ≤ c ∘ f †
  †-pulll {a = a} {b = b} {c = c} {f = f} w =
    a ∘ (f ∘ b) † =⟨ ap (a ∘_) dual-∘ ⟩
    a ∘ b † ∘ f † ≤⟨ ≤-pulll w ⟩
    c ∘ f † ≤∎

  †-pullr : a † ∘ b ≤ c → (a ∘ f) † ∘ b ≤ f † ∘ c
  †-pullr {a = a} {b = b} {c = c} {f = f} w =
    (a ∘ f) † ∘ b =⟨ ap (_∘ b) dual-∘ ⟩
    (f † ∘ a †) ∘ b ≤⟨ ≤-pullr w ⟩
    f † ∘ c ≤∎

  †-inner : (p : g ∘ g' † ≡ h) → (f ∘ g) ∘ (f' ∘ g') † ≡ f ∘ h ∘ f' †
  †-inner p = ap₂ _∘_ refl dual-∘ ∙ sym (assoc _ _ _)
            ∙ ap₂ _∘_ refl (assoc _ _ _ ∙ ap₂ _∘_ p refl)

  †-cancell : a ∘ b † ≤ id → a ∘ (f ∘ b) † ≤ f †
  †-cancell w = ≤-trans (†-pulll w) (≤-eliml ≤-refl)

  †-cancelr : a † ∘ b ≤ id → (a ∘ f) † ∘ b ≤ f †
  †-cancelr w = ≤-trans (†-pullr w) (≤-elimr ≤-refl)

  †-cancel-inner : a ∘ b † ≤ id → (f ∘ a) ∘ (g ∘ b) † ≤ f ∘ g †
  †-cancel-inner w = †-pulll (≤-cancelr w)
```
