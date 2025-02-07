<!--
```agda
open import Algebra.Semigroup
open import Algebra.Magma

open import Cat.Prelude

open import Data.Bool

open import Order.Diagram.Meet
open import Order.Diagram.Glb
open import Order.Base

import Order.Diagram.Meet.Reasoning as Meets
import Order.Diagram.Top
import Order.Reasoning
```
-->

```agda
module Order.Diagram.Glb.Reasoning {o ℓ} (P : Poset o ℓ) where
```

<!--
```agda
open Order.Diagram.Top P
open Order.Reasoning P
```
-->

# Reasoning about greatest lower bounds

This module provides syntax and reasoning combinators for working with
[[partial orders]] that have all [[greatest lower bounds]].

```agda
module Glbs
  {⋂      : ∀ {I : Type o} (f : I → Ob) → Ob}
  (⋂-glbs : ∀ {I : Type o} (f : I → Ob) → is-glb P f (⋂ f))
  where

  glbs : ∀ {I : Type o} (f : I → Ob) → Glb P f
  glbs f = record { glb = ⋂ f ; has-glb = ⋂-glbs f }

  module glbs {I} {f : I → Ob} = Glb (glbs f)
  open glbs using () renaming (glb≤fam to ⋂-proj; greatest to ⋂-universal) public
```

Performing two nested meets over $I$ and $J$ is the same as taking a
single meet over $\Sigma I J$.

```agda
  ⋂-twice
    : ∀ {I : Type o} {J : I → Type o} (f : (i : I) → J i → Ob)
    → ⋂ (λ i → ⋂ λ j → f i j)
    ≡ ⋂ {I = Σ I J} (λ p → f (p .fst) (p .snd))
  ⋂-twice f =
    ≤-antisym
      (⋂-universal _ (λ (i , j) → ≤-trans (⋂-proj i) (⋂-proj {f = f i} j)))
      (⋂-universal _ λ i → ⋂-universal _ λ j → ⋂-proj (i , j))
```

Let $f : J \to P$ and $g : I \to P$ be a pair of families. If there is
a map $t : I \to J$ such that $f_{t(i)} \leq g_{i}$, then the meet of $f$
is smaller than the meet of $g$.

```agda
  ⋂≤⋂-over
    : ∀ {I J : Type o} {f : J → Ob} {g : I → Ob}
    → (to : I → J)
    → (∀ i → f (to i) ≤ g i)
    → ⋂ f ≤ ⋂ g
  ⋂≤⋂-over to p =  ⋂-universal _ λ i → ≤-trans (⋂-proj (to i)) (p i)
```

As a corollary, if $f : I \to P$ is smaller than $g : I \to P$ for each
$i : I$, then the meet of $f$ is smaller than the meet of $g$.

```agda
  ⋂≤⋂
    : {I : Type o} {f g : I → Ob}
    → (∀ i → f i ≤ g i)
    → ⋂ f ≤ ⋂ g
  ⋂≤⋂ p = ⋂≤⋂-over (λ i → i) p
```

Taking the meet over a [[contractible]] family is equal the unique value
of the family.

```agda
  ⋂-singleton
    : ∀ {I : Type o} {f : I → Ob}
    → (p : is-contr I)
    → ⋂ f ≡ f (p .centre)
  ⋂-singleton {f = f} p = ≤-antisym
    (⋂-proj (p .centre))
    (⋂-universal _ λ i → ≤-refl' (ap f (p .paths i)))
```

We also provide syntax for binary meets and top elements.

```agda
  module _ (x y : Ob) where opaque
    private
      it : Meet P x y
      it = Glb→Meet (lower-glb (glbs _))

    infixr 25 _∩_
    _∩_ : Ob
    _∩_ = it .Meet.glb

    ∩-meets : is-meet P x y _∩_
    ∩-meets = it .Meet.has-meet

  opaque
    has-top : Top
    has-top = Glb→Top (lower-glb (glbs (λ ())))

  open Meets ∩-meets public
  open Top has-top using (top; !) public
```

There is a distributive law relating binary and infinitary meets.

```agda
  ∩-distrib-⋂-≤l
    : ∀ {I : Type o} {x : Ob} {f : I → Ob}
    → x ∩ ⋂ f ≤ ⋂ λ i → x ∩ f i
  ∩-distrib-⋂-≤l =
    (⋂-universal _ λ i → ∩-universal _ ∩≤l (≤-trans ∩≤r (⋂-proj i)))
```

If the infinitary meet is taken over a non-empty family, then the previous
distributive law can be extended to an equality.

```agda
  ∩-distrib-nonempty-⋂-l
    : ∀ {I : Type o} {x : Ob} {f : I → Ob}
    → ∥ I ∥
    → x ∩ ⋂ f ≡ ⋂ λ i → x ∩ f i
  ∩-distrib-nonempty-⋂-l i =
    ≤-antisym
     ∩-distrib-⋂-≤l
     (rec! (λ i → ∩-universal _ (≤-trans (⋂-proj i) ∩≤l) (⋂≤⋂ λ _ → ∩≤r)) i)
```

<!--
```agda
  ⋂-ap
    : ∀ {I I' : Type o} {f : I → Ob} {g : I' → Ob}
    → (e : I ≃ I')
    → (∀ i → f i ≡ g (e .fst i))
    → ⋂ f ≡ ⋂ g
  ⋂-ap e p = ap₂ (λ I f → ⋂ {I = I} f) (ua e) (ua→ p)

  -- raised i for "index", raised f for "family"
  ⋂-apⁱ : ∀ {I I' : Type o} {f : I' → Ob} (e : I ≃ I') → ⋂ (λ i → f (e .fst i)) ≡ ⋂ f
  ⋂-apᶠ : ∀ {I : Type o} {f g : I → Ob} → (∀ i → f i ≡ g i) → ⋂ f ≡ ⋂ g

  ⋂-apⁱ e = ⋂-ap e (λ i → refl)
  ⋂-apᶠ p = ⋂-ap (_ , id-equiv) p

```
-->

## Large meets

Let $P$ be a $\kappa$-small poset. If $P$ has all meets of size $\kappa$,
then it has all meets, regardless of size.

```agda
is-complete→is-large-complete
  : (glbs : ∀ {I : Type o} (f : I → Ob) → Glb P f)
  → ∀ {ℓ} {I : Type ℓ} (F : I → Ob) → Glb P F
is-complete→is-large-complete glbs {I = I} F =
  cover-preserves-glb
    (Ω-corestriction-is-surjective F)
    (glbs fst)
```

We also provide some notation for large meets.

```agda
module
  Large
    {⋂      : ∀ {I : Type o} (f : I → Ob) → Ob}
    (⋂-glbs : ∀ {I : Type o} (f : I → Ob) → is-glb P f (⋂ f))
  where

  open Glbs ⋂-glbs using (glbs)

  opaque
    ⋂ᴸ : ∀ {ℓ} {I : Type ℓ} (F : I → Ob) → Ob
    ⋂ᴸ F = is-complete→is-large-complete glbs F .Glb.glb

    ⋂ᴸ-proj : ∀ {ℓ} {I : Type ℓ} {F : I → Ob} (i : I) → ⋂ᴸ F ≤ F i
    ⋂ᴸ-proj = Glb.glb≤fam (is-complete→is-large-complete glbs _)

    ⋂ᴸ-universal : ∀ {ℓ} {I : Type ℓ} {F : I → Ob} (x : Ob) → (∀ i → x ≤ F i) → x ≤ ⋂ᴸ F
    ⋂ᴸ-universal = Glb.greatest (is-complete→is-large-complete glbs _)
```

<!--
```agda
  ⋂ᴸ-ap
    : ∀ {ℓ ℓ'} {I : Type ℓ} {I' : Type ℓ'} {f : I → Ob} {g : I' → Ob}
    → (e : I ≃ I')
    → (∀ i → f i ≡ g (e .fst i))
    → ⋂ᴸ f ≡ ⋂ᴸ g
  ⋂ᴸ-ap {g = g} e p = ≤-antisym
    (⋂ᴸ-universal _ λ i → ≤-trans (⋂ᴸ-proj (Equiv.from e i)) (≤-refl' (p _ ∙ ap g (Equiv.ε e i))))
    (⋂ᴸ-universal _ λ i → ≤-trans (⋂ᴸ-proj (Equiv.to e i)) (≤-refl' (sym (p i))))

  -- raised i for "index", raised f for "family"
  ⋂ᴸ-apⁱ : ∀ {ℓ ℓ'} {I : Type ℓ} {I' : Type ℓ'} {f : I' → Ob} (e : I ≃ I') → ⋂ᴸ (λ i → f (e .fst i)) ≡ ⋂ᴸ f
  ⋂ᴸ-apᶠ : ∀ {ℓ} {I : Type ℓ} {f g : I → Ob} → (∀ i → f i ≡ g i) → ⋂ᴸ f ≡ ⋂ᴸ g

  ⋂ᴸ-apⁱ e = ⋂ᴸ-ap e (λ i → refl)
  ⋂ᴸ-apᶠ p = ⋂ᴸ-ap (_ , id-equiv) p
```
-->
