<!--
```agda
open import Algebra.Semigroup
open import Algebra.Magma

open import Cat.Prelude

open import Order.Diagram.Join
open import Order.Diagram.Glb
open import Order.Diagram.Lub
open import Order.Base

import Order.Diagram.Join.Reasoning as Joins
import Order.Diagram.Bottom
import Order.Reasoning
```
-->

```agda
module Order.Diagram.Lub.Reasoning {o ℓ} (P : Poset o ℓ) where
```

<!--
```agda
open Order.Reasoning P
open Order.Diagram.Bottom P
```
-->

# Reasoning about least upper bounds

This module provides syntax and reasoning combinators for working with
[[partial orders]] that have all [[least upper bounds]].

```agda
module Lubs
  {⋃      : ∀ {I : Type o} (f : I → Ob) → Ob}
  (⋃-lubs : ∀ {I : Type o} (f : I → Ob) → is-lub P f (⋃ f))
  where

  lubs : ∀ {I : Type o} (f : I → Ob) → Lub P f
  lubs f = record { lub = ⋃ f ; has-lub = ⋃-lubs f }

  module ⋃-lubs {I} {f : I → Ob} = is-lub (⋃-lubs f)
  open ⋃-lubs using () renaming (fam≤lub to ⋃-inj; least to ⋃-universal) public
```

Performing two nested joins over $I$ and $J$ is the same as taking a
single join over $\Sigma I J$.

```agda
  ⋃-twice
    : ∀ {I : Type o} {J : I → Type o} (F : (i : I) → J i → Ob)
    → ⋃ (λ i → ⋃ λ j → F i j)
    ≡ ⋃ {I = Σ I J} (λ p → F (p .fst) (p .snd))
  ⋃-twice F = ≤-antisym
    (⋃-universal _ (λ i → ⋃-universal _ (λ j → ⋃-inj _)))
    (⋃-universal _ λ (i , j) → ≤-trans (⋃-inj j) (⋃-inj i))
```

Let $f : I \to P$ and $g : J \to P$ be a pair of families. If there is
a map $t : I \to J$ such that $f_{i} \leq g_{t(i)}$, then the meet of $f$
is smaller than the meet of $g$.

```agda
  ⋃≤⋃-over
    : ∀ {I J : Type o} {f : I → Ob} {g : J → Ob}
    → (to : I → J)
    → (∀ i → f i ≤ g (to i))
    → ⋃ f ≤ ⋃ g
  ⋃≤⋃-over to p = ⋃-universal _ λ i → ≤-trans (p i) (⋃-inj (to i))
```

As a corollary, if $f : I \to P$ is smaller than $g : I \to P$ for each
$i : I$, then the join of $f$ is smaller than the join of $g$.

```agda
  ⋃≤⋃
    : ∀ {I : Type o} {f g : I → Ob}
    → (∀ i → f i ≤ g i)
    → ⋃ f ≤ ⋃ g
  ⋃≤⋃ = ⋃≤⋃-over (λ i → i)
```

Taking the join over a [[contractible]] family is equal the unique value
of the family.

```agda
  ⋃-singleton
    : ∀ {I : Type o} {f : I → Ob}
    → (p : is-contr I)
    → ⋃ f ≡ f (p .centre)
  ⋃-singleton {f = f} p = ≤-antisym
    (⋃-universal _ λ i → ≤-refl' $ sym $ ap f (p .paths i))
    (⋃-inj _)
```

We also provide syntax for binary joins and bottom elements.

```agda
  module _ (x y : Ob) where opaque
    private
      it : Join P x y
      it = Lub→Join (lower-lub (lubs _))

    infixr 24 _∪_
    _∪_ : Ob
    _∪_ = it .Join.lub

    ∪-joins : is-join P x y _∪_
    ∪-joins = it .Join.has-join

  opaque
    has-bottom : Bottom
    has-bottom = Lub→Bottom (lower-lub (lubs (λ ())))

  open Joins ∪-joins public
  open Bottom has-bottom using (bot; ¡) public
```

There is a distributive law relating binary and infinitary joins.

```agda
  ∪-distrib-⋃-≤l
    : ∀ {I : Type o} {x : Ob} {f : I → Ob}
    → ⋃ (λ i → x ∪ f i) ≤ x ∪ ⋃ f
  ∪-distrib-⋃-≤l =
    ⋃-universal _ λ i → ∪-universal _ l≤∪ (≤-trans (⋃-inj i) r≤∪)
```

If the infinitary join is taken over a non-empty family, then the previous
distributive law can be extended to an equality.

```agda
  ∪-distrib-nonempty-⋃-l
    : ∀ {I : Type o} {x : Ob} {f : I → Ob}
    → ∥ I ∥
    → ⋃ (λ i → x ∪ f i) ≡ x ∪ ⋃ f
  ∪-distrib-nonempty-⋃-l i =
    ≤-antisym
      ∪-distrib-⋃-≤l
      (rec! (λ i → ∪-universal _ (≤-trans l≤∪ (⋃-inj i)) (⋃≤⋃ λ _ → r≤∪)) i)
```

<!--
```agda
  ⋃-ap
    : ∀ {I I' : Type o} {f : I → Ob} {g : I' → Ob}
    → (e : I ≃ I')
    → (∀ i → f i ≡ g (e .fst i))
    → ⋃ f ≡ ⋃ g
  ⋃-ap e p = ap₂ (λ I f → ⋃ {I = I} f) (ua e) (ua→ p)

  -- raised i for "index", raised f for "family"
  ⋃-apⁱ : ∀ {I I' : Type o} {f : I' → Ob} (e : I ≃ I') → ⋃ (λ i → f (e .fst i)) ≡ ⋃ f
  ⋃-apᶠ : ∀ {I : Type o} {f g : I → Ob} → (∀ i → f i ≡ g i) → ⋃ f ≡ ⋃ g

  ⋃-apⁱ e = ⋃-ap e (λ i → refl)
  ⋃-apᶠ p = ⋃-ap (_ , id-equiv) p
```
-->

## Large joins

Let $P$ be a $\kappa$-small poset. If $P$ has all joins of size $\kappa$,
then it has all joins, regardless of size.

```agda
is-cocomplete→is-large-cocomplete
  : (lubs : ∀ {I : Type o} (f : I → Ob) → Lub P f)
  → ∀ {ℓ} {I : Type ℓ} (F : I → Ob) → Lub P F
is-cocomplete→is-large-cocomplete lubs {I = I} F =
  cover-preserves-lub
    (Ω-corestriction-is-surjective F)
    (lubs fst)
```

We also provide some notation for large joins.

```agda
module
  Large
    {⋃ : {I : Type o} (F : I → Ob) → Ob}
    (⋃-lubs : ∀ {I} f → is-lub P f (⋃ {I} f))
  where

  open Lubs ⋃-lubs using (lubs)

  opaque
    ⋃ᴸ : ∀ {ℓ} {I : Type ℓ} (F : I → Ob) → Ob
    ⋃ᴸ F = is-cocomplete→is-large-cocomplete lubs F .Lub.lub

    ⋃ᴸ-inj : ∀ {ℓ} {I : Type ℓ} {F : I → Ob} (i : I) → F i ≤ ⋃ᴸ F
    ⋃ᴸ-inj = Lub.fam≤lub (is-cocomplete→is-large-cocomplete lubs _)

    ⋃ᴸ-universal : ∀ {ℓ} {I : Type ℓ} {F : I → Ob} (x : Ob) → (∀ i → F i ≤ x) → ⋃ᴸ F ≤ x
    ⋃ᴸ-universal = Lub.least (is-cocomplete→is-large-cocomplete lubs _)
```

<!--
```agda
  ⋃ᴸ-ap
    : ∀ {ℓ ℓ'} {I : Type ℓ} {I' : Type ℓ'} {f : I → Ob} {g : I' → Ob}
    → (e : I ≃ I')
    → (∀ i → f i ≡ g (e .fst i))
    → ⋃ᴸ f ≡ ⋃ᴸ g
  ⋃ᴸ-ap {g = g} e p = ≤-antisym
    (⋃ᴸ-universal _ λ i → ≤-trans (≤-refl' (p i)) (⋃ᴸ-inj _))
    (⋃ᴸ-universal _ λ i → ≤-trans (≤-refl' (ap g (sym (Equiv.ε e i)) ∙ sym (p (Equiv.from e _)))) (⋃ᴸ-inj _))

  -- raised i for "index", raised f for "family"
  ⋃ᴸ-apⁱ : ∀ {ℓ ℓ'} {I : Type ℓ} {I' : Type ℓ'} {f : I' → Ob} (e : I ≃ I') → ⋃ᴸ (λ i → f (e .fst i)) ≡ ⋃ᴸ f
  ⋃ᴸ-apᶠ : ∀ {ℓ} {I : Type ℓ} {f g : I → Ob} → (∀ i → f i ≡ g i) → ⋃ᴸ f ≡ ⋃ᴸ g

  ⋃ᴸ-apⁱ e = ⋃ᴸ-ap e (λ i → refl)
  ⋃ᴸ-apᶠ p = ⋃ᴸ-ap (_ , id-equiv) p
```
-->
