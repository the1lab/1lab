<!--
```agda
open import Cat.Prelude

open import Order.Diagram.Lub.Reasoning
open import Order.Lattice.Distributive
open import Order.Semilattice.Join
open import Order.Semilattice.Meet
open import Order.Diagram.Glb
open import Order.Diagram.Lub
open import Order.Lattice
open import Order.Frame
open import Order.Base

import Order.Semilattice.Join.Reasoning
import Order.Semilattice.Meet.Reasoning
import Order.Lattice.Reasoning
import Order.Reasoning
```
-->

```agda
module Order.Frame.Reasoning {o ℓ} {P : Poset o ℓ} (frm : is-frame P) where
```

```agda
open Order.Reasoning P public
open is-frame frm hiding (meets ; joins) public
```

# Reasoning about frames

This module exposes a large collection of reasoning combinators for
working with frames, along with re-exporting tools for working with
the underlying lattice.

```agda
meets : Meet-semilattice o ℓ
meets = P , has-meet-slat

joins : Join-semilattice o ℓ
joins = P , has-join-slat

lattice : Lattice o ℓ
lattice = P , has-lattice

open Order.Lattice.Reasoning has-lattice using
  ( ∩-idl; ∩-idr; module ∩
  ; ∪-idl; ∪-idr; module ∪
  ; ∩-absorbl; ∩-absorbr; ∪-absorbl; ∪-absorbr
  ) public
```

This module also has further lemmas about the interplay between meets
and arbitrary joins. The following result holds in any cocomplete
lattice:

```agda
⋃-product
  : ∀ {I J : Type o} (F : I → ⌞ P ⌟) (G : J → ⌞ P ⌟)
  → ⋃ (λ i → ⋃ λ j → G i ∩ F j)
  ≡ ⋃ {I = I × J} (λ p → F (p .fst) ∩ G (p .snd))
⋃-product {I} {J} F G = ≤-antisym
  (⋃-universal _ λ j → ⋃-universal _ λ i →
    G j ∩ F i                                       =⟨ ∩-comm ⟩
    F i ∩ G j                                       ≤⟨ ⋃-inj (i , j) ⟩
    ⋃ {I = I × J} (λ v → F (v .fst) ∩ G (v .snd)) ≤∎)
  (⋃-universal _ λ where
    (i , j) →
      F i ∩ G j                   ≤⟨ ⋃-inj i ⟩
      ⋃ (λ i → F i ∩ G j)         ≤⟨ ⋃-inj j ⟩
      ⋃ (λ i → ⋃ λ j → F j ∩ G i) =⟨ ap ⋃ (funext λ i → ap ⋃ $ funext λ j → ∩-comm) ⟩
      ⋃ (λ i → ⋃ λ j → G i ∩ F j) ≤∎)
```

But this result relies on the cocontinuity of meets.

```agda
⋃-∩-product
  : ∀ {I J : Type o} (F : I → ⌞ P ⌟) (G : J → ⌞ P ⌟)
  → ⋃ F ∩ ⋃ G
  ≡ ⋃ {I = I × J} (λ i → F (i .fst) ∩ G (i .snd))
⋃-∩-product F G =
  ⋃ F ∩ ⋃ G                         ≡⟨ ⋃-distribl (⋃ F) G ⟩
  ⋃ (λ i → ⋃ F ∩ G i)               ≡⟨ ap ⋃ (funext λ i → ∩-comm ∙ ⋃-distribl (G i) F) ⟩
  ⋃ (λ i → ⋃ λ j → G i ∩ F j)       ≡⟨ ⋃-product F G ⟩
  ⋃ (λ i → F (i .fst) ∩ G (i .snd)) ∎
```

<!--
```agda
⋃-distribr : ∀ {I} (f : I → Ob) x → ⋃ f ∩ x ≡ ⋃ λ i → f i ∩ x
⋃-distribr f x =
  ∩-comm
  ·· ⋃-distribl x f
  ·· ap ⋃ (funext λ _ → ∩-comm)
```
-->

Meets distribute over binary joins, so every frame is a
[[distributive lattice]].

```agda
opaque
  unfolding Lubs._∪_
  ∩-distribl : ∀ {x y z} → x ∩ (y ∪ z) ≡ (x ∩ y) ∪ (x ∩ z)
  ∩-distribl  =
    ⋃-distribl _ _
    ∙ ap ⋃ (funext (λ { (lift true) → refl ; (lift false) → refl }))

open Distributive.from-∩ has-lattice ∩-distribl public
```
