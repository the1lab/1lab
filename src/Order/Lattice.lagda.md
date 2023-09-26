<!--
```agda
open import Cat.Displayed.Total
open import Cat.Functor.Subcategory
open import Cat.Prelude

open import Order.Diagram.Glb
open import Order.Diagram.Lub
open import Order.Semilattice
open import Order.Base

import Cat.Reasoning

import Order.Reasoning as Poset
```
-->

```agda
module Order.Lattice where
```

# Lattices

```agda
module _ {o ℓ} (X : Poset o ℓ) where
  open Poset X

  record is-lattice : Type (o ⊔ ℓ) where
    no-eta-equality
    field
      has-is-meet-semilattice : is-meet-semilattice X
      has-is-join-semilattice : is-join-semilattice X

    open is-meet-semilattice has-is-meet-semilattice public
    open is-join-semilattice has-is-join-semilattice public

    ∩-absorbs-∪ : ∀ x y → x ∩ (x ∪ y) ≡ x
    ∩-absorbs-∪ _ _ =
      ≤-antisym
        (∩≤l _ _)
        (∩-universal _ _ _ ≤-refl (l≤∪ _ _))

    ∪-absorbs-∩ : ∀ x y → x ∪ (x ∩ y) ≡ x
    ∪-absorbs-∩ _ _ =
      ≤-antisym
        (∪-universal _ _ _ ≤-refl (∩≤l _ _))
        (l≤∪ _ _)
```

<!--
```agda
  is-lattice-is-prop : is-prop is-lattice
  is-lattice-is-prop = Iso→is-hlevel 1 eqv $
    ×-is-hlevel 1
      (is-meet-semilattice-is-prop X)
      (is-join-semilattice-is-prop X)
    where unquoteDecl eqv = declare-record-iso eqv (quote is-lattice)
```
-->

# Morphisms of Lattices

```agda
module _ {o ℓ} {X Y : Poset o ℓ} where

  record preserves-finite-meets-and-joins (f : Posets.Hom X Y) : Type (o ⊔ ℓ) where
    no-eta-equality
    field
      pres-finite-meets : preserves-finite-meets f
      pres-finite-joins : preserves-finite-joins f
```

<!--
```agda
  preserves-finite-meets-and-joins-is-prop
    : (f : Posets.Hom X Y)
    → is-prop (preserves-finite-meets-and-joins f)
  preserves-finite-meets-and-joins-is-prop f = Iso→is-hlevel 1 eqv $
    ×-is-hlevel 1 (preserves-finite-meets-is-prop f) (preserves-finite-joins-is-prop f)
    where unquoteDecl eqv = declare-record-iso eqv (quote preserves-finite-meets-and-joins) 
    
```
-->

<!--
```agda
module _ where
  open Total-hom
  open preserves-finite-meets-and-joins

  preserves-finite-meets-and-joins-id
    : ∀ {o ℓ} {X : Poset o ℓ}
    → preserves-finite-meets-and-joins (Posets.id {x = X})
  preserves-finite-meets-and-joins-id .pres-finite-meets =
    preserves-finite-meets-id 
  preserves-finite-meets-and-joins-id .pres-finite-joins =
    preserves-finite-joins-id

  preserves-finite-meets-and-joins-∘
    : ∀ {o ℓ} {X Y Z : Poset o ℓ}
    → {f : Posets.Hom Y Z} {g : Posets.Hom X Y}
    → preserves-finite-meets-and-joins f → preserves-finite-meets-and-joins g
    → preserves-finite-meets-and-joins (f Posets.∘ g)
  preserves-finite-meets-and-joins-∘ p q .pres-finite-meets =
    preserves-finite-meets-∘ (p .pres-finite-meets) (q .pres-finite-meets)
  preserves-finite-meets-and-joins-∘ p q .pres-finite-joins =
    preserves-finite-joins-∘ (p .pres-finite-joins) (q .pres-finite-joins)
```
-->

# The category of lattices

```agda
Lattices-subcat : ∀ o ℓ → Subcat (Posets o ℓ) (o ⊔ ℓ) (o ⊔ ℓ)
Lattices-subcat o ℓ .Subcat.is-ob = is-lattice
Lattices-subcat o ℓ .Subcat.is-hom f _ _ =
  preserves-finite-meets-and-joins f
Lattices-subcat o ℓ .Subcat.is-hom-prop f _ _ =
  preserves-finite-meets-and-joins-is-prop f
Lattices-subcat o ℓ .Subcat.is-hom-id _ =
  preserves-finite-meets-and-joins-id
Lattices-subcat o ℓ .Subcat.is-hom-∘ =
  preserves-finite-meets-and-joins-∘

Lattices : ∀ o ℓ → Precategory (lsuc (o ⊔ ℓ)) (o ⊔ ℓ)
Lattices o ℓ = Subcategory (Lattices-subcat o ℓ)

module Lattices {o} {ℓ} = Cat.Reasoning (Lattices o ℓ)

Lattice : ∀ o ℓ → Type _
Lattice o ℓ = Lattices.Ob {o} {ℓ}
```

<!--
```agda
{-# DISPLAY Lattices.Ob {o} {ℓ} = Lattice o ℓ #-}
```
-->

# Reasoning with Lattices

```agda
module Lattice {o} {ℓ} (L : Lattice o ℓ) where
  poset : Poset o ℓ
  poset = L .fst

  set : Set o
  set = L .fst .fst

  open Poset poset public

  has-is-lattice : is-lattice poset
  has-is-lattice = L .snd

  open is-lattice has-is-lattice public
```
