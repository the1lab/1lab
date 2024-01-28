<!--
```agda
open import Cat.Instances.Shape.Interval
open import Cat.Instances.Discrete
open import Cat.Prelude

open import Data.Fin.Finite

open Precategory
```
-->

```agda
module Cat.Finite where
```

# Finite precategories {defines="finite-precategory finite-category"}

A precategory is **finite** if both its type of objects and its total space of
morphisms are [[finite]].

```agda
record is-finite-precategory {o ℓ} (D : Precategory o ℓ) : Type (o ⊔ ℓ) where
  constructor finite-cat
  field
    ⦃ has-finite-Ob ⦄ : Finite (Ob D)
    ⦃ has-finite-Arrows ⦄ : Finite (Arrows D)

open is-finite-precategory
```

<!--
```agda
_ = Finite-Σ
_ = Finite-PathP
```
-->

Conveniently, because finite types are `closed`{.Agda ident=Finite-Σ} under
`Σ`{.Agda}, it suffices that each `Hom`{.Agda} set be finite:

```agda
finite-cat-hom
  : ∀ {o ℓ} {D : Precategory o ℓ}
  → ⦃ Finite (Ob D) ⦄
  → (∀ a b → Finite (Hom D a b))
  → is-finite-precategory D
finite-cat-hom {D = D} f = finite-cat where
  instance
    finite-Hom : ∀ {a b} → Finite (Hom D a b)
    finite-Hom {a} {b} = f a b
```

Thanks to even more instance magic (`path types of a finite type are
finite`{.Agda ident=Finite-PathP}), the [[discrete category]] on a
finite set is finite:

```agda
Disc-finite : ∀ {ℓ} {A : Type ℓ} {isg : is-groupoid A} → ⦃ Finite A ⦄
            → is-finite-precategory (Disc A isg)
Disc-finite = finite-cat
```
