```agda
open import 1Lab.Rewrite

open import Cat.Functor.Equivalence.Path
open import Cat.Functor.Equivalence
open import Cat.Functor.Equivalence
open import Cat.Displayed.Fibre
open import Cat.Displayed.Fibre
open import Cat.Displayed.Total
open import Cat.Displayed.Total
open import Cat.Displayed.Base
open import Cat.Displayed.Base
open import Cat.Prelude

import Cat.Displayed.Reasoning as DR
import Cat.Displayed.Reasoning as DR

module Cat.Displayed.Total.Op where

open Functor
open Total-hom
```

# Total Opposites

Opposites of displayed categories are somewhat subtle, as there are
multiple constructions that one could reasonably call the "opposite".
The most obvious construction is to construct a new
displayed category over $\ca{B}op$; we call this category the
**total opposite** of $\ca{E}$.

```agda
module _ {o ℓ o′ ℓ′} {ℬ : Precategory o ℓ} (ℰ : Displayed ℬ o′ ℓ′) where
  open Precategory ℬ
  open Displayed ℰ

  _^total-op : Displayed (ℬ ^op) o′ ℓ′
  _^total-op .Displayed.Ob[_] x = Ob[ x ]
  _^total-op .Displayed.Hom[_] f x y = Hom[ f ] y x
  _^total-op .Displayed.Hom[_]-set f x y = Hom[ f ]-set y x
  _^total-op .Displayed.id′ = id′
  _^total-op .Displayed._∘′_ f′ g′ = g′ ∘′ f′
  _^total-op .Displayed.idr′ f′ = idl′ f′
  _^total-op .Displayed.idl′ f′ = idr′ f′
  _^total-op .Displayed.assoc′ f′ g′ h′ = symP $ assoc′ h′ g′ f′
```

Much like the opposite of categories, the total opposite is an involution
on displayed categories.

```agda
total-op-involution
  : ∀ {o ℓ o′ ℓ′} {ℬ : Precategory o ℓ} {ℰ : Displayed ℬ o′ ℓ′}
  → (ℰ ^total-op) ^total-op ≡ ℰ
total-op-involution {ℰ = ℰ} = path where
  open Displayed

  path : (ℰ ^total-op) ^total-op ≡ ℰ
  path i .Ob[_] = ℰ .Ob[_]
  path i .Hom[_] = ℰ .Hom[_]
  path i .Hom[_]-set = ℰ .Hom[_]-set
  path i .id′ = ℰ .id′
  path i ._∘′_ = ℰ ._∘′_
  path i .idr′ = ℰ .idr′
  path i .idl′ = ℰ .idl′
  path i .assoc′ = ℰ .assoc′

```

<!--
```agda
private
  displayed-double-dual
    : ∀ {o ℓ o′ ℓ′} {ℬ : Precategory o ℓ} {ℰ : Displayed ℬ o′ ℓ′}
    → ((ℰ ^total-op) ^total-op) ≡rw ℰ
  displayed-double-dual {ℰ = ℰ} = make-rewrite (total-op-involution {ℰ = ℰ})
  {-# REWRITE displayed-double-dual #-}
```
-->

## The Total Opposites and Total Categories

The reason we refer to this construction as the total opposite is that
its total is **equal** to the opposite of the total category!
To show this, we first need to prove some lemmas relating the morphisms
of the total category of the total opposite to those in the opposite
of the total category. These functions are essentially the identity
function, but we can't convince Agda that this is the case due to
definitional equality reasons.

```agda
total-op→total-hom
  : ∀ {o ℓ o′ ℓ′} {ℬ : Precategory o ℓ} {ℰ : Displayed ℬ o′ ℓ′}
  → ∀ {x y} → Total-hom (ℰ ^total-op) x y → Total-hom ℰ y x
total-op→total-hom f = total-hom (f .hom) (f .preserves)

total-hom→total-op
  : ∀ {o ℓ o′ ℓ′} {ℬ : Precategory o ℓ} {ℰ : Displayed ℬ o′ ℓ′}
  → ∀ {x y} → Total-hom ℰ y x → Total-hom (ℰ ^total-op) x y
total-hom→total-op f = total-hom (f .hom) (f .preserves)
```

Furthermore, these two maps constitute an equivalence, and thus yield
an equality of types via univalence.

```agda
total-op→total-hom-is-equiv
  : ∀ {o ℓ o′ ℓ′} {ℬ : Precategory o ℓ} {ℰ : Displayed ℬ o′ ℓ′}
  → ∀ {x y} → is-equiv (total-op→total-hom {ℰ = ℰ} {x = x} {y = y})
total-op→total-hom-is-equiv =
  is-iso→is-equiv $ iso total-hom→total-op (λ _ → refl) (λ _ → refl)

total-op≡total-hom
  : ∀ {o ℓ o′ ℓ′} {ℬ : Precategory o ℓ} {ℰ : Displayed ℬ o′ ℓ′}
  → ∀ {x y} → Total-hom (ℰ ^total-op) x y ≡ Total-hom ℰ y x
total-op≡total-hom = ua $ total-op→total-hom , total-op→total-hom-is-equiv
```

We can use the fact that `total-op→total-hom`{.Agda} is an equivalence
to construct an isomorphism of precategories.

```agda
∫total-op→∫^op
  : ∀ {o ℓ o′ ℓ′} {ℬ : Precategory o ℓ} (ℰ : Displayed ℬ o′ ℓ′)
  → Functor (∫ (ℰ ^total-op)) ((∫ ℰ) ^op)
∫total-op→∫^op _ .F₀ x = x
∫total-op→∫^op _ .F₁ f = total-op→total-hom f
∫total-op→∫^op _ .F-id = refl
∫total-op→∫^op _ .F-∘ _ _ = refl

∫total-op≅∫^op
  : ∀ {o ℓ o′ ℓ′} {ℬ : Precategory o ℓ} (ℰ : Displayed ℬ o′ ℓ′)
  → is-precat-iso (∫total-op→∫^op ℰ)
∫total-op≅∫^op ℰ .is-precat-iso.has-is-ff = total-op→total-hom-is-equiv
∫total-op≅∫^op ℰ .is-precat-iso.has-is-iso = id-equiv
```

Finally, we show that this extends to an equality of categories.

```agda
∫total-op≡∫^op
  : ∀ {o ℓ o′ ℓ′} {ℬ : Precategory o ℓ} (ℰ : Displayed ℬ o′ ℓ′)
  → ∫ (ℰ ^total-op) ≡ (∫ ℰ) ^op
∫total-op≡∫^op ℰ =
  Precategory-path
    (∫total-op→∫^op ℰ)
    (∫total-op≅∫^op ℰ)
```

# Total Opposites and Fibre Categories

As one would expect, the fibre categories of the total opposite of
a displayed category $\cE$ are identical to the opposites of the fibre
categories of $\cE$. The proof is quite straightforward, and boils
down to eta-expanding morphisms of fibre categories.

```agda
fibre-op→fibre-hom
  : ∀ {o ℓ o′ ℓ′} {ℬ : Precategory o ℓ} {ℰ : Displayed ℬ o′ ℓ′}
  → ∀ {x a b} → Fibre-hom (ℰ ^total-op) x a b → Fibre-hom ℰ x b a
fibre-op→fibre-hom f .base = f .base
fibre-op→fibre-hom f .is-id = f .is-id
fibre-op→fibre-hom f .vert = f .vert

fibre-hom→fibre-op
  : ∀ {o ℓ o′ ℓ′} {ℬ : Precategory o ℓ} {ℰ : Displayed ℬ o′ ℓ′}
  → ∀ {x a b} → Fibre-hom ℰ x b a → Fibre-hom (ℰ ^total-op) x a b
fibre-hom→fibre-op f .base = f .base
fibre-hom→fibre-op f .is-id = f .is-id
fibre-hom→fibre-op f .vert = f .vert

fibre-op→fibre-hom-is-equiv
  : ∀ {o ℓ o′ ℓ′} {ℬ : Precategory o ℓ} {ℰ : Displayed ℬ o′ ℓ′} {x} {a} {b}
  → is-equiv (fibre-op→fibre-hom {ℰ = ℰ} {x = x} {a = a} {b = b})
fibre-op→fibre-hom-is-equiv =
  is-iso→is-equiv $ iso
    fibre-hom→fibre-op
    (λ _ → Fibre-hom-path _ _ refl refl)
    (λ _ → Fibre-hom-path _ _ refl refl)

fibre-op→fibre^op
  : ∀ {o ℓ o′ ℓ′} {ℬ : Precategory o ℓ} (ℰ : Displayed ℬ o′ ℓ′) x
  → Functor (Fibre (ℰ ^total-op) x) ((Fibre ℰ x) ^op)
fibre-op→fibre^op _ _ .F₀ a = a
fibre-op→fibre^op _ _ .F₁ = fibre-op→fibre-hom
fibre-op→fibre^op _ _ .F-id = Fibre-hom-path _ _ refl refl
fibre-op→fibre^op _ _ .F-∘ f g = Fibre-hom-path _ _ refl refl

fibre-op≅fibre^op
  : ∀ {o ℓ o′ ℓ′} {ℬ : Precategory o ℓ} (ℰ : Displayed ℬ o′ ℓ′) x
  → is-precat-iso (fibre-op→fibre^op ℰ x)
fibre-op≅fibre^op _ _ .is-precat-iso.has-is-ff = fibre-op→fibre-hom-is-equiv
fibre-op≅fibre^op _ _ .is-precat-iso.has-is-iso = id-equiv

fibre-op≡fibre^op
  : ∀ {o ℓ o′ ℓ′} {ℬ : Precategory o ℓ} (ℰ : Displayed ℬ o′ ℓ′) x
  → Fibre (ℰ ^total-op) x ≡ Fibre ℰ x ^op
fibre-op≡fibre^op ℰ x =
  Precategory-path
    (fibre-op→fibre^op ℰ x)
    (fibre-op≅fibre^op ℰ x)
```
