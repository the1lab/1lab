<!--
```agda
open import Cat.Functor.Equivalence.Path
open import Cat.Functor.Equivalence
open import Cat.Displayed.Fibre
open import Cat.Displayed.Total
open import Cat.Displayed.Base
open import Cat.Prelude

import Cat.Displayed.Reasoning as DR
```
-->

```agda
module Cat.Displayed.Total.Op where

open Functor
open ∫Hom
```

# Total opposites {defines="total-opposite"}

Opposites of [[displayed categories]] are somewhat subtle, as there are
multiple constructions that one could reasonably call the "opposite".
The most obvious construction is to construct a new displayed category
over $\ca{B}\op$; we call this category the **total opposite** of
$\ca{E}$.

```agda
module _ {o ℓ o' ℓ'} {ℬ : Precategory o ℓ} (ℰ : Displayed ℬ o' ℓ') where
  open Precategory ℬ
  open Displayed ℰ

  _^total-op : Displayed (ℬ ^op) o' ℓ'
  _^total-op .Displayed.Ob[_] x = Ob[ x ]
  _^total-op .Displayed.Hom[_] f x y = Hom[ f ] y x
  _^total-op .Displayed.Hom[_]-set f x y = Hom[ f ]-set y x
  _^total-op .Displayed.id' = id'
  _^total-op .Displayed._∘'_ f' g' = g' ∘' f'
  _^total-op .Displayed.idr' f' = idl' f'
  _^total-op .Displayed.idl' f' = idr' f'
  _^total-op .Displayed.assoc' f' g' h' = symP $ assoc' h' g' f'
  _^total-op .Displayed.hom[_] p f' = hom[ p ] f'
  _^total-op .Displayed.coh[_] p f' = coh[ p ] f'
```

## The total opposites and total categories

The reason we refer to this construction as the total opposite is that
its total is **equal** to the opposite of the [[total category]]!  To
show this, we first need to prove some lemmas relating the morphisms of
the total category of the total opposite to those in the opposite of the
total category.

```agda
total-op→total-hom
  : ∀ {o ℓ o' ℓ'} {ℬ : Precategory o ℓ} {ℰ : Displayed ℬ o' ℓ'}
  → ∀ {x y} → ∫Hom (ℰ ^total-op) x y → ∫Hom ℰ y x
total-op→total-hom f = ∫hom (f .fst) (f .snd)

total-hom→total-op
  : ∀ {o ℓ o' ℓ'} {ℬ : Precategory o ℓ} {ℰ : Displayed ℬ o' ℓ'}
  → ∀ {x y} → ∫Hom ℰ y x → ∫Hom (ℰ ^total-op) x y
total-hom→total-op f = ∫hom (f .fst) (f .snd)
```

Furthermore, these two maps constitute an equivalence, and thus yield
an equality of types via univalence.

```agda
total-op→total-hom-is-equiv
  : ∀ {o ℓ o' ℓ'} {ℬ : Precategory o ℓ} {ℰ : Displayed ℬ o' ℓ'}
  → ∀ {x y} → is-equiv (total-op→total-hom {ℰ = ℰ} {x = x} {y = y})
total-op→total-hom-is-equiv =
  is-iso→is-equiv $ iso total-hom→total-op (λ _ → refl) (λ _ → refl)

total-op≡total-hom
  : ∀ {o ℓ o' ℓ'} {ℬ : Precategory o ℓ} {ℰ : Displayed ℬ o' ℓ'}
  → ∀ {x y} → ∫Hom (ℰ ^total-op) x y ≡ ∫Hom ℰ y x
total-op≡total-hom = ua $ total-op→total-hom , total-op→total-hom-is-equiv
```

We can use the fact that `total-op→total-hom`{.Agda} is an equivalence
to construct an isomorphism of precategories.

```agda
∫total-op→∫^op
  : ∀ {o ℓ o' ℓ'} {ℬ : Precategory o ℓ} (ℰ : Displayed ℬ o' ℓ')
  → Functor (∫ (ℰ ^total-op)) ((∫ ℰ) ^op)
∫total-op→∫^op _ .F₀ x = x
∫total-op→∫^op _ .F₁ f = total-op→total-hom f
∫total-op→∫^op _ .F-id = refl
∫total-op→∫^op _ .F-∘ _ _ = refl

∫total-op≅∫^op
  : ∀ {o ℓ o' ℓ'} {ℬ : Precategory o ℓ} (ℰ : Displayed ℬ o' ℓ')
  → is-precat-iso (∫total-op→∫^op ℰ)
∫total-op≅∫^op ℰ .is-precat-iso.has-is-ff = total-op→total-hom-is-equiv
∫total-op≅∫^op ℰ .is-precat-iso.has-is-iso = id-equiv
```

Finally, we show that this extends to an equality of categories.

```agda
∫total-op≡∫^op
  : ∀ {o ℓ o' ℓ'} {ℬ : Precategory o ℓ} (ℰ : Displayed ℬ o' ℓ')
  → ∫ (ℰ ^total-op) ≡ (∫ ℰ) ^op
∫total-op≡∫^op ℰ =
  Precategory-path
    (∫total-op→∫^op ℰ)
    (∫total-op≅∫^op ℰ)
```

# Functors between fibres

If there is a functor between the fibres of a displayed category $\cE$,
then we also obtain a functor between the fibres of the total opposite
of $\cE$.

```agda
fibre-functor-total-op
  : ∀ {o ℓ o' ℓ'} {ℬ : Precategory o ℓ} {ℰ : Displayed ℬ o' ℓ'} {x y}
  → Functor (Fibre ℰ x) (Fibre ℰ y)
  → Functor (Fibre (ℰ ^total-op) x) (Fibre (ℰ ^total-op) y)
fibre-functor-total-op F .F₀ = F .F₀
fibre-functor-total-op F .F₁ = F .F₁
fibre-functor-total-op F .F-id = F .F-id
fibre-functor-total-op {ℰ = ℰ} F .F-∘ f g =
  ap (F .F₁) (DR.reindex ℰ _ _ ) ∙∙ F .F-∘ g f ∙∙ DR.reindex ℰ _ _
```
