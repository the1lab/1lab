<!--
```agda
open import Cat.Prelude
```
-->

```agda
module Cat.Instances.Lift where
```

# Lifting categories across universes

Suppose you have a category $\cC$ with objects in $o$ and homs in
$\ell$, but you really need it to have objects in some larger universe
$o \sqcup o'$ and homs in $\ell \sqcup \ell'$. Fortunately you can
uniformly lift the precategory $\cC$ to this bigger universe.

```agda
Lift-cat : ∀ {o ℓ} o' ℓ' → Precategory o ℓ → Precategory (o ⊔ o') (ℓ ⊔ ℓ')
Lift-cat o' ℓ' C = liftc where
  open Precategory C
  liftc : Precategory _ _
  liftc .Precategory.Ob = Lift o' Ob
  liftc .Precategory.Hom (lift x) (lift y) = Lift ℓ' (Hom x y)
  liftc .Precategory.Hom-set x y = hlevel 2
  liftc .Precategory.id = lift id
  liftc .Precategory._∘_ (lift f) (lift g) = lift (f ∘ g)
  liftc .Precategory.idr (lift f) = ap lift (idr f)
  liftc .Precategory.idl (lift f) = ap lift (idl f)
  liftc .Precategory.assoc (lift f) (lift g) (lift h) = ap lift (assoc f g h)

Lift-functor-l
  : ∀ {so sℓ} bo bℓ {o ℓ} {C : Precategory so sℓ} {D : Precategory o ℓ}
  → Functor C D
  → Functor (Lift-cat bo bℓ C) D
Lift-functor-l bo bℓ G = F where
  open Functor
  F : Functor _ _
  F .F₀ (lift x) = G .F₀ x
  F .F₁ (lift f) = G .F₁ f
  F .F-id = G .F-id
  F .F-∘ (lift f) (lift g) = G .F-∘ f g

Lift-functor-r
  : ∀ {so sℓ} bo bℓ {o ℓ} {C : Precategory so sℓ} {D : Precategory o ℓ}
  → Functor C D
  → Functor C (Lift-cat bo bℓ D)
Lift-functor-r bo bℓ G = F where
  open Functor
  F : Functor _ _
  F .F₀ x = lift $ G .F₀ x
  F .F₁ f = lift $ G .F₁ f
  F .F-id = ap lift $ G .F-id
  F .F-∘ f g = ap lift $ G .F-∘ f g
```
