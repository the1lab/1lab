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
  open HLevel-instance
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
  F .F₀ (lift x) = F₀ G x
  F .F₁ (lift f) = F₁ G f
  F .F-id = F-id G
  F .F-∘ (lift f) (lift g) = F-∘ G f g

Lift-functor-r
  : ∀ {so sℓ} bo bℓ {o ℓ} {C : Precategory so sℓ} {D : Precategory o ℓ}
  → Functor C D
  → Functor C (Lift-cat bo bℓ D)
Lift-functor-r bo bℓ G = F where
  open Functor
  F : Functor _ _
  F .F₀ x = lift $ F₀ G x
  F .F₁ f = lift $ F₁ G f
  F .F-id = ap lift $ F-id G
  F .F-∘ f g = ap lift $ F-∘ G f g
```
