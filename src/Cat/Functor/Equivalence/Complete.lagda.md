```agda
open import Cat.Functor.Adjoint.Continuous
open import Cat.Functor.Equivalence
open import Cat.Diagram.Limit.Base
open import Cat.Instances.Functor
open import Cat.Functor.Base
open import Cat.Prelude

module Cat.Functor.Equivalence.Complete where
```

# Completeness respects equivalences

Let $\ca{C}$ be a category admitting limits for $\ca{J}$-shaped
diagrams, and $F : \ca{C} \cong \ca{D}$ an equivalence. Then $\ca{D}$
also admits limits for $\ca{J}$-shaped diagrams; In particular, if
$\ca{C}$ is complete, then so is $\ca{D}$.

```agda
module
  _ {o ℓ o′ ℓ′} {C : Precategory o ℓ} {D : Precategory o′ ℓ′}
    {F : Functor C D} (eqv : is-equivalence F)
  where

  open is-equivalence eqv
```

This is a very short theorem: If $\ca{C}$ admits $\ca{J}$-shaped limits,
then for any diagram $K : \ca{J} \to \ca{D}$, the composite $F^{-1}K$
has a limit. But since equivalences are right adjoints, $F$ preserves
this limit, so $FF^{-1}K$ has a limit in $\ca{D}$; But that composite is
naturally isomorphic to $K$, so $K$ also has a limit.

```agda
  equivalence→complete : ∀ {co cℓ} → is-complete co cℓ C → is-complete co cℓ D
  equivalence→complete ccomp K =
    Limit-ap-iso (F∘-iso-id-l F∘F⁻¹≅Id)
      (subst Limit F∘-assoc (right-adjoint-limit F⁻¹⊣F (ccomp (F⁻¹ F∘ K))))
```
