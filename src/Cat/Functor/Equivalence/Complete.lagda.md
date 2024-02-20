<!--
```agda
open import Cat.Functor.Adjoint.Continuous
open import Cat.Functor.Equivalence
open import Cat.Diagram.Limit.Base
open import Cat.Instances.Functor
open import Cat.Prelude
```
-->

```agda
module Cat.Functor.Equivalence.Complete where
```

# Completeness respects equivalences

Let $\cC$ be a category admitting limits for $\cJ$-shaped
diagrams, and $F : \cC \cong \cD$ an equivalence. Then $\cD$
also admits limits for $\cJ$-shaped diagrams; In particular, if
$\cC$ is complete, then so is $\cD$.

```agda
module
  _ {o ℓ o' ℓ'} {C : Precategory o ℓ} {D : Precategory o' ℓ'}
    {F : Functor C D} (eqv : is-equivalence F)
  where

  open is-equivalence eqv
```

This is a very short theorem: If $\cC$ admits $\cJ$-shaped limits, then
for any diagram $K : \cJ \to \cD$, the composite $F\inv K$ has a limit.
But since equivalences are [[right adjoints]], $F$ preserves this limit,
so $FF\inv K$ has a limit in $\cD$; But that composite is naturally
isomorphic to $K$, so $K$ also has a limit.

```agda
  equivalence→complete : ∀ {co cℓ} → is-complete co cℓ C → is-complete co cℓ D
  equivalence→complete ccomp K =
    natural-iso→limit (F∘-iso-id-l F∘F⁻¹≅Id)
      (subst Limit F∘-assoc (right-adjoint-limit F⁻¹⊣F (ccomp (F⁻¹ F∘ K))))
```
