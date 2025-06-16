<!--
```agda
open import Cat.Functor.Properties.FullyFaithful
open import Cat.Functor.Adjoint.Continuous
open import Cat.Diagram.Colimit.Base
open import Cat.Functor.Equivalence
open import Cat.Diagram.Limit.Base
open import Cat.Instances.Functor
open import Cat.Functor.Compose
open import Cat.Prelude

open creates-colimit
open creates-limit
open lifts-colimit
open lifts-limit
```
-->

```agda
module Cat.Functor.Equivalence.Properties where
```

# Properties of equivalences of categories

This module collects some properties of [[equivalences of categories]].

## Equivalences create limits and colimits

<!--
```agda
module
  _ {o ℓ o' ℓ'} {C : Precategory o ℓ} {D : Precategory o' ℓ'}
    {F : Functor C D} (eqv : is-equivalence F)
    {oj ℓj} {J : Precategory oj ℓj}
  where

  open is-equivalence eqv
```
-->

If $F : \cC \cong \cD$ is an equivalence, then $F$ [[creates limits]]
and colimits. To see this, assume that $F \circ \rm{Dia}$ has a limit
in $\cD$. Since $F^{-1}$ is continuous, we get a limit of
$F^{-1} \circ F \circ \rm{Dia} \cong \rm{Dia}$ in $\cC$; this limit
is automatically preserved since $F$ is continuous as well.
$F$ also reflects limits, since it is [[fully faithful]].

```agda
  equivalence→lifts-limits : lifts-limits-of J F
  equivalence→lifts-limits {Diagram = Diagram} lim = λ where
      .lifted → lim'
      .preserved → right-adjoint-is-continuous F⁻¹⊣F (Limit.has-ran lim')
    where
      lim' : Limit Diagram
      lim' = natural-iso→limit (ni-assoc ∙ni F∘-iso-id-l (Id≅F⁻¹∘F ni⁻¹))
        (right-adjoint-limit F⊣F⁻¹ lim)

  equivalence→creates-limits : creates-limits-of J F
  equivalence→creates-limits .has-lifts-limit = equivalence→lifts-limits
  equivalence→creates-limits {Diagram = Diagram} .reflects =
    ff→reflects-limit F (is-equivalence→is-ff F eqv) Diagram

  equivalence→lifts-colimits : lifts-colimits-of J F
  equivalence→lifts-colimits {Diagram = Diagram} colim = λ where
      .lifted → colim'
      .preserved → left-adjoint-is-cocontinuous F⊣F⁻¹ (Colimit.has-lan colim')
    where
      colim' : Colimit Diagram
      colim' = natural-iso→colimit (ni-assoc ∙ni F∘-iso-id-l (Id≅F⁻¹∘F ni⁻¹))
        (left-adjoint-colimit F⁻¹⊣F colim)

  equivalence→creates-colimits : creates-colimits-of J F
  equivalence→creates-colimits .has-lifts-colimit = equivalence→lifts-colimits
  equivalence→creates-colimits {Diagram = Diagram} .reflects =
    ff→reflects-colimit F (is-equivalence→is-ff F eqv) Diagram
```

## (Co)completeness respects equivalences

As a consequence of the previous fact, $\cC$ has (co)limits of $\cJ$-shaped
diagrams if and only if $\cD$ does, since both $F$ and $F^{-1}$ are
equivalences and thus lift (co)limits.

<!--
```agda
module
  _ {o ℓ o' ℓ'} {C : Precategory o ℓ} {D : Precategory o' ℓ'}
    {F : Functor C D} (eqv : is-equivalence F)
    {co cℓ}
  where
  open is-equivalence eqv
```
-->

```agda
  equivalence→complete⁻¹ : is-complete co cℓ D → is-complete co cℓ C
  equivalence→complete⁻¹ = lifts-limits→complete F
    (equivalence→lifts-limits eqv)

  equivalence→complete : is-complete co cℓ C → is-complete co cℓ D
  equivalence→complete = lifts-limits→complete F⁻¹
    (equivalence→lifts-limits inverse-equivalence)

  equivalence→cocomplete⁻¹ : is-cocomplete co cℓ D → is-cocomplete co cℓ C
  equivalence→cocomplete⁻¹ = lifts-colimits→cocomplete F
    (equivalence→lifts-colimits eqv)

  equivalence→cocomplete : is-cocomplete co cℓ C → is-cocomplete co cℓ D
  equivalence→cocomplete = lifts-colimits→cocomplete F⁻¹
    (equivalence→lifts-colimits inverse-equivalence)
```
