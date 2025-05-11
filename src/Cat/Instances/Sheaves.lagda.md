<!--
```agda
open import Cat.Instances.Presheaf.Exponentials
open import Cat.Functor.Equivalence.Properties
open import Cat.Instances.Sheaf.Limits.Finite
open import Cat.Instances.Sheaf.Exponentials
open import Cat.Functor.Adjoint.Continuous
open import Cat.Functor.Adjoint.Reflective
open import Cat.Instances.Algebras.Limits
open import Cat.Instances.Sets.Cocomplete
open import Cat.Instances.Functor.Limits
open import Cat.Functor.Adjoint.Monadic
open import Cat.Functor.FullSubcategory
open import Cat.Instances.Sets.Complete
open import Cat.Instances.Sheaf.Limits
open import Cat.Diagram.Colimit.Base
open import Cat.Diagram.Exponential
open import Cat.Functor.Equivalence
open import Cat.Site.Sheafification
open import Cat.Diagram.Limit.Base
open import Cat.Instances.Functor
open import Cat.Functor.Adjoint
open import Cat.Functor.Base
open import Cat.Site.Base
open import Cat.Prelude

open Cartesian-closed
open is-exponential
open Exponential
```
-->

```agda
module Cat.Instances.Sheaves where
```

# The topos of sheaves {defines="topos-of-sheaves"}

This module collects a compendium of the nice properties enjoyed by the
category of [[sheaves]] on a [[site]].

```agda
Sh[_,_] : ∀ {ℓ} (C : Precategory ℓ ℓ) (J : Coverage C ℓ) → Precategory (lsuc ℓ) ℓ
Sh[ C , J ] = Sheaves J _
```

<!--
```agda
module _ {ℓ} {C : Precategory ℓ ℓ} {J : Coverage C ℓ} where
```
-->

## Monadicity

Since the [[sheafification]] construction provides a [[left adjoint]] to
the [[fully faithful]] inclusion of presheaves into sheaves, we can
immediately conclude that the category of sheaves on a site is
[[monadic]] over the presheaves on that same site.

```agda
  Sheafification : Functor (PSh ℓ C) Sh[ C , J ]
  Sheafification = free-objects→functor (Small.make-free-sheaf J)

  Sheafification⊣ι : Sheafification ⊣ forget-sheaf J _
  Sheafification⊣ι = free-objects→left-adjoint (Small.make-free-sheaf J)
```

Note that since the category of $J$-sheaves is defined to literally have
the same $\hom$-sets as the category of presheaves on $\cC$, the action
of the forgetful functor on morphisms is definitionally the identity.

```agda
  Sheafification-is-reflective : is-reflective Sheafification⊣ι
  Sheafification-is-reflective = id-equiv

  Sheafification-is-monadic : is-monadic Sheafification⊣ι
  Sheafification-is-monadic = is-reflective→is-monadic _ id-equiv
```

### Limits and colimits

By general properties of reflective subcategories, we have that the
category of sheaves on a site is [[complete|complete category]] and
[[cocomplete|cocomplete category]]; Completeness is by an equivalence
with the [[Eilenberg-Moore category]] of the sheafification monad (which
[[has all limits|limits in categories of algebras]] which $\psh(\cC)$
does), and cocompleteness follows by computing the colimit in
presheaves, then sheafifying the result.

```agda
  Sh[]-is-complete : is-complete ℓ ℓ Sh[ C , J ]
  Sh[]-is-complete = equivalence→complete
    (is-equivalence.inverse-equivalence Sheafification-is-monadic)
    (Eilenberg-Moore-is-complete _
      (Functor-cat-is-complete (Sets-is-complete {ι = ℓ} {ℓ} {ℓ})))

  Sh[]-is-cocomplete : is-cocomplete ℓ ℓ Sh[ C , J ]
  Sh[]-is-cocomplete F = done where
    psh-colim : Colimit (forget-sheaf J _ F∘ F)
    psh-colim = Functor-cat-is-cocomplete (Sets-is-cocomplete {ι = ℓ} {ℓ} {ℓ}) _

    sheafified : Colimit ((Sheafification F∘ forget-sheaf J _) F∘ F)
    sheafified = subst Colimit F∘-assoc $
      left-adjoint-colimit Sheafification⊣ι psh-colim

    done = natural-iso→colimit
      (F∘-iso-id-l (is-reflective→counit-iso Sheafification⊣ι id-equiv))
      sheafified
```

## Cartesian closure

Since [[sheaves are an exponential ideal|exponentials of sheaves]] in
presheaves, meaning that $B^A$ is a sheaf whenever $B$ is, we can
conclude that the category of sheaves on a site is also [[Cartesian
closed]].

```agda
  Sh[]-cc : Cartesian-closed Sh[ C , J ] (Sh[]-products J) (Sh[]-terminal J)
  Sh[]-cc .has-exp (A , _) (B , bshf) = exp where
    exp' = PSh-closed C .has-exp A B

    exp : Exponential Sh[ C , J ] _ _ _ _
    exp .B^A .fst = exp' .B^A
    exp .B^A .snd = is-sheaf-exponential J A B bshf
    exp .ev       = exp' .ev
    exp .has-is-exp .ƛ        = exp' .ƛ
    exp .has-is-exp .commutes = exp' .commutes
    exp .has-is-exp .unique   = exp' .unique
```
