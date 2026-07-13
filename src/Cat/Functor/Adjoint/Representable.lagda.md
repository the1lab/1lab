<!--
```agda
open import Cat.Instances.Elements.Covariant
open import Cat.Diagram.Coproduct.Copower
open import Cat.Diagram.Coproduct.Indexed
open import Cat.Functor.Hom.Representable
open import Cat.Functor.Equivalence.Path
open import Cat.Instances.Sets.Complete
open import Cat.Functor.Adjoint.Hom
open import Cat.Functor.Equivalence
open import Cat.Functor.Hom.Duality
open import Cat.Instances.Functor
open import Cat.Diagram.Terminal
open import Cat.Diagram.Initial
open import Cat.Functor.Adjoint
open import Cat.Instances.Comma
open import Cat.Instances.Sets
open import Cat.Functor.Hom
open import Cat.Prelude

import Cat.Functor.Reasoning.Presheaf
import Cat.Reasoning

open Corepresentation
open Representation
open Functor
```
-->

```agda
module Cat.Functor.Adjoint.Representable {o ℓ} {C : Precategory o ℓ} where
```

# Adjoints in terms of representability

Building upon our characterisation of [[adjoints as Hom isomorphisms]], we now
investigate the relationship between [[adjoint functors]] and [[representable
functors]].

In this section, we show that for a functor $R : \cC \to \cD$ to be a right adjoint
is equivalent to the functor $\hom_\cD(d, R-) : \cC \to \Sets$ having a representing
object for all $d : \cD$.

The forward direction follows directly from the natural isomorphism $\hom_\cC(Ld, -)
\cong \hom_\cD(d, R-)$, which exhibits $Ld$ as a representing object.

<!--
```agda
module _ {o'} {D : Precategory o' ℓ}
  {L : Functor D C} {R : Functor C D} (L⊣R : L ⊣ R)
  where
  private
    module L = Functor L
    module R = Functor R
  open _⊣_ L⊣R
```
-->

```agda
  right-adjoint→is-objectwise-rep
    : ∀ d → is-corepresentation (Hom-from D d F∘ R) (L.₀ d) (η d)
  {-# INLINE right-adjoint→is-objectwise-rep #-}
  right-adjoint→is-objectwise-rep d =
    yo-is-equiv→is-corepresentation λ c →
    L-adjunct-is-equiv L⊣R

  left-adjoint→is-objectwise-rep
    : ∀ c → is-corepresentation (Hom-into C c F∘ L.op) (R.₀ c) (ε c)
  {-# INLINE left-adjoint→is-objectwise-rep #-}
  left-adjoint→is-objectwise-rep c =
    yo-is-equiv→is-corepresentation λ d →
    R-adjunct-is-equiv L⊣R
```

The other direction should be more surprising: if we only have a family of objects
$Ld$ representing the functors $\hom_\cD(d, R-)$, why should we expect them to
assemble into a *functor* $L : \cD \to \cC$?


<!--
```agda
module _ {o'} {D : Precategory o' ℓ}
  {R : Functor C D}
  (corep : ∀ d → Corepresentation (Hom-from D d F∘ R))
  where

  private
    module D = Cat.Reasoning D
    module corep d = Corepresentation (corep d)
```
-->

First, observe that the data of a corepresenting object for $\cD(d, R(-))$ is
exactly the data of a [[free object]] for $R$.

```agda
  objectwise-rep→free-objects : ∀ d → Free-object R d
  objectwise-rep→free-objects d = record
    { unit = corep.section d
    ; fold = corep.universal d
    ; commute = λ {c} {f} → corep.factors d f
    ; unique = λ {c} {f} → corep.unique d f
    }
```

Moreover, if we have free objects for every $d : \cD$, then we can assemble them
into a left adjoint.

```agda
  objectwise-rep→functor : Functor D C
  objectwise-rep→functor = free-objects→functor objectwise-rep→free-objects

  objectwise-rep→left-adjoint : objectwise-rep→functor ⊣ R
  objectwise-rep→left-adjoint =
    free-objects→left-adjoint objectwise-rep→free-objects
```

## Right adjoints into Sets are representable

For functors into $\Sets_\ell$, we can go one step further: under certain conditions,
being a right adjoint is equivalent to being representable.

Indeed, if $R$ has a left adjoint $L : \Sets_\ell \to \cC$, then $R$ is automatically
represented by $L\{*\}$, the image of the singleton set by $L$, because we have
$\hom_\cC(L\{*\}, c) \cong (\{*\} \to Rc) \cong Rc$.

<!--
```agda
module _
  {R : Functor C (Sets ℓ)} {L : Functor (Sets ℓ) C} (L⊣R : L ⊣ R)
  where
  open _⊣_ L⊣R
```
-->

```agda
  open Terminal (Sets-terminal {ℓ})

  right-adjoint→is-corepresentation : is-corepresentation R (L .F₀ top) (η top (lift tt))
  {-# INLINE right-adjoint→is-corepresentation #-}
  right-adjoint→is-corepresentation =
    yo-is-equiv→is-corepresentation λ c →
    ∘-is-equiv (Π-⊤-eqv .snd) (L-adjunct-is-equiv L⊣R)
```

Going the other way, if we assume that $\cC$ is [[copowered]] over $\Sets_\ell$
(in other words, that it admits $\ell$-small [[indexed coproducts]]), then any
functor $R$ with representing object $c$ has a left adjoint given by taking copowers
of $c$: for any set $X$, we have $\hom_\cC(X \otimes c, -) \cong
(X \to \hom_\cC(c, -)) \cong (X \to R-)$.

<!--
```agda
module _
  (copowered : has-indexed-coproducts C ℓ)
  {R : Functor C (Sets ℓ)} (R-corep : Corepresentation R)
  where
```
-->

```agda
  private
    module R = Cat.Functor.Reasoning.Presheaf R
    module corep = Corepresentation R-corep
    open Copowers (λ _ → copowered)


    Hom[X,R-]-rep : ∀ X → Corepresentation (Hom-from (Sets ℓ) X F∘ R)
    Hom[X,R-]-rep X .corep = X ⊗ R-corep .corep
    Hom[X,R-]-rep X .section x = R.₁ (⊗!.ι ∣ X ∣ corep.corep x) corep.section
    Hom[X,R-]-rep X .has-is-corep = yo-is-equiv→is-corepresentation λ Y →
      subst-is-equiv (ext (λ f x → R.collapse refl))
      $ ∘-is-equiv
        (Π-ap-cod-is-equiv (λ x → is-corepresentation→yo-is-equiv corep.has-is-corep Y))
        (⊗!.hom-iso ∣ X ∣ corep.corep .snd)

  corepresentable→functor : Functor (Sets ℓ) C
  corepresentable→functor = objectwise-rep→functor Hom[X,R-]-rep

  corepresentable→left-adjoint : corepresentable→functor ⊣ R
  corepresentable→left-adjoint = objectwise-rep→left-adjoint Hom[X,R-]-rep
```
