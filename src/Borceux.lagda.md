---
description: |
  Lemmas and theorems from Francis Borceux's "Handbook of Categorical Algebra".
---
<!--
```agda
open import Algebra.Group.Cat.FinitelyComplete
open import Algebra.Monoid.Category
open import Algebra.Group.Cat.Base
open import Algebra.Group.Free hiding (_◆_)
open import Algebra.Group.Ab

open import Cat.Morphism.Factorisation.Orthogonal
open import Cat.Diagram.Coequaliser.RegularEpi
open import Cat.Functor.Adjoint.Epireflective
open import Cat.Functor.Adjoint.Representable
open import Cat.Instances.Elements.Covariant renaming (∫ to ∫cov)
open import Cat.Instances.StrictCat.Cohesive hiding (Disc)
open import Cat.Monoidal.Instances.Cartesian
open import Cat.Diagram.Pullback.Properties
open import Cat.Internal.Instances.Discrete
open import Cat.Functor.Adjoint.Continuous
open import Cat.Functor.Adjoint.Reflective
open import Cat.Diagram.Colimit.Universal
open import Cat.Diagram.Coproduct.Indexed
open import Cat.Diagram.Projective.Strong
open import Cat.Diagram.Separator.Regular
open import Cat.Functor.Hom.Representable
open import Cat.Instances.Sets.Cocomplete
open import Cat.Diagram.Separator.Strong
open import Cat.Instances.Functor.Limits
open import Cat.CartesianClosed.Locally
open import Cat.Diagram.Limit.Equaliser
open import Cat.Diagram.Product.Indexed
open import Cat.Functor.Adjoint.Compose
open import Cat.Functor.FullSubcategory
open import Cat.Instances.Sets.Complete
open import Cat.Diagram.Colimit.Cocone
open import Cat.Diagram.Limit.Pullback
open import Cat.Functor.Hom.Properties
open import Cat.Instances.Localisation
open import Cat.Instances.MarkedGraphs
open import Cat.Instances.OuterFunctor
open import Cat.Internal.Functor.Outer
open import Cat.Morphism.Factorisation
open import Cat.Bi.Diagram.Adjunction
open import Cat.Functor.Adjoint.Monad
open import Cat.Functor.Kan.Pointwise
open import Cat.Diagram.Colimit.Base
open import Cat.Diagram.Limit.Finite
open import Cat.Functor.Conservative
open import Cat.Functor.Hom.Coyoneda
open import Cat.Diagram.Coequaliser
open import Cat.Functor.Adjoint.AFT
open import Cat.Functor.Adjoint.Hom
open import Cat.Functor.Adjoint.Kan
open import Cat.Functor.Equivalence
open import Cat.Functor.Kan.Adjoint
open import Cat.Functor.Subcategory
open import Cat.Instances.Delooping
open import Cat.Instances.StrictCat
open import Cat.Morphism.Orthogonal
open import Cat.Morphism.Strong.Epi
open import Cat.Bi.Instances.Spans
open import Cat.Diagram.Idempotent
open import Cat.Diagram.Limit.Base
open import Cat.Diagram.Limit.Cone
open import Cat.Functor.Hom.Yoneda
open import Cat.Functor.Properties
open import Cat.Instances.Discrete
open import Cat.Diagram.Equaliser
open import Cat.Diagram.Separator
open import Cat.Functor.Bifunctor
open import Cat.Instances.Functor
open import Cat.Instances.Karoubi
open import Cat.Instances.Product
open import Cat.Internal.Opposite
open import Cat.Diagram.Pullback
open import Cat.Diagram.Terminal
open import Cat.Functor.Constant
open import Cat.Functor.Kan.Base
open import Cat.Functor.Morphism
open import Cat.Instances.Graphs
open import Cat.Diagram.Initial
open import Cat.Diagram.Product
open import Cat.Diagram.Pushout
open import Cat.Functor.Adjoint
open import Cat.Functor.Compose
open import Cat.Instances.Comma
open import Cat.Instances.Slice
open import Cat.Functor.Closed
open import Cat.Instances.Free
open import Cat.Instances.Sets
open import Cat.Morphism.Lifts
open import Cat.Diagram.Monad
open import Cat.Functor.Final
open import Cat.Functor.Joint
open import Cat.Internal.Base
open import Cat.Functor.Base
open import Cat.Functor.Hom
open import Cat.Morphism
open import Cat.Bi.Base
open import Cat.Prelude
open import Cat.Strict

open import Data.Set.Surjection

open import Order.Cat
```
-->
```agda
module Borceux where
```

Though the 1Lab is not purely a formalization of category theory, it does
aim to be a useful reference on the subject. However, the 1Lab organizes
content in a highly non-linear fashion; this can make it somewhat difficult
to use as a companion to more traditional resources.

This page attempts to (somewhat) rectify this situation by gathering all
of the results from Francis Borceux's "Handbook of Categorical Algebra"
[@Borceux:vol1] in a single place.^[It also serves as an excellent place to
find possible contributions!]

# Volume 1

## 1 The language of categories

### 1.1 Logical foundations of the theory

* Proposition 1.1: [Russell's paradox]

[Russell's paradox]: 1Lab.Counterexamples.Russell.html

## 1.2 Categories and functors

<!--
```agda
_ = Precategory
_ = Functor
_ = is-strict
_ = Strict-cats
_ = Sets
_ = Groups
_ = poset→category
_ = Disc
_ = B
_ = Slice
_ = Ab↪Sets
_ = Hom-from
_ = Const
```
-->

* Definition 1.2.1: `Precategory`{.Agda}
* Definition 1.2.2: `Functor`{.Agda}
* Definition 1.2.3: `is-strict`{.Agda}
* Proposition 1.2.4: `Strict-cats`{.Agda}
* Examples 1.2.5:
  * a. `Sets`{.Agda}
  * c. `Groups`{.Agda}
* Examples 1.2.6:
  * b. `poset→category`{.Agda}
  * c. `Disc`{.Agda}
  * d. `B`{.Agda}
* Examples 1.2.7:
  * a. `Slice`{.Agda}
* Examples 1.2.8:
  * a. `Ab↪Sets`{.Agda}
  * d. `Hom[_,-]`{.Agda}
  * e. `Const`{.Agda}

### 1.3 Natural transformations

<!--
```agda
_ = _=>_
_ = Cat[_,_]
_ = _◆_
_ = ◆-interchange
_ = yo-is-equiv
_ = yo-naturalr
_ = yo-naturall
_ = constⁿ
```
-->

* Definition 1.3.1: `_=>_`{.Agda}
* Proposition 1.3.2: `Cat[_,_]`{.Agda}
* Theorem 1.3.3:
  * 1. `yo-is-equiv`{.Agda}
  * 2. `yo-naturalr`{.Agda}
  * 3. `yo-naturall`{.Agda}
* Proposition 1.3.4: `_◆_`{.Agda}
* Proposition 1.3.5: `◆-interchange`{.Agda}
* Examples 1.3.6:
  * c. (as part of `[-,-]`{.Agda})
  * d. `constⁿ`{.Agda}

### 1.4 Contravariant functors

Borceux defines contravariant functors as a distinct object rather than
functors from $\cC\op$; this makes it somewhat difficult to map
definitions on a 1-1 basis.

<!--
```agda
_ = _^op
_ = Hom[-,-]
_ = よ₀
_ = よ
```
-->

* Definition 1.4.1: `_^op`{.Agda}
* Definition 1.4.2: `_^op`{.Agda}
* Examples 1.4.3:
  * a. `Hom[-,-]`{.Agda}
  * b. `よ₀`{.Agda}
  * c. (as part of `よ`{.Agda})
  * d. `よ`{.Agda}

### 1.5 Full and faithful functors

<!--
```agda
_ = is-faithful
_ = is-full
_ = is-fully-faithful
_ = is-precat-iso
_ = よ-is-fully-faithful
_ = Hom[-,-]-is-fully-faithful
_ = Subcat
_ = Restrict
```
-->

* Definition 1.5.1:
  * 1. `is-faithful`{.Agda}
  * 2. `is-full`{.Agda}
  * 3. `is-fully-faithful`{.Agda}
  * 4. `is-precat-iso`{.Agda}
* Proposition 1.5.2:
  * 1. `よ-is-fully-faithful`{.Agda}
  * 2. `Hom[-,-]-is-fully-faithful`{.Agda}
* Definition 1.5.3: `Subcat`{.Agda}
* Definition 1.5.4: `Restrict`{.Agda}

### 1.6 Comma categories

<!--
```agda
_ = _↓_
_ = Dom
_ = Cod
_ = θ
_ = ∫cov
_ = _×ᶜ_
_ = Cat⟨_,_⟩
```
-->

* Definition 1.6.1: `_↓_`{.Agda}
* Proposition 1.6.2:
  * 1. `Dom`{.Agda}
  * 2. `Cod`{.Agda}
  * 3. `θ`{.Agda}
* Definition 1.6.4: `∫cov`{.Agda}
* Definition 1.6.5: `_×ᶜ_`{.Agda}
* Proposition 1.6.6: `Cat⟨_,_⟩`{.Agda}

### 1.7 Monomorphisms

<!--
```agda
_ = is-monic
_ = id-monic
_ = ∘-is-monic
_ = monic-cancell
_ = has-section
_ = has-retract
_ = has-retract→monic
_ = faithful→reflects-mono
_ = embedding→monic
_ = monic→is-embedding
```
-->

* Definition 1.7.1: `is-monic`{.Agda}
* Proposition 1.7.2:
  * 1. `id-monic`{.Agda}
  * 2. `∘-is-monic`{.Agda}
  * 3. `monic-cancell`{.Agda}
* Definition 1.7.3:
  * 1. `has-section`{.Agda}
  * 2. `has-retract`{.Agda}
* Proposition 1.7.4: `has-retract→monic`{.Agda}
* Proposition 1.7.6: `faithful→reflects-mono`{.Agda}
* Examples 1.7.7:
  * a. `embedding→monic`{.Agda}, `monic→is-embedding`{.Agda}

### 1.8 Epimorphisms

<!--
```agda
_ = is-epic
_ = id-epic
_ = ∘-is-epic
_ = epic-cancelr
_ = has-section→epic
_ = faithful→reflects-epi
_ = surjective→regular-epi
_ = epi→surjective
```
-->

* Definition 1.8.1: `is-epic`{.Agda}
* Proposition 1.8.2:
  * 1. `id-epic`{.Agda}
  * 2. `∘-is-epic`{.Agda}
  * 3. `epic-cancelr`{.Agda}
* Proposition 1.8.3: `has-section→epic`{.Agda}
* Proposition 1.8.4: `faithful→reflects-epi`{.Agda}
* Examples 1.8.5:
  * a. `surjective→regular-epi`{.Agda}, `epi→surjective`{.Agda}

### 1.9 Isomorphisms

<!--
```agda
_ = is-invertible
_ = id-invertible
_ = invertible-∘
_ = invertible→monic
_ = invertible→epic
_ = has-retract+epic→invertible
_ = F-iso.F-map-invertible
_ = is-ff→is-conservative
_ = equiv≃iso
```
-->

* Definition 1.9.1: `is-invertible`{.Agda}
* Proposition 1.9.2:
  * 1. `id-invertible`{.Agda}
  * 2. `invertible-∘`{.Agda}
  * 3. `invertible→monic`{.Agda}, `invertible→epic`{.Agda}
* Proposition 1.9.3: `has-retract+epic→invertible`{.Agda}
* Proposition 1.9.4: `F-iso.F-map-invertible`{.Agda}
* Proposition 1.9.5: `is-ff→is-conservative`{.Agda}
* Examples 1.9.6:
  * a. `equiv≃iso`{.Agda}

### 1.10 The duality principle

<!--
```agda
_ = Hom[-,-]
```
-->

* Definition 1.10.1: `_^op`{.Agda}
* Examples 1.10.3:
  * a. `Hom[-,-]`{.Agda}

### 1.11 Exercises

<!--
```agda
_ = thin-functor
_ = よ-preserves-mono
_ = Hom[-,-]-reverses-epi
_ = Curry
_ = Uncurry
_ = has-section+monic→invertible
```
-->

* Exercise 1.11.1: 🚧 `thin-functor`{.Agda}
* Exercise 1.11.5: `よ-preserves-mono`{.Agda}
* Exercise 1.11.6: `Hom[-,-]-reverses-epi`{.Agda}
* Exercise 1.11.8: 🚧 `Curry`{.Agda}, `Uncurry`{.Agda}
* Exercise 1.11.9: `has-section+monic→invertible`{.Agda}

## 2 Limits

### 2.1 Products

<!--
```agda
_ = is-product
_ = ×-Unique
_ = Binary-products.swap-is-iso
_ = Cartesian-monoidal
_ = is-indexed-product
_ = Indexed-product-unique
_ = is-indexed-product-assoc
```
-->

* Definition 2.1.1: `is-product`{.Agda}
* Proposition 2.1.2: `×-Unique`{.Agda}
* Proposition 2.1.3:
  * 1. `Binary-products.swap-is-iso`{.Agda}
  * 2. `Cartesian-monoidal`{.Agda}
* Definition 2.1.4: `is-indexed-product`{.Agda}
* Proposition 2.1.5: `Indexed-product-unique`{.Agda}
* Proposition 2.1.6: `is-indexed-product-assoc`{.Agda}

### 2.2 Coproducts

<!--
```agda
_ = is-indexed-coproduct
_ = is-indexed-coproduct→iso
_ = is-indexed-coproduct-assoc
```
-->

* Definition 2.2.1: `is-indexed-coproduct`{.Agda}
* Proposition 2.2.2: `is-indexed-coproduct→iso`{.Agda}
* Proposition 2.2.3: `is-indexed-coproduct-assoc`{.Agda}

### 2.3 Initial and terminal objects

<!--
```agda
_ = is-initial
_ = is-terminal
_ = Sets-initial
_ = Sets-terminal
_ = Zero-group-is-zero
```
-->

* Definition 2.3.1:
  * 1. `is-terminal`{.Agda}
  * 2. `is-initial`{.Agda}
* Examples 2.3.2:
  * a. `Sets-initial`{.Agda}, `Sets-terminal`{.Agda}
  * b. 🚧 `Zero-group-is-zero`{.Agda}

### 2.4 Equalizers, coequalizers

<!--
```agda
_ = is-equaliser
_ = is-equaliser→iso
_ = is-equaliser→is-monic
_ = id-is-equaliser
_ = equaliser+epi→invertible
```
-->

* Definition 2.4.1: `is-equaliser`{.Agda}
* Proposition 2.4.2: `is-equaliser→iso`{.Agda}
* Proposition 2.4.3: `is-equaliser→is-monic`{.Agda}
* Proposition 2.4.4: `id-is-equaliser`{.Agda}
* Proposition 2.4.5: `equaliser+epi→invertible`{.Agda}

### 2.5 Pullbacks, pushouts

<!--
```agda
_ = is-pullback
_ = Pullback-unique
_ = is-monic→pullback-is-monic
_ = is-invertible→pullback-is-invertible
_ = is-kernel-pair
_ = is-kernel-pair→epil
_ = is-kernel-pair→epir
_ = monic→id-kernel-pair
_ = id-kernel-pair→monic
_ = same-kernel-pair→id-kernel-pair
_ = is-effective-epi.is-effective-epi→is-regular-epi
_ = is-regular-epi→is-effective-epi
_ = pasting-left→outer-is-pullback
_ = Sets-pullbacks
```
-->

* Definition 2.5.1: `is-pullback`{.Agda}
* Proposition 2.5.2: `Pullback-unique`{.Agda}
* Proposition 2.5.3:
  * 1. `is-monic→pullback-is-monic`{.Agda}
  * 2. `is-invertible→pullback-is-invertible`{.Agda}
* Definition 2.5.4: `is-kernel-pair`{.Agda}
* Proposition 2.5.5: `is-kernel-pair→epil`{.Agda}, `is-kernel-pair→epir`{.Agda}
* Proposition 2.5.6:
  * (1 ⇒ 2): `monic→id-kernel-pair`{.Agda}
  * (2 ⇒ 1): `id-kernel-pair→monic`{.Agda}
  * (3 ⇒ 2): `same-kernel-pair→id-kernel-pair`{.Agda}
* Proposition 2.5.7: `is-effective-epi.is-effective-epi→is-regular-epi`{.Agda}
* Proposition 2.5.8: `is-regular-epi→is-effective-epi`{.Agda}
* Proposition 2.5.9:
  * 1. `pasting-left→outer-is-pullback`{.Agda}
* Examples 2.5.10
  * a. `Sets-pullbacks`{.Agda}

### 2.6 Limits and colimits

<!--
```agda
_ = Cone
_ = is-limit
_ = limits-unique
_ = is-limit.unique₂
_ = Cocone
_ = is-colimit
_ = Limit→Equaliser
_ = Equaliser→Limit
_ = Limit→Pullback
_ = Pullback→Limit
```
-->

* Definition 2.6.1: `Cone`{.Agda}
* Definition 2.6.2: `is-limit`{.Agda}
* Proposition 2.6.3: `limits-unique`{.Agda}
* Proposition 2.6.4: `is-limit.unique₂`{.Agda}
* Definition 2.6.5: `Cocone`{.Agda}
* Definition 2.6.6: `is-colimit`{.Agda}
* Examples 2.6.7:
  * b. `Limit→Equaliser`{.Agda}, `Equaliser→Limit`{.Agda}
  * c. `Limit→Pullback`{.Agda}, `Pullback→Limit`{.Agda}

### 2.7 Complete categories

<!--
```agda
_ = is-complete
```
-->

* Definition 2.7.2: `is-complete`{.Agda}

### 2.8 Existence theorem for limits

<!--
```agda
_ = with-equalisers
_ = with-pullbacks
```
-->

* Proposition 2.8.2:
  * 2. `with-equalisers`{.Agda}
  * 3. `with-pullbacks`{.Agda}

### 2.9 Limit preserving functors

<!--
```agda
_ = preserves-limit
_ = is-lex.pres-monos
_ = corepresentable-preserves-limits
_ = representable-reverses-colimits
_ = reflects-limit
_ = conservative-reflects-limits
```
-->

* Definition 2.9.1: `preserves-limit`{.Agda}
* Proposition 2.9.3: `is-lex.pres-monos`{.Agda}
* Proposition 2.9.4: `corepresentable-preserves-limits`{.Agda}
* Proposition 2.9.5: `representable-reverses-colimits`{.Agda}
* Definition 2.9.6: `reflects-limit`{.Agda}
* Proposition 2.9.7: `conservative-reflects-limits`{.Agda}

### 2.10 Absolute colimits

### 2.11 Final functors

::: warning
Borceux uses some outdated terminology here, and also uses a condition
that is overly powerful. We opt to stick with the terminology from the
nLab instead.
:::

<!--
```agda
_ = is-final
_ = extend-is-colimit
_ = is-colimit-restrict
```
-->

* Definition 2.11.1: `is-final`{.Agda}
* Proposition 2.11.2: `extend-is-colimit`{.Agda}, `is-colimit-restrict`{.Agda}

### 2.12 Interchange of limits

### 2.13 Filtered colimits

### 2.14 Universality of colimits


<!--
```agda
_ = has-stable-colimits
```
-->

* Definition 2.14.1: `has-stable-colimits`{.Agda}

### 2.15 Limits in categories of functors

<!--
```agda
_ = functor-limit
_ = Functor-cat-is-complete
_ = coyoneda
```
-->

* Proposition 2.15.1: `functor-limit`{.Agda}
* Theorem 2.15.2: `Functor-cat-is-complete`{.Agda}
* Proposition 2.15.6: `coyoneda`{.Agda}

### 2.16 Limits in comma categories

### 2.17 Exercises

<!--
```agda
_ = Cone→cone
```
-->

* Exercise 2.17.3: 🚧 `Cone→cone`{.Agda}
* Exercises 2.17.8: `extend-is-colimit`{.Agda}, `is-colimit-restrict`{.Agda}

## 3 Adjoint functors

### 3.1 Reflection along a functor

<!--
```agda
_ = Free-object
_ = free-object-unique
_ = free-objects→left-adjoint
_ = _⊣_
_ = free-objects≃left-adjoint
_ = hom-iso→adjoints
_ = make-free-group
_ = Free-monoid⊣Forget
_ = Disc⊣Γ
_ = Γ⊣Codisc
```
-->

* Definition 3.1.1: `Free-object`{.Agda}
* Proposition 3.1.2: `free-object-unique`{.Agda}
* Proposition 3.1.3: `free-objects→left-adjoint`{.Agda}
* Definition 3.1.4: `_⊣_`
* Theorem 3.1.5: `free-objects≃left-adjoint`{.Agda}, `hom-iso→adjoints`{.Agda}
* Examples 3.1.6:
  * a. `Free-monoid⊣Forget`{.Agda}
  * b. `make-free-group`{.Agda}
  * k. `Disc⊣Γ`{.Agda}, `Γ⊣Codisc`{.Agda}

### 3.2 Properties of adjoint functors

<!--
```agda
_ = LF⊣GR
_ = right-adjoint-is-continuous
```
-->

* Proposition 3.2.1: `LF⊣GR`{.Agda}
* Proposition 3.2.2: `right-adjoint-is-continuous`{.Agda}

### 3.3 The adjoint functor theorem

<!--
```agda
_ = Solution-set
_ = solution-set→left-adjoint
```
-->

* Definition 3.3.2: `Solution-set`{.Agda}
* Theorem 3.3.3: `solution-set→left-adjoint`{.Agda}

### 3.4 Fully faithful adjoint functors

<!--
```agda
_ = is-reflective→counit-is-iso
_ = is-counit-iso→is-reflective
_ = is-equivalence
```
-->

* Proposition 3.4.1:
  * (⇒). `is-reflective→counit-is-iso`{.Agda}
  * (⇐). `is-counit-iso→is-reflective`{.Agda}

* Definition 3.4.4: `is-equivalence`{.Agda}

### 3.5 Reflective subcategories

<!--
```agda
_ = is-reflective
```
-->

* Definition 3.5.2: `is-reflective`{.Agda}

### 3.6 Epireflective subcategories

<!--
```agda
_ = is-epireflective
_ = epireflective+strong-mono→unit-invertible
_ = factor+strong-mono-unit-invertible→epireflective
_ = is-strong-epireflective
_ = strong-epireflective+mono→unit-invertible
_ = factor+mono-unit-invertible→strong-epireflective
```
-->

* Definition 3.6.1: `is-epireflective`{.Agda}
* Proposition 3.6.2:
  * (1 ⇒ 2): `epireflective+strong-mono→unit-invertible`{.Agda}
  * (2 ⇒ 1): `factor+strong-mono-unit-invertible→epireflective`{.Agda}
* Definition 3.6.2: `is-strong-epireflective`{.Agda}
* Proposition 3.6.4:
  * (1 ⇒ 2): `strong-epireflective+mono→unit-invertible`{.Agda}
  * (2 ⇒ 1): `factor+mono-unit-invertible→strong-epireflective`{.Agda}

### 3.7 Kan extensions

<!--
```agda
_ = is-lan
_ = is-ran
_ = cocomplete→lan
_ = ff→pointwise-lan-ext
_ = left-adjoint→preserves-lan
_ = is-initial-cocone→is-colimit
_ = is-colimit→is-initial-cocone
_ = is-colimit→is-initial-cocone
_ = adjoint→is-lan-id
_ = adjoint→is-absolute-lan
```
-->

* Definition 3.7.1: `is-lan`{.Agda}
* Theorem 3.7.2: `cocomplete→lan`{.Agda}
* Proposition 3.7.3: `ff→pointwise-lan-ext`{.Agda}
* Proposition 3.7.4: `left-adjoint→preserves-lan`{.Agda}
* Proposition 3.7.5:
  * (⇒) `is-initial-cocone→is-colimit`{.Agda}
  * (⇐) `is-colimit→is-initial-cocone`{.Agda}
* Proposition 3.7.6:
  * (1 ⇒ 2) `adjoint→is-lan-id`{.Agda}, `adjoint→is-absolute-lan`{.Agda}

### 3.8 Tensor products of set-valued functors

### 3.9 Exercises

<!--
```agda
_ = right-adjoint→objectwise-rep
_ = corepresentable→left-adjoint
_ = Karoubi-is-completion
```
-->

* Exercise 3.9.2:
  * (⇒) `corepresentable→left-adjoint`{.Agda}
  * (⇐) `right-adjoint→objectwise-rep`{.Agda}
* Exercise 3.9.3: `Karoubi-is-completion`{.Agda}

## 4 Generators and Projectives

### 4.1 Well-powered categories

### 4.2 Intersection and union

### 4.3 Strong epimorphisms

<!--
```agda
_ = is-regular-epi
_ = is-strong-epi
_ = ∘-is-strong-epic
_ = strong-epi-cancelr
_ = strong-epi+mono→invertible
_ = is-regular-epi→is-strong-epi
_ = is-strong-epi→is-extremal-epi
_ = equaliser-lifts→is-strong-epi
_ = is-extremal-epi→is-strong-epi
```
-->

* Definition 4.3.1: `is-regular-epi`{.Agda}
* Definition 4.3.5: `is-strong-epi`{.Agda}
* Proposition 4.3.6:
  * 1. `∘-is-strong-epic`{.Agda}
  * 2. `strong-epi-cancelr`{.Agda}
  * 3. `strong-epi-mono→invertible`{.Agda}
  * 4. `is-regular-epi→is-strong-epi`{.Agda}
  * 5. `is-strong-epi→is-extremal-epi`{.Agda}
* Proposition 4.3.7:
  * 1. `equaliser-lifts→is-strong-epi`{.Agda}
  * 2. `is-extremal-epi→is-strong-epi`{.Agda}

### 4.4 Epi-mono factorizations

### 4.5 Generators

<!--
```agda
_ = is-separating-family
_ = is-separator
_ = separating-family→epi
_ = epi→separating-family
_ = is-strong-separating-family
_ = is-regular-separating-family
_ = is-dense-separating-family
_ = is-dense-separator
_ = dense-separator→regular-separator
_ = regular-separator→strong-separator
_ = is-jointly-faithful
_ = is-jointly-conservative
_ = separating-family→jointly-faithful
_ = jointly-faithful→separating-family
_ = separator→faithful
_ = faithful→separator
_ = strong-separating-family→jointly-conservative
_ = lex+jointly-conservative→strong-separating-family
_ = strong-separator→conservative
_ = lex+conservative→strong-separator
_ = equalisers+jointly-conservative→separating-family
_ = dense-separating-family→jointly-ff
_ = jointly-ff→dense-separating-family
_ = zero+separating-family→separator
```
-->

* Definition 4.5.1:
  * `is-separating-family`{.Agda}
  * `is-separator`{.Agda}
* Proposition 5.4.2:
  * (⇒) `separating-family→epic`{.Agda}
  * (⇐) `epic→separating-family`{.Agda}
* Definition 4.5.3:
  * `is-strong-separating-family`{.Agda}
  * `is-regular-separating-family`{.Agda}
* Definition 4.5.4:
  * `is-dense-separating-family`{.Agda}
  * `is-dense-separator`{.Agda}
* Proposition 4.5.5:
  * `dense-separator→regular-separator`{.Agda}
  * `regular-separator→strong-separator`{.Agda}
* Definition 4.5.7:
  * `is-jointly-faithful`{.Agda}
  * `is-jointly-conservative`{.Agda}
* Proposition 4.5.8:
  * (⇒) `separating-family→jointly-faithful`{.Agda}
  * (⇐) `jointly-faithful→separating-family` {.Agda}
* Proposition 4.5.9:
  * (⇒) `separator→faithful`{.Agda}
  * (⇐) `faithful→separator`{.Agda}
* Proposition 4.5.10:
  * (⇒) `strong-separating-family→jointly-conservative`{.Agda}
  * (⇐) `lex+jointly-conservative→strong-separating-family`{.Agda}
* Proposition 4.5.11:
  * (⇒) `strong-separator→conservative`{.Agda}
  * (⇐) `lex+conservative→strong-separator`{.Agda}
* Proposition 4.5.12: `equalisers+jointly-conservative→separating-family`{.Agda}
* Proposition 4.5.14
  * (⇒) `dense-separating-family→jointly-ff`{.Agda}
  * (⇐) `jointly-ff→dense-separating-family`{.Agda}
* Proposition 4.5.16: `zero+separating-family→separator`{.Agda}

### 4.6 Projectives

::: warning
Borceux uses the term "projective" to refer to [[strong projectives]].
:::

<!--
```agda
_ = is-strong-projective
_ = preserves-strong-epis→strong-projective
_ = strong-projective→preserves-strong-epis
_ = indexed-coproduct-strong-projective
_ = retract→strong-projective
_ = Strong-projectives
_ = strong-projective-separating-faily→strong-projectives
_ = zero+indexed-coproduct-strong-projective→strong-projective
```
-->

* Definition 4.6.1: `is-strong-projective`{.Agda}
* Proposition 4.6.2:
  Note that there is a slight typo in Borceux here: $\cC(P,-)$
  must preserve [[strong epimorphisms]].
  (⇒) `preserves-strong-epis→strong-projective`{.Agda}
  (⇐) `strong-projective→preserves-strong-epis`{.Agda}
* Proposition 4.6.3: `indexed-coproduct-strong-projective`{.Agda}
* Proposition 4.6.4: `retract→strong-projective`{.Agda}
* Definition 4.6.5: `Strong-projectives`{.Agda}
* Proposition 4.6.6: `strong-projective-separating-faily→strong-projectives`{.Agda}
* Proposition 4.6.7:
  * (⇒) `zero+indexed-coproduct-strong-projective→strong-projective`{.Agda}
  * (⇐) `indexed-coproduct-strong-projective`{.Agda}

### 4.7 Injective cogenerators

### 4.8 Exercises

## 5 Categories of fractions

### 5.1 Graphs and path categories

<!--
```agda
_ = Graph
_ = Graph-hom
_ = Path-in
_ = Path-category
_ = Free-category
_ = Marked-graph
_ = Marked-graphs
_ = Marked-free-category
```
-->

* Definition 5.1.1: `Graph`{.Agda}
* Definition 5.1.2: `Graph-hom`{.Agda}
* Definition 5.1.3: `Path-in`{.Agda}
* Proposition 5.1.4: `Path-category`{.Agda}, `Free-category`{.Agda}
* Definition 5.1.5: `Marked-graph`{.Agda}, `Marked-graphs`{.Agda}
* Proposition 5.1.6: `Marked-free-category`{.Agda}

### 5.2 Calculus of fractions

<!--
```agda
_ = Localisation
```
-->

* Proposition 5.2.2: `Localisation`{.Agda}

### 5.3 Reflective subcategories as categories of fractinos

### 5.4 The orthogonal subcategory problem

<!--
```agda
_ = Orthogonal
_ = object-orthogonal-!-orthogonal
_ = in-subcategory→orthogonal-to-inverted
_ = orthogonal-to-ηs→in-subcategory
_ = in-subcategory→orthogonal-to-ηs
```
-->

* Definition 5.4.1: `m⊥m`{.Agda}
* Definition 5.4.2:
  1. `Orthogonal`{.Agda}
  2. `Orthogonal`{.Agda}
* Proposition 5.4.3: `object-orthogonal-!-orthogonal`{.Agda}
* Proposition 5.4.4:
  * 1.
    * (a ⇒ b) `in-subcategory→orthogonal-to-inverted`{.Agda}
    * (a ⇒ c) `in-subcategory→orthogonal-to-ηs`{.Agda}

### 5.5 Factorisation systems

<!--
```agda
_ = is-ofs
_ = factorisation-essentially-unique
_ = L-is-⊥R
_ = in-intersection≃is-iso
```
-->

* Definition 5.5.1: `is-factorisation-system`{.Agda}
* Proposition 5.5.2: `factorisation-essentially-unique`{.Agda}
* Proposition 5.5.3: 🚧 `E-is-⊥M`{.Agda}
* Proposition 5.5.4:
  * 3. `in-intersection≃is-iso`{.Agda}

### 5.6 The case of localisations

### 5.7 Universal closure operations

### 5.8 The calculus of bidense morphisms

### 5.9 Exercises

## 6 Flat functors and Cauchy completeness

### 6.1 Exact functors

<!--
```agda
_ = is-lex
```
-->

* Definition 6.1.1: `is-lex`{.Agda}

### 6.2 Left exact reflection of a functor

### 6.3 Flat functors

### 6.4 The relevance of regular cardinals

### 6.5 The splitting of idempotents

<!--
```agda
_ = is-idempotent
_ = is-split→is-idempotent
_ = is-split
_ = is-idempotent-complete
```
-->

* Definition 6.5.1: `is-idempotent`{.Agda}
* Proposition 6.5.2: `is-split→is-idempotent`{.Agda}
* Definition 6.5.3: `is-split`{.Agda}
* Definition 6.5.8: `is-idempotent-complete`{.Agda}
* Proposition 6.5.9: `Karoubi-is-completion`{.Agda}

### 6.6 The more general adjoint functor theorem

### 6.7 Exercises

## 7 Bicategories and distributors

### 7.1 2-categories

### 7.2 2-functors and 2-natural transformations

### 7.3 Modifications and n-categories

### 7.4 2-limits and bilimits

### 7.5 Lax functors and pseudo-functors

### 7.6 Lax limits and pseudo-limits

### 7.7 Bicategories

<!--
```agda
_ = Prebicategory
_ = Adjointᵇ._⊣_
_ = Spanᵇ
```
-->

* Definition 7.7.1: `Prebicategory`{.Agda}
* Definition 7.7.2: `Adjointᵇ._⊣_`{.Agda}
* Example 7.7.3: `Spanᵇ`{.Agda}

### 7.8 Distributors

### 7.9 Cauchy completeness versus distributors

### 7.10 Exercises

## 8 Internal category theory

### 8.1 Internal categories and functors

<!--
```agda
_ = Internal-cat
_ = Internal-functor
_ = _=>i_
_ = Disci
_ = _^opi
```
-->

* Definition 8.1.1: `Internal-cat`{.Agda}
* Definition 8.1.2: `Internal-functor`{.Agda}
* Definition 8.1.3: `_=>i_`{.Agda}
* Examples 8.1.6:
  * a. `Disci`{.Agda}
  * c. `_^opi`{.Agda}

### 8.2 Internal base-valued functors

<!--
```agda
_ = Outer-functor
_ = _=>o_
_ = Outer-functors
_ = ConstO
_ = const-nato
```
-->

* Definition 8.2.1: `Outer-functor`{.Agda}
* Definition 8.2.2: `_=>o_`{.Agda}
* Proposition 8.2.3: `Outer-functors`{.Agda}
* Example 8.2.4: `ConstO`{.Agda}, `const-nato`{.Agda}

### 8.3 Internal limits and colimits

### 8.4 Exercises
* Exercise 8.4.6:
  * (⇒) `dependent-product→lcc`{.Agda}
  * (⇐) `lcc→dependent-product`{.Agda}
