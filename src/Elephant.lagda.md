---
description: |
    Lemmas and theorems from Peter Johnstone's "Sketches of an Elephant"
---
<!--
```agda
open import Cat.Instances.Elements.Covariant
open import Cat.Functor.Adjoint.Reflective
open import Cat.Site.Instances.Canonical
open import Cat.CartesianClosed.Locally
open import Cat.Functor.Monadic.Crude
open import Cat.Diagram.Limit.Finite
open import Cat.Diagram.Exponential
open import Cat.Diagram.Congruence
open import Cat.Instances.Karoubi
open import Cat.Instances.Sheaves
open import Cat.Functor.Algebra
open import Cat.Site.Closure
open import Cat.Site.Base
open import Cat.Regular

open import Topoi.Base
```
-->
```agda
module Elephant where
```

# Sketching the elephant

Though the 1Lab is not purely a formalization of category theory, it does
aim to be a useful reference on the subject. However, the 1Lab organizes
content in a highly non-linear fashion; this can make it somewhat difficult
to use as a companion to more traditional resources.

This page attempts to (somewhat) rectify this situation by gathering all
of the results from "Sketches of an Elephant – A Topos Theory Compendium"
[@Elephant] in a single place.^[It also serves as an excellent place to
find possible contributions!]

# A. Toposes as categories

## A1 Regular and cartesian closed categories

### A1.1 Preliminary assumptions

<!--
```agda
_ = FG-iso→is-reflective
_ = crude-monadicity
_ = ∫
_ = Karoubi-is-completion
_ = lambek
```
-->

* Lemma 1.1.1: `FG-iso→is-reflective`{.Agda}
* Lemma 1.1.2: `crude-monadicity`{.Agda}
* Lemma 1.1.4: `lambek`{.Agda}
* Proposition 1.1.7: `∫`{.Agda}
* Lemma 1.1.8: `Karoubi-is-completion`{.Agda}

### A1.2 Cartesian Categories

<!--
```agda
_ = Finitely-complete→is-finitely-complete
_ = with-equalisers
_ = with-pullbacks
```
-->

* Lemma 1.2.1:
  i.   `Finitely-complete→is-finitely-complete`{.Agda}
  iii. `with-equalisers`{.Agda}
  iv.  `with-pullbacks`{.Agda}

### A1.3 Regular Categories

<!--
```agda
_ = is-strong-epi→is-regular-epi
_ = is-congruence
```
-->

* Proposition 1.3.4: `is-strong-epi→is-regular-epi`{.Agda}
* Definition 1.3.6: `is-congruence`{.Agda}

### A1.4 Coherent Categories

### A1.5 Cartesian closed categories

<!--
```agda
_ = exponentiable→constant-family⊣product
_ = dependent-product→lcc
_ = lcc→dependent-product
```
-->

* Lemma 1.5.2:
  i. (⇐) `exponentiable→constant-family⊣product`{.Agda}
* Corollary 1.5.3:
  (⇒) `dependent-product→lcc`{.Agda}
  (⇐) `lcc→dependent-product`{.Agda}

### A1.6 Subobject classifiers

# C Toposes as spaces

## C2 Sheaves on a site

### C2.1 Sites and coverages

<!--
```agda
_ = Coverage
_ = Patch
_ = is-separated₁
_ = is-sheaf
_ = is-separated
_ = is-sheaf-maximal
_ = is-sheaf-factor
_ = is-sheaf-transitive
_ = is-colim
_ = is-universal-colim
```
-->

* Definition 2.1.1: `Coverage`{.Agda}
* Definition 2.1.2:
  * *Compatible families*: `Patch`{.Agda}
  * *Separated presheaves*: `is-separated₁`{.Agda}
  * *Sheaves on a site*: `is-sheaf`{.Agda}, `is-separated`{.Agda}
* Lemma 2.1.5: `is-sheaf-maximal`{.Agda}
* Lemma 2.1.6: `is-sheaf-factor`{.Agda}
* Lemma 2.1.7: `is-sheaf-transitive`{.Agda}, though see the warning there.
* Example 2.1.12, *(universally) effective-epimorphic sieves*: `is-colim`{.Agda}, `is-universal-colim`{.Agda}

### C2.2 The topos of sheaves

See [[topos of sheaves]].

<!--
```agda
_ = Sheafification-is-reflective
_ = Sh[]-is-complete
_ = Sh[]-is-cocomplete
_ = Sh[]-cc
```
-->

* Proposition 2.2.6:
  * *Reflectivity*: `Sheafification-is-reflective`{.Agda}
  * *Completeness*: `Sh[]-is-complete`{.Agda}
  * *Cocompleteness*: `Sh[]-is-cocomplete`{.Agda}
  * *Cartesian closure*: `Sh[]-cc`{.Agda}
