<!--
```agda
open import Algebra.Ring

open import Cat.Abelian.Base
open import Cat.Prelude
```
-->

```agda
module Cat.Abelian.Endo {o ℓ} {C : Precategory o ℓ} (A : Ab-category C) where
```

<!--
```agda
private module A = Ab-category A
```
-->

# Endomorphism rings

Fix an [$\Ab$-category] $\cA$: It can be the category of [[abelian
groups]] $\Ab$ itself, for example, or $R$-Mod for your favourite
ring^[We tacitly assume the reader has a favourite ring.]. Because
composition in $\cA$ distributes over addition, the collection of
endomorphisms of any particular object $x : \cA$ is not only a monoid,
but a _ring_: the **endomorphism ring** of $x$.

[$\Ab$-category]: Cat.Abelian.Base.html#ab-enriched-categories

```agda
Endo : A.Ob → Ring ℓ
Endo x = to-ring mr where
  open make-ring
  mr : make-ring (A.Hom x x)
  mr .ring-is-set = A.Hom-set x x
  mr .0R = A.0m
  mr .1R = A.id
  mr .make-ring._+_ = A._+_
  mr .make-ring.-_ = A.Hom.inverse
  mr .make-ring._*_ = A._∘_
  mr .+-idl = A.Hom.idl
  mr .+-invr = A.Hom.inverser
  mr .+-assoc = A.Hom.associative
  mr .+-comm = A.Hom.commutes
  mr .*-idl = A.idl _
  mr .*-idr = A.idr _
  mr .*-assoc = A.assoc _ _ _
  mr .*-distribl = sym (A.∘-linear-r _ _ _)
  mr .*-distribr = sym (A.∘-linear-l _ _ _)
```

This is a fantastic source of non-commutative rings, and indeed the
justification for allowing them at all. Even for the relatively simple
case of $\cA = \Ab$, it is an open problem to characterise the
abelian groups with commutative endomorphism rings.
