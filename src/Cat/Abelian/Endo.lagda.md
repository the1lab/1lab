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

# Endomorphism rings {defines="endomorphism-ring"}

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
  mr .+-idl _ = A.Hom.idl
  mr .+-invr _ = A.Hom.inverser
  mr .+-assoc _ _ _ = A.Hom.associative
  mr .+-comm _ _ = A.Hom.commutes
  mr .*-idl _ = A.idl _
  mr .*-idr _ = A.idr _
  mr .*-assoc _ _ _ = A.assoc _ _ _
  mr .*-distribl _ _ _ = sym (A.∘-linear-r _ _ _)
  mr .*-distribr _ _ _ = sym (A.∘-linear-l _ _ _)
```

This is a fantastic source of non-commutative rings, and indeed the
justification for allowing them at all. Even for the relatively simple
case of $\cA = \Ab$, it is an open problem to characterise the
abelian groups with commutative endomorphism rings.
