<!--
```agda
{-# OPTIONS -vtc.def.fun:10 #-}
open import Algebra.Group.Cat.Base
open import Algebra.Semigroup
open import Algebra.Group.Ab hiding (ℤ)
open import Algebra.Prelude
open import Algebra.Monoid
open import Algebra.Group

open import Cat.Instances.Delooping
open import Cat.Abelian.Base

open import Data.Int.Properties
open import Data.Int.Base

import Cat.Reasoning
```
-->

```agda
module Algebra.Ring where
```

# Rings {defines=ring}

The **ring** is one of the basic objects of study in algebra, which
abstracts the best bits of the common algebraic structures: The integers
$\bb{Z}$, the rationals $\bb{Q}$, the reals $\bb{R}$, and the complex
numbers $\bb{C}$ are all rings, as are the collections of polynomials
with coefficients in any of those. Less familiar examples of rings
include square matrices (with values in a ring) and the integral
cohomology ring of a topological space: that these are so far from being
"number-like" indicates the incredible generality of rings.

A **ring** is an [[abelian group]] $R$ (which we call the **additive
group** of $R$), together with the data of a monoid on $R$ (the
**multiplicative monoid**), where the multiplication of the monoid
_distributes over_ the addition. We'll see why this compatibility
condition is required afterwards. Check out what it means for a triple
$(1, *, +)$ to be a ring structure on a type:

```agda
record is-ring {ℓ} {R : Type ℓ} (1r : R) (_*_ _+_ : R → R → R) : Type ℓ where
  no-eta-equality
  field
    *-monoid : is-monoid 1r _*_
    +-group  : is-abelian-group _+_
    *-distribl : ∀ {x y z} → x * (y + z) ≡ (x * y) + (x * z)
    *-distribr : ∀ {x y z} → (y + z) * x ≡ (y * x) + (z * x)
```

<!--
```agda
  open is-monoid *-monoid
    renaming ( idl to *-idl
             ; idr to *-idr
             ; associative to *-associative
             )
    hiding (has-is-set ; magma-hlevel ; underlying-set)
    public

  open is-abelian-group +-group
    renaming ( _—_ to _-_
             ; inverse to -_
             ; 1g to 0r
             ; inversel to +-invl
             ; inverser to +-invr
             ; associative to +-associative
             ; idl to +-idl
             ; idr to +-idr
             ; commutes to +-commutes
             )
    public

  additive-group : Group ℓ
  ∣ additive-group .fst ∣                    = R
  additive-group .fst .is-tr                 = is-abelian-group.has-is-set +-group
  additive-group .snd .Group-on._⋆_          = _+_
  additive-group .snd .Group-on.has-is-group = is-abelian-group.has-is-group +-group

  group : Abelian-group ℓ
  ∣ group .fst ∣                         = R
  group .fst .is-tr                      = is-abelian-group.has-is-set +-group
  group .snd .Abelian-group-on._*_       = _+_
  group .snd .Abelian-group-on.has-is-ab = +-group

  Ringoid : Ab-category (B record { _⋆_ = _*_ ; has-is-monoid = *-monoid })
  Ringoid .Ab-category.Abelian-group-on-hom _ _ = record { has-is-ab = +-group }
  Ringoid .Ab-category.∘-linear-l f g h = sym *-distribr
  Ringoid .Ab-category.∘-linear-r f g h = sym *-distribl

  private
    module ringoid = Ab-category Ringoid
      using ( ∘-zero-l ; ∘-zero-r ; neg-∘-l ; neg-∘-r ; ∘-minus-l ; ∘-minus-r )

  open ringoid renaming
      ( ∘-zero-l to *-zerol
      ; ∘-zero-r to *-zeror
      ; neg-∘-l to neg-*-l
      ; neg-∘-r to neg-*-r
      ; ∘-minus-l to *-minus-l
      ; ∘-minus-r to *-minus-r
      )
    public

  module m = Cat.Reasoning (B record { _⋆_ = _*_ ; has-is-monoid = *-monoid })
    hiding (module HLevel-instance)
  module a = Abelian-group-on record { has-is-ab = +-group }

record Ring-on {ℓ} (R : Type ℓ) : Type ℓ where
  field
    1r : R
    _*_ _+_ : R → R → R
    has-is-ring : is-ring 1r _*_ _+_

  open is-ring has-is-ring public
  infixl 25 _*_
  infixl 20 _+_

instance
  H-Level-is-ring
    : ∀ {ℓ} {R : Type ℓ} {1r : R} {_*_ _+_ : R → R → R} {n}
    → H-Level (is-ring 1r _*_ _+_) (suc n)
  H-Level-is-ring {1r = 1r} {_*_} {_+_} =
    prop-instance {T = is-ring 1r _*_ _+_} $ λ where
      x y i .*-monoid   → hlevel 1 (x .*-monoid) (y .*-monoid) i
      x y i .+-group    → hlevel 1 (x .+-group) (y .+-group) i
      x y i .*-distribl → x .+-group .is-abelian-group.has-is-set _ _ (x .*-distribl) (y .*-distribl) i
      x y i .*-distribr → x .+-group .is-abelian-group.has-is-set _ _ (x .*-distribr) (y .*-distribr) i
    where open is-ring
```
-->

There is a natural notion of ring homomorphism, which we get by smashing
together that of a monoid homomorphism (for the multiplicative part) and
of group homomorphism; Every map of rings has an underlying map of
groups which preserves the addition operation, and it must also preserve
the multiplication. This encodes the view of a ring as an "abelian group
with a monoid structure".

```agda
record is-ring-hom
  {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (R : Ring-on A) (S : Ring-on B)
  (f : A → B)
  : Type (ℓ ⊔ ℓ') where
  private
    module A = Ring-on R
    module B = Ring-on S

  field
    pres-id : f A.1r ≡ B.1r
    pres-+  : ∀ x y → f (x A.+ y) ≡ f x B.+ f y
    pres-*  : ∀ x y → f (x A.* y) ≡ f x B.* f y
```

<!--
```agda
  ring-hom→group-hom : is-group-hom (A.additive-group .snd) (B.additive-group .snd) f
  ring-hom→group-hom = record { pres-⋆ = pres-+ }

  module gh = is-group-hom ring-hom→group-hom renaming (pres-id to pres-0 ; pres-inv to pres-neg)
  open gh using (pres-0 ; pres-neg ; pres-diff) public

private unquoteDecl eqv = declare-record-iso eqv (quote is-ring-hom)

module _ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} {R : Ring-on A} {S : Ring-on B} where
  open Ring-on R using (magma-hlevel)
  open Ring-on S using (magma-hlevel)

  instance abstract
    H-Level-ring-hom : ∀ {f n} → H-Level (is-ring-hom R S f) (suc n)
    H-Level-ring-hom = prop-instance λ x y → Iso→is-hlevel 1 eqv (hlevel 1) x y

open is-ring-hom
```
-->

It follows, by standard equational nonsense, that rings and ring
homomorphisms form a precategory --- for instance, we have $f(g(1_R)) =
f(1_S) = 1_T$.

```agda
Ring-structure : ∀ ℓ → Thin-structure ℓ Ring-on
Ring-structure ℓ .is-hom f x y = el! (is-ring-hom x y f)
Ring-structure ℓ .id-is-hom .pres-id = refl
Ring-structure ℓ .id-is-hom .pres-+ x y = refl
Ring-structure ℓ .id-is-hom .pres-* x y = refl
Ring-structure ℓ .∘-is-hom f g α β .pres-id = ap f (β .pres-id) ∙ α .pres-id
Ring-structure ℓ .∘-is-hom f g α β .pres-+ x y = ap f (β .pres-+ x y) ∙ α .pres-+ _ _
Ring-structure ℓ .∘-is-hom f g α β .pres-* x y = ap f (β .pres-* x y) ∙ α .pres-* _ _
Ring-structure ℓ .id-hom-unique α β i .Ring-on.1r = α .pres-id i
Ring-structure ℓ .id-hom-unique α β i .Ring-on._*_ x y = α .pres-* x y i
Ring-structure ℓ .id-hom-unique α β i .Ring-on._+_ x y = α .pres-+ x y i
Ring-structure ℓ .id-hom-unique {s = s} {t} α β i .Ring-on.has-is-ring =
  is-prop→pathp
    (λ i → hlevel {T = is-ring (α .pres-id i)
      (λ x y → α .pres-* x y i) (λ x y → α .pres-+ x y i)} 1)
    (s .Ring-on.has-is-ring) (t .Ring-on.has-is-ring) i

Rings : ∀ ℓ → Precategory (lsuc ℓ) ℓ
Rings _ = Structured-objects (Ring-structure _)
module Rings {ℓ} = Cat.Reasoning (Rings ℓ)

Ring : ∀ ℓ → Type (lsuc ℓ)
Ring ℓ = Rings.Ob
```

## In components

We give a more elementary description of rings, which is suitable for
_constructing_ values of the record type `Ring`{.Agda} above. This
re-expresses the data included in the definition of a ring with the
least amount of redundancy possible, in the most direct terms
possible: A ring is a set, equipped with two binary operations $*$ and
$+$, such that $*$ distributes over $+$ on either side; $+$ is an
abelian group; and $*$ is a monoid.

```agda
record make-ring {ℓ} (R : Type ℓ) : Type ℓ where
  no-eta-equality
  field
    ring-is-set : is-set R

    -- R is an abelian group:
    0R      : R
    _+_     : R → R → R
    -_      : R → R
    +-idl   : ∀ {x} → 0R + x ≡ x
    +-invr  : ∀ {x} → x + (- x) ≡ 0R
    +-assoc : ∀ {x y z} → x + (y + z) ≡ (x + y) + z
    +-comm  : ∀ {x y} → x + y ≡ y + x

    -- R is a commutative monoid:
    1R      : R
    _*_     : R → R → R
    *-idl   : ∀ {x} → 1R * x ≡ x
    *-idr   : ∀ {x} → x * 1R ≡ x
    *-assoc : ∀ {x y z} → x * (y * z) ≡ (x * y) * z

    -- Multiplication is bilinear:
    *-distribl : ∀ {x y z} → x * (y + z) ≡ (x * y) + (x * z)
    *-distribr : ∀ {x y z} → (y + z) * x ≡ (y * x) + (z * x)
```

<!--
```agda
  to-ring-on : Ring-on R
  to-ring-on = ring where
    open is-ring hiding (-_ ; +-invr ; +-invl ; *-distribl ; *-distribr ; *-idl ; *-idr ; +-idl ; +-idr)

    -- All in copatterns to prevent the unfolding from exploding on you
    ring : Ring-on R
    ring .Ring-on.1r = 1R
    ring .Ring-on._*_ = _*_
    ring .Ring-on._+_ = _+_
    ring .Ring-on.has-is-ring .*-monoid .has-is-semigroup .is-semigroup.has-is-magma = record { has-is-set = ring-is-set }
    ring .Ring-on.has-is-ring .*-monoid .has-is-semigroup .is-semigroup.associative = *-assoc
    ring .Ring-on.has-is-ring .*-monoid .idl = *-idl
    ring .Ring-on.has-is-ring .*-monoid .idr = *-idr
    ring .Ring-on.has-is-ring .+-group .is-abelian-group.has-is-group .is-group.unit = 0R
    ring .Ring-on.has-is-ring .+-group .is-abelian-group.has-is-group .is-group.has-is-monoid .has-is-semigroup .has-is-magma = record { has-is-set = ring-is-set }
    ring .Ring-on.has-is-ring .+-group .is-abelian-group.has-is-group .is-group.has-is-monoid .has-is-semigroup .associative = +-assoc
    ring .Ring-on.has-is-ring .+-group .is-abelian-group.has-is-group .is-group.has-is-monoid .idl = +-idl
    ring .Ring-on.has-is-ring .+-group .is-abelian-group.has-is-group .is-group.has-is-monoid .idr = +-comm ∙ +-idl
    ring .Ring-on.has-is-ring .+-group .is-abelian-group.has-is-group .is-group.inverse = -_
    ring .Ring-on.has-is-ring .+-group .is-abelian-group.has-is-group .is-group.inversel = +-comm ∙ +-invr
    ring .Ring-on.has-is-ring .+-group .is-abelian-group.has-is-group .is-group.inverser = +-invr
    ring .Ring-on.has-is-ring .+-group .is-abelian-group.commutes = +-comm
    ring .Ring-on.has-is-ring .is-ring.*-distribl = *-distribl
    ring .Ring-on.has-is-ring .is-ring.*-distribr = *-distribr

  to-ring : Ring ℓ
  to-ring .fst = el R ring-is-set
  to-ring .snd = to-ring-on

open make-ring using (to-ring ; to-ring-on) public
```
-->

This data is missing (by design, actually!) one condition which we would
expect: $0 \ne 1$. We exploit this to give our first example of a ring,
the **zero ring**, which has carrier set the `unit`{.Agda ident=⊤} ---
the type with one object.

Despite the name, the zero ring is not the [zero object] in the category
of rings: it is the [[terminal object]]. In the category of rings, the
initial object is the ring $\bb{Z}$, which is very far (infinitely far!)
from having a single element. It's called the "zero ring" because it has
one element $x$, which must be the additive identity, hence we call it
$0$. But it's also the multiplicative identity, so we might also call
the ring $\{*\}$ the _One Ring_, which would be objectively cooler.

[zero object]: Cat.Diagram.Zero.html

```agda
Zero-ring : Ring lzero
Zero-ring = to-ring {R = ⊤} λ where
  .make-ring.ring-is-set _ _ _ _ _ _ → tt
  .make-ring.0R → tt
  .make-ring._+_ _ _ → tt
  .make-ring.-_  _ → tt
  .make-ring.+-idl _ → tt
  .make-ring.+-invr _ → tt
  .make-ring.+-assoc _ → tt
  .make-ring.+-comm _ → tt
  .make-ring.1R → tt
  .make-ring._*_ _ _ → tt
  .make-ring.*-idl _ → tt
  .make-ring.*-idr _ → tt
  .make-ring.*-assoc _ → tt
  .make-ring.*-distribl _ → tt
  .make-ring.*-distribr _ → tt
```

Rings, unlike other categories of algebraic structures (like that of
[groups] or [abelian groups]), are structured enough to differentiate
between the initial and terminal objects. As mentioned above, the
initial object is the ring $\bb{Z}$, and the terminal ring is the zero
ring. As for why this happens, consider that, since ring homomorphisms
must preserve the unit^[being homomorphisms for the additive group, they
automatically preserve zero], it is impossible to have a ring
homomorphism $h : 0 \to R$ unless $0 = h(0) = h(1) = 1$ in $R$.

[groups]: Algebra.Group.html
[abelian groups]: Algebra.Group.Ab.html

```agda
ℤ : Ring lzero
ℤ = to-ring {R = Int} λ where
  .make-ring.ring-is-set → hlevel 2
  .make-ring.0R → 0
  .make-ring._+_ → _+ℤ_
  .make-ring.-_ → negℤ
  .make-ring.+-idl      → +ℤ-zerol _
  .make-ring.+-invr {x} → +ℤ-invr x
  .make-ring.+-assoc {x} {y} {z} → +ℤ-assoc x y z
  .make-ring.+-comm {x} {y} → +ℤ-commutative x y
  .make-ring.1R    → 1
  .make-ring._*_   → _*ℤ_
  .make-ring.*-idl → *ℤ-onel _
  .make-ring.*-idr → *ℤ-oner _
  .make-ring.*-assoc    {x} {y} {z} → *ℤ-associative x y z
  .make-ring.*-distribl {x} {y} {z} → *ℤ-distribl x y z
  .make-ring.*-distribr {x} {y} {z} → *ℤ-distribr x y z
```
