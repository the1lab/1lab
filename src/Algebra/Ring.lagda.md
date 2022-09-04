```agda
{-# OPTIONS -vtc.def.fun:10 #-}
open import Algebra.Semigroup
open import Algebra.Group.Ab
open import Algebra.Prelude
open import Algebra.Monoid
open import Algebra.Group

open import Cat.Instances.Delooping
open import Cat.Abelian.Base

open import Data.Int

import Cat.Reasoning

module Algebra.Ring where
```

# Rings

The **ring** is one of the basic objects of study in algebra, which
abstracts the best bits of the common algebraic structures: The integers
$\bb{Z}$, the rationals $\bb{Q}$, the reals $\bb{R}$, and the complex
numbers $\bb{C}$ are all rings, as are the collections of polynomials
with coefficients in any of those. Less familiar examples of rings
include square matrices (with values in a ring) and the integral
cohomology ring of a topological space: that these are so far from being
"number-like" indicates the incredible generality of rings.

A **ring** is an [abelian group] $R$ (which we call the **additive
group** of $R$), together with the data of a monoid on $R$ (the
**multiplicative monoid**), where the multiplication of the monoid
_distributes over_ the addition. We'll see why this compatibility
condition is required afterwards. Check out what it means for a triple
$(1, *, +)$ to be a ring structure on a type:

[abelian group]: Algebra.Group.Ab.html

```agda
record is-ring {ℓ} {R : Type ℓ} (1r : R) (_*_ _+_ : R → R → R) : Type ℓ where
  no-eta-equality
  field
    *-monoid : is-monoid 1r _*_
    +-group  : is-group _+_
    +-commutes : ∀ {x y} → x + y ≡ y + x
    *-commutes : ∀ {x y} → x * y ≡ y * x
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

  open is-group +-group
    renaming ( _—_ to _-_
             ; inverse to -_
             ; unit to 0r
             ; inversel to +-invl
             ; inverser to +-invr
             ; associative to +-associative
             ; idl to +-idl
             ; idr to +-idr
             )
    public

  additive-group : Group ℓ
  additive-group = (R , record { _⋆_ = _+_ ; has-is-group = +-group })

  Ringoid : Ab-category (B record { _⋆_ = _*_ ; has-is-monoid = *-monoid })
  Ringoid .Ab-category.Group-on-hom _ _ = additive-group .snd
  Ringoid .Ab-category.Hom-grp-ab _ _ f g = +-commutes
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
  module a = AbGrp (restrict additive-group λ _ _ → +-commutes)

record Ring-on {ℓ} (R : Type ℓ) : Type ℓ where
  field
    1r : R
    _*_ _+_ : R → R → R
    has-is-ring : is-ring 1r _*_ _+_

  open is-ring has-is-ring public

instance
  H-Level-is-ring
    : ∀ {ℓ} {R : Type ℓ} {1r : R} {_*_ _+_ : R → R → R} {n}
    → H-Level (is-ring 1r _*_ _+_) (suc n)
  H-Level-is-ring {1r = 1r} {_*_} {_+_} =
    prop-instance {T = is-ring 1r _*_ _+_} $ λ where
      x y i .*-monoid   → hlevel 1 (x .*-monoid) (y .*-monoid) i
      x y i .+-group    → hlevel 1 (x .+-group) (y .+-group) i
      x y i .+-commutes → x .+-group .is-group.has-is-set _ _ (x .+-commutes) (y .+-commutes) i
      x y i .*-commutes → x .+-group .is-group.has-is-set _ _ (x .*-commutes) (y .*-commutes) i
      x y i .*-distribl → x .+-group .is-group.has-is-set _ _ (x .*-distribl) (y .*-distribl) i
      x y i .*-distribr → x .+-group .is-group.has-is-set _ _ (x .*-distribr) (y .*-distribr) i
    where open is-ring

Ring : ∀ ℓ → Type (lsuc ℓ)
Ring _ = Σ (Type _) Ring-on
```
-->

There is a natural notion of ring homomorphism, which we get by smashing
together that of a monoid homomorphism (for the multiplicative part) and
of group homomorphism; Every map of rings has an underlying map of
groups which preserves the addition operation, and it must also preserve
the multiplication. This encodes the view of a ring as an "abelian group
with a monoid structure".

```agda
record is-ring-hom {ℓ} (A B : Ring ℓ) (f : A .fst → B .fst) : Type ℓ where
  private
    module A = Ring-on (A .snd)
    module B = Ring-on (B .snd)

  field
    pres-id : f A.1r ≡ B.1r
    pres-+  : ∀ x y → f (x A.+ y) ≡ f x B.+ f y
    pres-*  : ∀ x y → f (x A.* y) ≡ f x B.* f y
```

<!--
```agda
private unquoteDecl eqv = declare-record-iso eqv (quote is-ring-hom)

module _ {ℓ} {A B : Ring ℓ} where
  open Ring-on (A .snd) using (magma-hlevel)
  open Ring-on (B .snd) using (magma-hlevel)

  instance abstract
    H-Level-ring-hom : ∀ {f n} → H-Level (is-ring-hom A B f) (suc n)
    H-Level-ring-hom = prop-instance λ x y → is-hlevel≃ 1 ((Iso→Equiv eqv) e⁻¹) (hlevel 1) x y

is-ring≃ : ∀ {ℓ} (A B : Ring ℓ) (e : A .fst ≃ B .fst) → Type ℓ
is-ring≃ A B (f , _) = is-ring-hom A B f

Ring-univalent : ∀ {ℓ} → is-univalent (HomT→Str (is-ring≃ {ℓ}))
Ring-univalent {ℓ = ℓ} =
  Derive-univalent-record (record-desc
    (Ring-on {ℓ = ℓ}) is-ring≃
    (record:
      field[ _*_         by pres-* ]
      field[ _+_         by pres-+ ]
      field[ 1r          by pres-id ]
      axiom[ has-is-ring by (λ _ → prop) ]))
  where
    open Ring-on
    open is-ring-hom
    -- if you try to use (λ _ → hlevel 1) in the record-desc, even with
    -- an explicit {T = is-ring _ _ _} argument, Agda gets an internal
    -- error at src/full/Agda/TypeChecking/Unquote.hs:511:20
    prop : ∀ {A : Type ℓ} {1r : A} {_*_ _+_ : A → A → A}
         → is-prop (is-ring 1r _*_ _+_)
    prop = hlevel 1
```
-->

It follows, by standard equational nonsense, that rings and ring
homomorphisms form a precategory --- for instance, we have $f(g(1_R)) =
f(1_S) = 1_T$.

```agda
Rings : ∀ ℓ → Precategory (lsuc ℓ) ℓ
```

<!--
```agda
Rings ℓ = precat where
  open Precategory
  open is-ring-hom

  precat : Precategory _ _
  precat .Ob = Ring _
  precat .Hom A B = Σ[ f ∈ (A .fst → B .fst) ] (is-ring-hom A B f)
  precat .Hom-set A B = goal where abstract
    open Ring-on (A .snd) using (magma-hlevel)
    open Ring-on (B .snd) using (magma-hlevel)
    goal : is-set (Σ[ f ∈ (A .fst → B .fst) ] (is-ring-hom A B f))
    goal = hlevel 2

  precat .id = (λ x → x) , rh where
    rh : is-ring-hom _ _ _
    rh .pres-* _ _ = refl
    rh .pres-+ _ _ = refl
    rh .pres-id    = refl
  precat ._∘_ f g = (λ x → f .fst (g .fst x)) , h where
    h : is-ring-hom _ _ _
    h .pres-* _ _ = ap (f .fst) (g .snd .pres-* _ _) ∙ f .snd .pres-* _ _
    h .pres-+ _ _ = ap (f .fst) (g .snd .pres-+ _ _) ∙ f .snd .pres-+ _ _
    h .pres-id    = ap (f .fst) (g .snd .pres-id) ∙ f .snd .pres-id
  precat .idr {A} f = Σ-prop-path (λ f → hlevel 1) refl
    where open Ring-on (A .snd) using (magma-hlevel)
  precat .idl {A} f = Σ-prop-path (λ _ → hlevel 1) refl
    where open Ring-on (A .snd) using (magma-hlevel)
  precat .assoc {z = Z} f g h = Σ-prop-path (λ _ → hlevel 1) refl
    where open Ring-on (Z .snd) using (magma-hlevel)
module Rings {ℓ} = Precategory (Rings ℓ)
```
-->

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
    +-assoc : ∀ {x y z} → (x + y) + z ≡ x + (y + z)
    +-comm  : ∀ {x y} → x + y ≡ y + x

    -- R is a commutative monoid:
    1r      : R
    _*_     : R → R → R
    *-idl   : ∀ {x} → 1r * x ≡ x
    *-idr   : ∀ {x} → x * 1r ≡ x
    *-assoc : ∀ {x y z} → (x * y) * z ≡ x * (y * z)
    *-comm  : ∀ {x y} → x * y ≡ y * x

    -- Multiplication is bilinear:
    *-distribl : ∀ {x y z} → x * (y + z) ≡ (x * y) + (x * z)
    *-distribr : ∀ {x y z} → (y + z) * x ≡ (y * x) + (z * x)
```

<!--
```agda
  from-make-ring-on : Ring-on R
  from-make-ring-on = ring where
    open is-ring hiding (-_ ; +-invr ; +-invl ; *-distribl ; *-distribr ; *-idl ; *-idr ; +-idl ; +-idr)

    -- All in copatterns to prevent the unfolding from exploding on you
    ring : Ring-on R
    ring .Ring-on.1r = 1r
    ring .Ring-on._*_ = _*_
    ring .Ring-on._+_ = _+_
    ring .Ring-on.has-is-ring .*-monoid .has-is-semigroup .is-semigroup.has-is-magma = record { has-is-set = ring-is-set }
    ring .Ring-on.has-is-ring .*-monoid .has-is-semigroup .is-semigroup.associative = sym *-assoc
    ring .Ring-on.has-is-ring .*-monoid .idl = *-idl
    ring .Ring-on.has-is-ring .*-monoid .idr = *-idr
    ring .Ring-on.has-is-ring .+-group .is-group.unit = 0R
    ring .Ring-on.has-is-ring .+-group .is-group.has-is-monoid .has-is-semigroup .has-is-magma = record { has-is-set = ring-is-set }
    ring .Ring-on.has-is-ring .+-group .is-group.has-is-monoid .has-is-semigroup .associative = sym +-assoc
    ring .Ring-on.has-is-ring .+-group .is-group.has-is-monoid .idl = +-idl
    ring .Ring-on.has-is-ring .+-group .is-group.has-is-monoid .idr = +-comm ∙ +-idl
    ring .Ring-on.has-is-ring .+-group .is-group.inverse = -_
    ring .Ring-on.has-is-ring .+-group .is-group.inversel = +-comm ∙ +-invr
    ring .Ring-on.has-is-ring .+-group .is-group.inverser = +-invr
    ring .Ring-on.has-is-ring .+-commutes = +-comm
    ring .Ring-on.has-is-ring .is-ring.*-distribl = *-distribl
    ring .Ring-on.has-is-ring .is-ring.*-distribr = *-distribr
    ring .Ring-on.has-is-ring .is-ring.*-commutes = *-comm

  from-make-ring : Ring ℓ
  from-make-ring = R , from-make-ring-on

open make-ring using (from-make-ring ; from-make-ring-on) public
```
-->

This data is missing (by design, actually!) one condition which we would
expect: $0 \ne 1$. We exploit this to give our first example of a ring,
the **zero ring**, which has carrier set the `unit`{.Agda ident=⊤} ---
the type with one object.

Despite the name, the zero ring is not the [zero object] in the category
of rings: it is the [terminal object]. In the category of rings, the
initial object is the ring $\bb{Z}$, which is very far (infinitely far!)
from having a single element. It's called the "zero ring" because it has
one element $x$, which must be the additive identity, hence we call it
$0$. But it's also the multiplicative identity, so we might also call
the ring $\{*\}$ the _One Ring_, which would be objectively cooler.

[terminal object]: Cat.Diagram.Terminal.html
[zero object]: Cat.Diagram.Zero.html

```agda
Zero-ring : Ring lzero
Zero-ring = from-make-ring {R = ⊤} λ where
  .make-ring.ring-is-set _ _ _ _ _ _ → tt
  .make-ring.0R → tt
  .make-ring._+_ _ _ → tt
  .make-ring.-_  _ → tt
  .make-ring.+-idl _ → tt
  .make-ring.+-invr _ → tt
  .make-ring.+-assoc _ → tt
  .make-ring.+-comm _ → tt
  .make-ring.1r → tt
  .make-ring._*_ _ _ → tt
  .make-ring.*-idl _ → tt
  .make-ring.*-idr _ → tt
  .make-ring.*-assoc _ → tt
  .make-ring.*-distribl _ → tt
  .make-ring.*-distribr _ → tt
  .make-ring.*-comm _ → tt
```

Rings, unlike other categories of algebraic structures (like that of
[groups] or [abelian groups]), are structured enough to differentiate
between the initial and terminal objects. As mentioned above, the
initial object is the ring $\bb{Z}$, and the terminal ring is the zero
ring. As for why this happens, consider that, since ring homomorphisms
must preserve the unit[^being homomorphisms for the additive group, they
automatically preserve zero], it is impossible to have a ring
homomorphism $h : 0 \to R$ unless $0 = h(0) = h(1) = 1$ in $R$.

[groups]: Algebra.Group.html
[abelian groups]: Algebra.Group.Ab.html

```agda
ℤ : Ring lzero
ℤ = from-make-ring {R = Int} λ where
  .make-ring.ring-is-set → hlevel 2
  .make-ring.0R → 0
  .make-ring._+_ → _+ℤ_
  .make-ring.-_ → negate
  .make-ring.+-idl → +ℤ-zerol _
  .make-ring.+-invr {x} → +ℤ-inverser x
  .make-ring.+-assoc {x} {y} {z} → +ℤ-associative x y z
  .make-ring.+-comm {x} {y} → +ℤ-commutative x y
  .make-ring.1r → 1
  .make-ring._*_ → _*ℤ_
  .make-ring.*-idl → *ℤ-idl _
  .make-ring.*-idr → *ℤ-idr _
  .make-ring.*-assoc {x} {y} {z} → *ℤ-associative x y z
  .make-ring.*-distribl {x} {y} {z} → *ℤ-distrib-+ℤ-l x y z
  .make-ring.*-distribr {x} {y} {z} → *ℤ-distrib-+ℤ-r x y z
  .make-ring.*-comm {x} {y} → *ℤ-commutative x y
```
