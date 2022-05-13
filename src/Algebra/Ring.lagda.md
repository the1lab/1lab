```agda
open import Algebra.Group.Ab
open import Algebra.Prelude
open import Algebra.Monoid
open import Algebra.Group
open import Algebra.Semigroup

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
record is-ring {ℓ} {R : Type ℓ} (1R : R) (_*_ _+_ : R → R → R) : Type ℓ where
  no-eta-equality
  field
    *-monoid : is-monoid 1R _*_
    +-group  : is-group _+_
    +-commutes : ∀ {x y} → x + y ≡ y + x
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
             ; inversel to +-invl
             ; inverser to +-invr
             ; associative to +-associative
             ; idl to *-idl
             ; idr to *-idr
             )
    public

record Ring-on {ℓ} (R : Type ℓ) : Type ℓ where
  field
    1R : R
    _*_ _+_ : R → R → R
    has-is-ring : is-ring 1R _*_ _+_

  open is-ring has-is-ring public

instance
  H-Level-is-ring
    : ∀ {ℓ} {R : Type ℓ} {1R : R} {_*_ _+_ : R → R → R} {n}
    → H-Level (is-ring 1R _*_ _+_) (suc n)
  H-Level-is-ring {1R = 1R} {_*_} {_+_} =
    prop-instance {T = is-ring 1R _*_ _+_} $ λ where
      x y i .*-monoid   → hlevel 1 (x .*-monoid) (y .*-monoid) i
      x y i .+-group    → hlevel 1 (x .+-group) (y .+-group) i
      x y i .+-commutes → x .+-group .is-group.has-is-set _ _ (x .+-commutes) (y .+-commutes) i
      x y i .*-distribl → x .+-group .is-group.has-is-set _ _ (x .*-distribl) (y .*-distribl) i
      x y i .*-distribr → x .+-group .is-group.has-is-set _ _ (x .*-distribr) (y .*-distribr) i
    where open is-ring

Ring : ∀ ℓ → Type (lsuc ℓ)
Ring _ = Σ Ring-on
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
    pres-id : f A.1R ≡ B.1R
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
      field[ 1R          by pres-id ]
      axiom[ has-is-ring by (λ _ → prop) ]))
  where
    open Ring-on
    open is-ring-hom
    -- if you try to use (λ _ → hlevel 1) in the record-desc, even with
    -- an explicit {T = is-ring _ _ _} argument, Agda gets an internal
    -- error at src/full/Agda/TypeChecking/Unquote.hs:511:20
    prop : ∀ {A : Type ℓ} {1R : A} {_*_ _+_ : A → A → A}
         → is-prop (is-ring 1R _*_ _+_)
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
    goal = Σ-is-hlevel 2 (hlevel 2) λ f → hlevel 2

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

    -- R is a monoid:
    1R      : R
    _*_     : R → R → R
    *-idl   : ∀ {x} → 1R * x ≡ x
    *-idr   : ∀ {x} → x * 1R ≡ x
    *-assoc : ∀ {x y z} → (x * y) * z ≡ x * (y * z)

    -- Multiplication is bilinear:
    *-distribl : ∀ {x y z} → x * (y + z) ≡ (x * y) + (x * z)
    *-distribr : ∀ {x y z} → (y + z) * x ≡ (y * x) + (z * x)
```

<!--
```agda
  from-make-ring-on : Ring-on R
  from-make-ring-on = ring where
    open is-ring hiding (-_ ; +-invr ; +-invl ; *-distribl ; *-distribr ; *-idl ; *-idr)

    -- All in copatterns to prevent the unfolding from exploding on you
    ring : Ring-on R
    ring .Ring-on.1R = 1R
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
Zero-ring = from-make-ring {R = ⊤} $ record
  { ring-is-set = λ _ _ _ _ _ _ → tt
  ; 0R         = tt
  ; _+_        = λ _ _ → tt
  ; -_         = λ _ → tt
  ; +-idl      = λ _ → tt
  ; +-invr     = λ _ → tt
  ; +-assoc    = λ _ → tt
  ; +-comm     = λ _ → tt
  ; 1R         = tt
  ; _*_        = λ _ _ → tt
  ; *-idl      = λ _ → tt
  ; *-idr      = λ _ → tt
  ; *-assoc    = λ _ → tt
  ; *-distribl = λ _ → tt
  ; *-distribr = λ _ → tt
  }
```
