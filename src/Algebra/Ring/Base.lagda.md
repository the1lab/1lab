```agda
open import Algebra.Group.Ab
open import Algebra.Prelude
open import Algebra.Group

module Algebra.Ring.Base where
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

A **ring** is an [abelian group] $R$, together with a distinguished
point $1 : R$ to be called the **multiplicative unit**, and a
**multiplication** homomorphism $· : R \otimes R \to R$, such that $·$
has $1$ as a left/right unit, and it is associative. That is: A ring is
a [monoid], but described "on an abelian group" rather than "on a set"

[abelian group]: Algebra.Group.Ab.html
[monoid]: Algebra.Monoid.html

```agda
record Ring ℓ : Type (lsuc ℓ) where
  no-eta-equality
  field
    group : AbGroup ℓ
```

<!--
```agda
  open Group-on (group .object .snd)
    renaming ( unit to R0
             ; _⋆_ to _+_
             ; _—_ to _-_
             ; _⁻¹ to -_
             ; idl to +-idl
             ; idr to +-idr
             ; associative to +-assoc
             ; inversel to +-invl
             ; inverser to +-invr
             )
    public
  R : Type ℓ
  R = group .object .fst
```
-->

```agda
  field
    1R  : R
    *-hom : Ab.Hom (group ⊗ group) group
```

The fact that `_*_`{.Agda} is defined as a map out of the [tensor
product] abelian group means that it is a _bilinear map_ --- meaning
that multiplication and addition satisfy a _distributivity_ equality,
which is familiar from our example of $\bb{Z}$ before: $x(y + z) =
xy + xz$. Since rings are not necessarily commutative, we note that the
symmetric equation holds as well: $(y+z)x = yz + xz$.

[tensor product]: Algebra.Group.Ab.html#the-tensor-product

```agda
  _*_ : R → R → R
  x * y = *-hom .fst (x :, y)

  field
    *-idl : ∀ {x} → 1R * x ≡ x
    *-idr : ∀ {x} → x * 1R ≡ x
    *-assoc : ∀ {x y z} → (x * y) * z ≡ x * (y * z)

  *-distribl : ∀ {x y z} → x * (y + z) ≡ (x * y) + (x * z)
  *-distribl {x} {y} {z} =
    x * (y + z)                       ≡⟨⟩
    *-hom .fst (x :, (y + z))         ≡⟨ ap (*-hom .fst) (sym t-fixl) ⟩
    *-hom .fst ((x :, y) :+ (x :, z)) ≡⟨ *-hom .snd .Group-hom.pres-⋆ _ _ ⟩
    (x * y) + (x * z)                 ∎

  *-distribr : ∀ {x y z} → (y + z) * x ≡ (y * x) + (z * x)
  *-distribr {x} {y} {z} =
    (y + z) * x                       ≡⟨⟩
    *-hom .fst ((y + z) :, x)         ≡⟨ ap (*-hom .fst) (sym t-fixr) ⟩
    *-hom .fst ((y :, x) :+ (z :, x)) ≡⟨ *-hom .snd .Group-hom.pres-⋆ _ _ ⟩
    (y * x) + (z * x)                 ∎
```

## The elementary description

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
  from-make-ring : Ring ℓ
  from-make-ring = ring where
    Rg : AbGroup ℓ
    Rg .object .fst = R
    Rg .object .snd =
      make-group ring-is-set 0R _+_ -_ (λ _ _ _ → +-assoc) (λ _ → +-comm ∙ +-invr) (λ _ → +-invr) λ _ → +-idl
    Rg .witness x y = +-comm {x} {y}

    ring : Ring ℓ
    ring .Ring.group = Rg
    ring .Ring.1R = 1R
    ring .Ring.*-hom = from-multilinear-map {A = Rg} {Rg} {Rg} _*_
      (λ _ _ _ → *-distribr) λ _ _ _ → *-distribl
    ring .Ring.*-idl = *-idl
    ring .Ring.*-idr = *-idr
    ring .Ring.*-assoc = *-assoc

open make-ring using (from-make-ring) public
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

# Ring homomorphisms

There is a natural notion of ring homomorphism, which we get by smashing
together that of monoid homomorphism (for the multiplicative part) and
of group homomorphism; Every map of rings has an underlying map of
groups which preserves the addition operation, and it must also preserve
the multiplication.

```agda
record Ring-hom {ℓ} (R S : Ring ℓ) : Type ℓ where
  no-eta-equality
  private
    module R = Ring R
    module S = Ring S

  field
    map : R.R → S.R
    pres-* : ∀ x y → map (x R.* y) ≡ map x S.* map y
    pres-+ : ∀ x y → map (x R.+ y) ≡ map x S.+ map y
    pres-1 : map R.1R ≡ S.1R

  group-hom : Ab.Hom R.group S.group
  group-hom = map , record { pres-⋆ = pres-+ }

  open Group-hom (group-hom .snd) hiding (pres-⋆)
    renaming ( pres-id to pres-0 ; pres-inv to pres-neg ; pres-diff to pres-sub )
    public

open Ring-hom
```

<!--
```agda
Ring-hom-path
  : ∀ {ℓ} {R S : Ring ℓ} {f g : Ring-hom R S}
  → f .map ≡ g .map → f ≡ g
Ring-hom-path {R = R} {S} {f} {g} fg = f≡g where
  module S = Ring S
  module R = Ring R
  f≡g : f ≡ g
  f≡g i .Ring-hom.map = fg i
  f≡g i .Ring-hom.pres-* x y =
    is-prop→pathp (λ i → S.has-is-set (fg i (x R.* y)) (fg i x S.* fg i y)) (f .pres-* _ _) (g .pres-* _ _) i
  f≡g i .Ring-hom.pres-+ x y =
    is-prop→pathp (λ i → S.has-is-set (fg i (x R.+ y)) (fg i x S.+ fg i y)) (f .pres-+ _ _) (g .pres-+ _ _) i
  f≡g i .Ring-hom.pres-1 =
    is-prop→pathp (λ i → S.has-is-set (fg i R.1R) S.1R) (f .pres-1) (g .pres-1) i
private unquoteDecl eqv = declare-record-iso eqv (quote Ring-hom)
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
  precat : Precategory _ _
  precat .Ob = Ring _
  precat .Hom = Ring-hom
  precat .Hom-set a b = goal where abstract
    module a = Ring a
    module b = Ring b

    goal : is-set (Ring-hom a b)
    goal = is-hlevel≃ 2 (Iso→Equiv eqv e⁻¹) (hlevel 2)

  precat .id = rh where
    rh : Ring-hom _ _
    rh .map x = x
    rh .pres-* _ _ = refl
    rh .pres-+ _ _ = refl
    rh .pres-1 = refl
  precat ._∘_ f g = h  where
    h : Ring-hom _ _
    h .map x = f .map (g .map x)
    h .pres-* _ _ = ap (f .map) (g .pres-* _ _) ∙ f .pres-* _ _
    h .pres-+ _ _ = ap (f .map) (g .pres-+ _ _) ∙ f .pres-+ _ _
    h .pres-1 = ap (f .map) (g .pres-1) ∙ f .pres-1
  precat .idr f = Ring-hom-path refl
  precat .idl f = Ring-hom-path refl
  precat .assoc f g h = Ring-hom-path refl
```
-->
