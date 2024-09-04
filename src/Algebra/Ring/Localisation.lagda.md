<!--
```agda
open import 1Lab.Prelude hiding (_*_ ; _+_ ; _-_)

open import Algebra.Ring.Commutative
open import Algebra.Ring.Solver
open import Algebra.Ring

open import Data.Set.Coequaliser hiding (_/_)
```
-->

```agda
module Algebra.Ring.Localisation where
```

# Localisations of commutative rings {defines="localisation-of-a-ring"}

The **localisation** $R\loc{S}$ of a commutative [[ring]] $R$ at a set
of elements $S$ is the universal solution to forcing the elements of $S$
to become invertible, analogously to how [[localisations of a
category||localisation]] $\cC$ universally invert a class of maps in
$\cC$. Explicitly, it is a commutative ring $R\loc{S}$, equipped with a
homomorphism $1/- : R \to R\loc{S}$ which sends elements $s \in S$ to
*invertible* elements $s/1 : R\loc{S}$, and which is initial among
these.

The elements of $R\loc{S}$ are given by formal *fractions*, which we
will write $r/s$, with $r, s : R$ and $s \in S$. Type-theoretically,
such a fraction is really a *triple*, since we must also consider the
witness $w : s \in S$ that the denominator belongs to $S$; but, since
these proofs do not matter for identity of fractions, we will generally
omit them in the prose.

```agda
record Fraction {ℓ ℓ'} {R : Type ℓ} (S : R → Type ℓ') : Type (ℓ ⊔ ℓ') where
  no-eta-equality ; pattern
  constructor _/_[_]
  field
    num   : R
    denom : R
    has-denom : denom ∈ S
```

<!--
```agda
open Fraction renaming (num to ↑ ; denom to ↓)

pattern _/_ x y = x / y [ _ ]

instance
  Inductive-Fraction
    : ∀ {ℓ ℓ' ℓ'' ℓm} {R : Type ℓ} {S : R → Type ℓ'} {P : Fraction S → Type ℓ''}
    → ⦃ _ : Inductive ((num : ⌞ R ⌟) (denom : ⌞ R ⌟) (has : denom ∈ S) → P (num / denom [ has ])) ℓm ⦄
    → Inductive ((x : Fraction S) → P x) ℓm
  Inductive-Fraction ⦃ r ⦄ .Inductive.methods        = r .Inductive.methods
  Inductive-Fraction ⦃ r ⦄ .Inductive.from f (x / s [ p ]) = r .Inductive.from f x s p

Fraction-path
  : ∀ {ℓ ℓ'} {R : Type ℓ} {S : ⌞ R ⌟ → Type ℓ'}
  → ⦃ _ : ∀ {x} → H-Level (S x) 1 ⦄ {x y : Fraction S}
  → ↑ x ≡ ↑ y → ↓ x ≡ ↓ y → x ≡ y
Fraction-path {S = S} {x = x / s [ p ]} {y / t [ q ] } α β i = record
  { num = α i
  ; denom = β i
  ; has-denom = is-prop→pathp (λ i → hlevel {T = S (β i)} 1) p q i
  }
```
-->

<!--
```agda
module Frac {ℓ} (R : CRing ℓ) where
  open Explicit (R .snd)
  open CRing R
```
-->

To ensure that we have a well-behaved theory of fractions, we will
require that $S$ is a **multiplicatively closed** subset of $R$. In
particular, the presence of $1 \in S$ allows us to form the fractions
$r/1$ for any $r : R$, thus ensuring we have a map $R \to R\loc{S}$. We
also require that, if $s \in S$ and $s' \in S$, then also $ss' \in S$.
This will be important to define both multiplication *and identity* of
fractions.

```agda
  record is-multiplicative {ℓ'} (S : ⌞ R ⌟ → Type ℓ') : Type (ℓ ⊔ ℓ') where
    field
      has-1 : 1r ∈ S
      has-* : ∀ {x y} → x ∈ S → y ∈ S → (x * y) ∈ S
```

Under the assumption that $S$ is multiplicatively closed, we could
attempt to mimic the usual operations on integer-valued fractions on our
fractions, for example, defining the sum $x/s + y/t$ to be $(xt+ys)/st$.
This turns out not to work too well: for example, if we then also define
$-x/s = (-x)/s$, we would have $x/s + -x/s$ equal to

$$
\frac{xs + (-x)s}{s^2} = \frac{(x - x)s}{s^2} = \frac{0}{s^2}
$$

which is not *literally* the zero fraction $0/1$. However, we still have
$0s^2 = 0*1$, so these fractions "represent the same quantity" --- they
both stand for *zero times* the formal inverse of something. We could
then try to identify fractions $x/s$ and $y/t$ whenever $xt = ys$, but,
in a general ring $R$, this relation fails to be transitive, so it can
not be equality in a set. Therefore, we allow an "adjustment" by one of
our formal denominators: the equivalence relation we will impose on
fractions identifies $x/s \approx y/t$ whenever there exists $u \in S$
with $uxt = uys$.

```agda
  data _≈_ {ℓ'} {S : ⌞ R ⌟ → Type ℓ'} (x y : Fraction S) : Type (ℓ ⊔ ℓ') where
    inc : (u : ⌞ R ⌟) (u∈S : u ∈ S) → u * ↑ x * ↓ y ≡ u * ↑ y * ↓ x → x ≈ y
    squash : is-prop (x ≈ y)
```

<!--
```agda
  {-
  We define _≈_ as a data type so it's injective. It could also be a
  record, but then we'd have to truncate the record in a separate step.
  -}

  instance
    Inductive-≈
      : ∀ {ℓ' ℓ'' ℓm} {S : ⌞ R ⌟ → Type ℓ'} {x y : Fraction S} {P : x ≈ y → Type ℓ''}
      → ⦃ h : ∀ {x} → H-Level (P x) 1 ⦄
      → ⦃ r : Inductive ((u : ⌞ R ⌟) (u∈S : u ∈ S) (p : u * ↑ x * ↓ y ≡ u * ↑ y * ↓ x) → P (inc u u∈S p)) ℓm ⦄
      → Inductive ((p : x ≈ y) → P p) ℓm
    Inductive-≈ ⦃ h ⦄ ⦃ r ⦄ .Inductive.methods = r .Inductive.methods
    Inductive-≈ {S = S} {x} {y} {P} ⦃ h ⦄ ⦃ r ⦄ .Inductive.from f = go (r .Inductive.from f) where
      go
        : ((u : ⌞ R ⌟) (u∈S : u ∈ S) (p : u * ↑ x * ↓ y ≡ u * ↑ y * ↓ x) → P (inc u u∈S p))
        → ∀ x → P x
      go m (inc u u∈S x) = m u u∈S x
      go m (squash x y i) = is-prop→pathp (λ i → hlevel {T = P (squash x y i)} 1) (go m x) (go m y) i

    H-Level-≈ : ∀ {ℓ'} {S : ⌞ R ⌟ → Type ℓ'} {x y : Fraction S} {n} → H-Level (x ≈ y) (suc n)
    H-Level-≈ = prop-instance squash
```
-->

In the literature, this is more commonly phrased as $u(xt - ys) = 0$,
but the equivalence between that and our definition is routine.

```agda
  _≈'_ : ∀ {ℓ'} {S : ⌞ R ⌟ → Type ℓ'} → Fraction S → Fraction S → Type _
  _≈'_ {S = S} (x / s) (y / t) = ∃[ u ∈ R ] (u ∈ S × u * (x * t - y * s) ≡ 0r)
```

<details>
<summary>The calculation can be found in this `<details>`{.html} block.</summary>

```agda
  ≈→≈' : ∀ {ℓ'} {S : ⌞ R ⌟ → Type ℓ'} {x y : Fraction S} → x ≈ y → x ≈' y
  ≈→≈' {x = x / s} {y = y / t} = elim! λ u u∈S p →
    let
      prf =
        u * (x * t - y * s)   ≡⟨ solve 5 (λ u x t y s → u :* (x :* t :- y :* s) ≔ u :* x :* t :- u :* y :* s) u x t y s refl ⟩
        u * x * t - u * y * s ≡⟨ ap₂ _-_ refl (sym p) ⟩
        u * x * t - u * x * t ≡⟨ solve 1 (λ x → x :- x ≔ 0) (u * x * t) refl ⟩
        0r                    ∎
    in inc (u , u∈S , prf)

  ≈'→≈ : ∀ {ℓ'} {S : ⌞ R ⌟ → Type ℓ'} {x y : Fraction S} → x ≈' y → x ≈ y
  ≈'→≈ {x = x / s} {y = y / t} = elim! λ u u∈S p →
    let
      prf =
        u * x * t - u * y * s ≡⟨ solve 5 (λ u x t y s → u :* x :* t :- u :* y :* s ≔ u :* (x :* t :- y :* s)) u x t y s refl ⟩
        u * (x * t - y * s)   ≡⟨ p ⟩
        0r                    ∎
    in inc u u∈S (zero-diff prf)
```

</details>

<!--
```agda
module Loc {ℓ} (R : CRing ℓ) (S : ⌞ R ⌟ → Ω) (mult : Frac.is-multiplicative R (_∈ S)) where
  open Frac.is-multiplicative mult
  open Explicit (R .snd)
  open CRing R
  open Frac R public

  open Congruence using (_∼_ ; has-is-prop ; reflᶜ ; _∙ᶜ_ ; symᶜ)
```
-->

Our next step is showing that this relation is actually an equivalence
relation. The proof of transitivity is the most interesting step: we
assume that $vxt = vys$ and $wyu = wzt$, with "adjustments" by $v, w \in
S$ respectively, but we produce the equation $(wvt)xu = (wvt)zs$ --- we
must consider the denominator of the middle fraction $y/t$ to relate the
two endpoints $x/s$ and $z/u$.

```agda
  Fraction-congruence : Congruence (Fraction (_∈ S)) _
  Fraction-congruence ._∼_ = _≈_
  Fraction-congruence .has-is-prop (_ / _) (_ / _) = hlevel 1
  Fraction-congruence .reflᶜ {x / s} = inc 1r has-1 refl
  Fraction-congruence .symᶜ {x / s} {y / t} = rec! λ u u∈S p → inc u u∈S (sym p)
  Fraction-congruence ._∙ᶜ_ {x / s} {y / t [ r ]} {z / u} = elim!
    λ v v∈S p w w∈S q →
      let
        prf =
          w * v * t * x * u     ≡⟨ cring! R ⟩
          w * u * (v * x * t)   ≡⟨ ap (w * u *_) p ⟩
          w * u * (v * y * s)   ≡⟨ cring! R ⟩
          (w * y * u) * (v * s) ≡⟨ ap₂ _*_ q refl ⟩
          (w * z * t) * (v * s) ≡⟨ cring! R ⟩
          w * v * t * z * s     ∎
      in
      inc (w * v * t) (has-* (has-* w∈S v∈S) r) prf
```

<!--
```agda
  module Fr = Congruence Fraction-congruence
  open Fraction

  private
    /-ap : ∀ {x y : Fraction (_∈ S)} → x .num ≡ y .num → x .denom ≡ y .denom → Path Fr.quotient (inc x) (inc y)
    /-ap p q = ap Coeq.inc (Fraction-path p q)
```
-->

We then define $R\loc{S}$ to be the set of fractions $r/s$, identified
according to this relation. Since $1 \in S$, we can immediately cough up
the function $x \mapsto x/1$, mapping $R \to R\loc{W}$.

```agda
  _/1 : ⌞ R ⌟ → Fr.quotient
  x /1 = inc (x / 1r [ has-1 ])
```

To define the operations of a ring on $R\loc{W}$, we first define them
at the level of fractions:

::: mathpar

$$
\frac{x}{s} + \frac{y}{t} = \frac{xt + ys}{st}
$$

$$
-\frac{x}{s} = \frac{-x}{s}
$$

$$
\frac{x}{s}\frac{y}{t} = \frac{xy}{st}
$$

:::

As mentioned above, these operations do not satisfy the laws of a ring
*on the set of fractions*. We must therefore prove that they respect the
quotient we've taken, and then prove that they satisfy the ring laws *on
the quotient*.

```agda
  +f : Fraction (_∈ S) → Fraction (_∈ S) → Fraction (_∈ S)
  +f (x / s [ p ]) (y / t [ q ]) = (x * t + y * s) / (s * t) [ has-* p q ]

  -f : Fraction (_∈ S) → Fraction (_∈ S)
  -f (x / s [ p ]) = (- x) / s [ p ]

  *f : Fraction (_∈ S) → Fraction (_∈ S) → Fraction (_∈ S)
  *f (x / s [ p ]) (y / t [ q ]) = (x * y) / (s * t) [ has-* p q ]
```

<details>
<summary>Showing that these operations descend to the quotient is
entirely routine algebra; However, the calculations *do* get pretty
long, so we'll leave them in this `<details>`{.html} block.</summary>

```agda
  -ₗ_ : Fr.quotient → Fr.quotient
  -ₗ_ = Quot-elim (λ _ → hlevel 2) (λ x → inc (-f x)) -f-resp where abstract
    -f-resp : ∀ x y → x ≈ y → Path Fr.quotient (inc (-f x)) (inc (-f y))
    -f-resp (x / s) (y / t) = elim! λ u u∈S p →
      let
        prf =
          u * (- x) * t ≡⟨ ap (_* t) (sym neg-*-r) ∙ sym neg-*-l ⟩
          - (u * x * t) ≡⟨ ap -_ p ⟩
          - (u * y * s) ≡⟨ neg-*-l ∙ ap (_* s) neg-*-r ⟩
          u * (- y) * s ∎
      in quot (inc u u∈S prf)

  _+ₗ_ : Fr.quotient → Fr.quotient → Fr.quotient
  _+ₗ_ = Fr.op₂-comm +f (λ a b → Fr.reflᶜ' (+f-comm a b)) +f-resp where abstract
    +f-comm : ∀ u v → +f u v ≡ +f v u
    +f-comm (x / s) (y / t) = Fraction-path +-commutes *-commutes

    +f-resp : ∀ x u v → u ≈ v → +f x u ≈ +f x v
    +f-resp (x / s) (u / y) (v / z) = rec! λ w w∈S p →
      let
        prf =
          w * (x * y + u * s) * (s * z)             ≡⟨ cring! R ⟩
          w * x * y * s * z + s * s * ⌜ w * u * z ⌝ ≡⟨ ap! p ⟩
          w * x * y * s * z + s * s * ⌜ w * v * y ⌝ ≡⟨ cring! R ⟩
          w * (x * z + v * s) * (s * y)             ∎
      in inc w w∈S prf

  _*ₗ_ : Fr.quotient → Fr.quotient → Fr.quotient
  _*ₗ_ = Fr.op₂-comm *f *f-comm *f-resp where abstract
    *f-comm : ∀ u v → *f u v ≈ *f v u
    *f-comm (x / s) (y / t) = inc 1r has-1 (solve 4 (λ x y t s → 1 :* (x :* y) :* (t :* s) ≔ 1 :* (y :* x) :* (s :* t)) x y t s refl)

    *f-resp : ∀ x u v → u ≈ v → *f x u ≈ *f x v
    *f-resp (x / s) (u / y) (v / z) = rec! λ w w∈S p →
      let
        prf =
          w * (x * u) * (s * z) ≡⟨ cring! R ⟩
          s * x * (w * u * z)   ≡⟨ ap (s * x *_) p ⟩
          s * x * (w * v * y)   ≡⟨ cring! R ⟩
          w * (x * v) * (s * y) ∎
      in inc w w∈S prf
```
</details>

```agda
  infixl 8 _+ₗ_
  infixl 9 _*ₗ_
  infix 10 -ₗ_ _/1

  0ₗ 1ₗ : Fr.quotient
  0ₗ = 0r /1
  1ₗ = 1r /1
```

We choose the zero and identity elements for $R\loc{S}$ so that the
localising map $R \to R\loc{S}$ preserves them definitionally. We're
almost done with the construction; while there's quite a bit of algebra
left to do to show that we have a ring, this is almost entirely
automatic. As a warm-up, we can prove that $x/1$ is inverted by $1/x$
whenever $x \in S$.

```agda
  /1-inverts : ∀ x (p : x ∈ S) → inc (1r / x [ p ]) *ₗ (x /1) ≡ 1ₗ
  /1-inverts x p = quot (inc 1r has-1
    (solve 1 (λ x → 1 :* (1 :* x) :* 1 ≔ 1 :* 1 :* (x :* 1)) x refl))
```

The actual proof obligation is shown above: we have to establish that $1
* (1 * x) * 1 = 1 * 1 * (x * 1)$, which can be shown by a naïve solver.
The equations for each of the ring laws are similarly boring:

```agda
  abstract
    +ₗ-idl : ∀ x → 0ₗ +ₗ x ≡ x
    +ₗ-idl = elim! λ x s _ → /-ap
      (solve 2 (λ s x → 0 :* s :+ x :* 1 ≔ x) s x refl)
      *-idl

    +ₗ-invr : ∀ x → x +ₗ (-ₗ x) ≡ 0ₗ
    +ₗ-invr = elim! λ x s _ → quot (inc 1r has-1 (solve 2
      (λ x s → 1 :* (x :* s :+ (:- x) :* s) :* 1 ≔ 1 :* 0 :* (s :* s)) x s refl))

    +ₗ-assoc : ∀ x y z → x +ₗ (y +ₗ z) ≡ (x +ₗ y) +ₗ z
    +ₗ-assoc = elim! λ x s _ y t _ z u _ → /-ap
      (solve 6 (λ x y z s t u →
        x :* (t :* u) :+ (y :* u :+ z :* t) :* s
      ≔ (x :* t :+ y :* s) :* u :+ z :* (s :* t)) x y z s t u refl)
      *-associative

    +ₗ-comm : ∀ x y → x +ₗ y ≡ y +ₗ x
    +ₗ-comm = elim! λ x s _ y t _ → /-ap +-commutes *-commutes

    *ₗ-idl : ∀ x → 1ₗ *ₗ x ≡ x
    *ₗ-idl = elim! λ x s s∈S → quot (inc s s∈S (solve 2
      (λ x s → s :* (1 :* x) :* s ≔ s :* x :* (1 :* s)) x s refl))

    *ₗ-comm : ∀ x y → x *ₗ y ≡ y *ₗ x
    *ₗ-comm = elim! λ x s _ y t _ → /-ap *-commutes *-commutes

    *ₗ-assoc : ∀ x y z → x *ₗ (y *ₗ z) ≡ (x *ₗ y) *ₗ z
    *ₗ-assoc = elim! λ x s _ y t _ z u _ → /-ap *-associative *-associative

    *ₗ-distribl : ∀ x y z → x *ₗ (y +ₗ z) ≡ (x *ₗ y) +ₗ (x *ₗ z)
    *ₗ-distribl = elim! λ x s _ y t _ z u _ →
      let
        prf : 1r * (x * (y * u + z * t)) * (s * t * (s * u))
            ≡ 1r * (x * y * (s * u) + x * z * (s * t)) * (s * (t * u))
        prf = cring! R
      in quot (inc 1r has-1 prf)
```

Finally, these fit together to make a commutative ring.

```agda
  private
    module mr = make-ring
    open make-ring

    mk-loc : make-ring Fr.quotient
    mk-loc .ring-is-set = hlevel 2
    mk-loc .0R  = 0ₗ
    mk-loc ._+_ = _+ₗ_
    mk-loc .-_  = -ₗ_
    mk-loc .1R  = 1ₗ
    mk-loc ._*_ = _*ₗ_
    mk-loc .+-idl = +ₗ-idl
    mk-loc .+-invr = +ₗ-invr
    mk-loc .+-assoc = +ₗ-assoc
    mk-loc .+-comm = +ₗ-comm
    mk-loc .*-idl = *ₗ-idl
    mk-loc .*-idr x = *ₗ-comm x 1ₗ ∙ *ₗ-idl x
    mk-loc .*-assoc = *ₗ-assoc
    mk-loc .*-distribl = *ₗ-distribl
    mk-loc .*-distribr x y z =
      *ₗ-comm (y +ₗ z) x ∙ *ₗ-distribl x y z ∙ ap₂ _+ₗ_ (*ₗ-comm x y) (*ₗ-comm x z)

  S⁻¹R : CRing ℓ
  S⁻¹R .fst = el! Fr.quotient
  S⁻¹R .snd .CRing-on.has-ring-on = to-ring-on mk-loc
  S⁻¹R .snd .CRing-on.*-commutes {x} {y} = *ₗ-comm x y
```
