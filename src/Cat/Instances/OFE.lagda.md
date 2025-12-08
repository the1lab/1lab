<!--
```agda
open import 1Lab.Reflection hiding (absurd)

open import Cat.Displayed.Univalence.Thin
open import Cat.Prelude

open import Data.Nat.Properties
open import Data.Nat.Order
open import Data.Nat.Base
open import Data.List
```
-->

```agda
module Cat.Instances.OFE where
```

# Ordered families of equivalence relations

An **ordered family of equivalence relations** (OFE, for short) is a set
$X$ equipped with a family of equivalence relations, indexed by natural
numbers $n$ and written $x \within{n} y$, that _approximate_ the
equality on $X$. The family of equivalence relations can be thought of
as equipping $X$ with a notion of _fractional distance_: $x \within{n}
y$ means that $x$ and $y$ are "within distance $2^{-n}$ of each other".
The axioms of an OFE are essentially that

- The maximal distance between two points is $1$, i.e., $x
\within{0} y$ is the total relation;

- Points that are within some distance $d$ of each other are also within
$d'$, for any $d' \le d$;

- Arbitrarily close points are the same.

::: warning
We remark that the term OFE generally stands for ordered family of
_equivalences_, rather than _equivalence relations_; However, this
terminology is mathematically incorrect: there is no meaningful sense in
which an OFE is a family $I \to (A \simeq B)$.

To preserve the connection with the literature, we shall maintain the
acronym "OFE"; Keep in mind that we do it with disapproval.
:::

Another perspective on OFEs, and indeed a large part for the
justification of their study, is in the semantics of programming
languages: in that case, the relation $x \within{n} y$ should be
interpreted as _equivalent for $n$ steps of computation_: a program
running for at most $n$ steps can not tell $\within{n}$-related elements
apart. Our axioms are then that a program running for no steps can not
distinguish anything, so we have $x \within{0} y$ for any $x, y$, and
that our approximations become finer with an increasing number of steps:
with arbitrarily many steps, the only indistinguishable elements must
actually be equal.

```agda
record is-ofe {ℓ ℓ'} {X : Type ℓ} (within : Nat → X → X → Type ℓ') : Type (ℓ ⊔ ℓ') where
  no-eta-equality

  field
    has-is-prop : ∀ n x y → is-prop (within n x y)

    ≈-refl  : ∀ n {x} → within n x x
    ≈-sym   : ∀ n {x y} → within n x y → within n y x
    ≈-trans : ∀ n {x y z} → within n y z → within n x y → within n x z

    bounded : ∀ x y → within 0 x y
    step    : ∀ n x y → within (suc n) x y → within n x y
    limit   : ∀ x y → (∀ n → within n x y) → x ≡ y

  ofe→ids : is-identity-system (λ x y → ∀ n → within n x y) (λ x n → ≈-refl n)
  ofe→ids = set-identity-system
    (λ x y → Π-is-hlevel 1 λ n → has-is-prop n x y)
    (limit _ _)
```

From a HoTT perspective, this definition works extremely smoothly: note
that since we require the approximate equalities $x \within{n} y$ to be
propositions, every subsequent field of the record is _also_ a
proposition, so equality of `is-ofe`{.Agda} is trivial, like we would
expect. Moreover, since "equality at the limit", the relation

$$
R(x, y) = \forall n, x \within{n} y
$$

is a reflexive relation (since each $x \within{n} y$ is reflexive) that
implies equality, the type underlying a OFE is automatically a set; its
identity type is _equivalent_ to equality at the limit.

<!--
```agda
private unquoteDecl eqv = declare-record-iso eqv (quote is-ofe)

opaque instance
  H-Level-is-ofe
    : ∀ {ℓ ℓ'} {X : Type ℓ} {rs : Nat → X → X → Type ℓ'} {n}
    → H-Level (is-ofe rs) (suc n)
  H-Level-is-ofe {X = X} {rs = rs} = prop-instance λ x →
    let
      instance
        hlr : ∀ {n k x y} → H-Level (rs x n y) (suc k)
        hlr = prop-instance (x .is-ofe.has-is-prop _ _ _)

        hs : H-Level X 2
        hs = basic-instance 2 $
          identity-system→hlevel 1 (is-ofe.ofe→ids x) (λ x y → hlevel 1)
    in Iso→is-hlevel 1 eqv (hlevel 1) x

record OFE-on {ℓ} ℓ' (X : Type ℓ) : Type (ℓ ⊔ lsuc ℓ') where
  field
    within     : (n : Nat) (x y : X) → Type ℓ'
    has-is-ofe : is-ofe within
  open is-ofe has-is-ofe public

private
  hlevel-within : ∀ {ℓ ℓ'} {X : Type ℓ} (O : OFE-on ℓ' X) {x y n} → is-prop (O .OFE-on.within n x y)
  hlevel-within O = O .OFE-on.has-is-prop _ _ _

instance
  open hlevel-projection

  hlevel-proj-ofe : hlevel-projection (quote OFE-on.within)
  hlevel-proj-ofe .has-level       = quote hlevel-within
  hlevel-proj-ofe .get-level _     = pure (quoteTerm (suc zero))
  hlevel-proj-ofe .get-argument (_ ∷ _ ∷ _ ∷ o v∷ _) = pure o
  hlevel-proj-ofe .get-argument _ = typeError []

module
  _ {ℓ ℓ₁ ℓ' ℓ₁'} {X : Type ℓ} {Y : Type ℓ₁} (f : X → Y)
    (O : OFE-on ℓ' X) (P : OFE-on ℓ₁' Y)
  where

  private
    module O = OFE-on O
    module P = OFE-on P
```
-->

The correct notion of morphism between OFEs is that of **non-expansive
maps**, once again appealing to the notion of distance for intuition. A
function $f : X \to Y$ is non-expansive if points under $f$ do not get
farther. Apart from the intuitive justification, we note that the
[structure identity principle][sip] essentially forces non-expansivity
to be the definition of morphism of OFEs: the type of OFEs is equivalent
to a $\Sigma$-type that starts

$$
\Sigma (X : \ty) \Sigma (R : X \to \bN \to X \to \ty) \Sigma ...
$$,

where all the components in $...$ are propositional. Its identity type
can be _computed_ to consist of equivalences between the underlying
types that preserve the relations $R$, and since the relations are
propositions, bi-implication suffices: an identification between OFEs is
a non-expansive equivalence of types with non-expansive inverse.

[sip]: 1Lab.Univalence.SIP.html

```agda
  record is-non-expansive : Type (ℓ ⊔ ℓ' ⊔ ℓ₁') where
    no-eta-equality
    field
      pres-≈ : ∀ {x y n} → O.within n x y → P.within n (f x) (f y)
```

<!--
```agda

module _ {ℓa ℓb ℓa' ℓb'} {A : Type ℓa} {B : Type ℓb} (O : OFE-on ℓa' A) (P : OFE-on ℓb' B)
  where

  private
    module O = OFE-on O
    module P = OFE-on P

  record _→ⁿᵉ_ : Type (ℓa ⊔ ℓb ⊔ ℓa' ⊔ ℓb') where
    field
      map    : A → B
      pres-≈ : ∀ n {x y} → O.within n x y → P.within n (map x) (map y)

open _→ⁿᵉ_ public

module _ {ℓa ℓb ℓa' ℓb'} {A : Type ℓa} {B : Type ℓb} {O : OFE-on ℓa' A} {P : OFE-on ℓb' B} where
  private module P = OFE-on P

  Nonexp-ext : ∀ {f g : O →ⁿᵉ P} → (∀ x → f .map x ≡ g .map x) → f ≡ g
  Nonexp-ext α i .map z = α z i
  Nonexp-ext {f = f} {g} α i .pres-≈ n {x} {y} β =
    is-prop→pathp (λ i → P.has-is-prop n (α x i) (α y i)) (f .pres-≈ n β) (g .pres-≈ n β) i

unquoteDecl
  H-Level-is-non-expansive = declare-record-hlevel 1 H-Level-is-non-expansive (quote is-non-expansive)

open is-non-expansive

OFE-structure : ∀ {ℓ ℓ'} → Thin-structure (ℓ ⊔ ℓ') (OFE-on {ℓ} ℓ')
∣ OFE-structure .is-hom f O P ∣ = is-non-expansive f O P
OFE-structure .is-hom f O P .is-tr = hlevel 1
OFE-structure .id-is-hom .pres-≈ w = w
OFE-structure .∘-is-hom f g α β .pres-≈ w = α .pres-≈ (β .pres-≈ w)
OFE-structure .id-hom-unique {s = s} {t = t} α β = q where
  module s = OFE-on s
  module t = OFE-on t

  p : ∀ x y n → (s.within x n y) ≃ (t.within x n y)
  p x y n = prop-ext (s.has-is-prop _ _ _) (t.has-is-prop _ _ _)
    (α .pres-≈) (β .pres-≈)

  q : s ≡ t
  q i .OFE-on.within x n y = ua (p x y n) i
  q i .OFE-on.has-is-ofe = is-prop→pathp
    (λ i → hlevel {T = is-ofe (λ x n y → ua (p x y n) i)} 1)
    s.has-is-ofe t.has-is-ofe i

OFEs : ∀ ℓ ℓ' → Precategory (lsuc (ℓ ⊔ ℓ')) (ℓ ⊔ ℓ')
OFEs ℓ ℓ' = Structured-objects (OFE-structure {ℓ} {ℓ'})
module OFEs {ℓ ℓ'} = Precategory (OFEs ℓ ℓ')

OFE : ∀ ℓ ℓ' → Type (lsuc (ℓ ⊔ ℓ'))
OFE ℓ ℓ' = OFEs.Ob {ℓ} {ℓ'}

open OFE-on hiding (ofe→ids) public
open is-ofe public
open is-non-expansive public
```
-->

## Examples

A canonical class of examples for OFEs is given by strings, or, more
generally, lists: if $X$ is a set, then, for $x, y : \rm{List}(X)$, we
can define the relations $x \within{n} y$ to mean _the length-$n$
prefixes of $x$ and $y$ are equal_. Let's quickly go over the axioms
informally before looking at the formalisation:

- Each relation $\within{n}$ is an equivalence relation, since it is
  defined to be equality;

- At the limit, suppose we have lists $x, y$: we do not yet know that
  their lengths agree, but we _do_ know that taking a "prefix" longer than
  the list gives back the entire list.

  So, writing $l_x$ and $l_y$ for the lengths, we can use our assumption
  that $x$ and $y$ agree at length $l = \max(l_x, l_y)$: the length $l$
  prefixes of both $x$ and $y$ are both the entire lists $x$ and $y$, so
  we have

  $$
  x = \rm{take}(l,x) = \rm{take}(l,y) = y
  $$,

  where the middle step is $x \within{l} y$.

- Finally, since a length $l+1$ prefix is necessarily adding an element
  onto a length $l$ prefix, we satisfy the monotonicity requirement. In
  the formalisation, we use a direct inductive argument for this. We'll
  show that, for all $xs, ys, n$, if $\rm{take}(1 + n, xs) = \rm{take}(1
  + n, ys)$, then $\rm{take}(n, xs) = \rm{take}(n, ys)$.

  On the _one_ interesting case, we assume that $x :: \rm{take}(1 + n,
  xs) = y :: \rm{take}(1 + n, ys)$, which we can split into $x = y$ and
  $\rm{take}(1 + n, xs) = \rm{take}(1 + n, ys)$. The induction
  hypothesis lets us turn this latter equality into $\rm{take}(n,xs) =
  \rm{take}(n,ys)$, which pairs up with $x = y$ to conclude exactly what
  we want.

```agda
Lists : ∀ {ℓ} {X : Type ℓ} → is-set X → OFE-on ℓ (List X)
Lists X-set .within n xs ys = take n xs ≡ take n ys
Lists X-set .has-is-ofe .has-is-prop n xs ys = ListPath.is-set→List-is-set X-set _ _
Lists X-set .has-is-ofe .≈-refl  n     = refl
Lists X-set .has-is-ofe .≈-sym   n p   = sym p
Lists X-set .has-is-ofe .≈-trans n p q = q ∙ p
Lists X-set .has-is-ofe .bounded x y   = refl

Lists X-set .has-is-ofe .limit x y wit = sym rem₁ ∙∙ agree ∙∙ rem₂ where
  enough = max (length x) (length y)
  agree : take enough x ≡ take enough y
  agree = wit enough

  rem₁ : take enough x ≡ x
  rem₁ = take-length-more x enough (max-≤l _ _)
  rem₂ : take enough y ≡ y
  rem₂ = take-length-more y enough (max-≤r _ _)

Lists X-set .has-is-ofe .step n x y p = steps x y n p where
  steps : ∀ {ℓ} {A : Type ℓ} (x y : List A) n
        → take (suc n) x ≡ take (suc n) y → take n x ≡ take n y
  steps (x ∷ xs) (y ∷ ys) (suc n) p =
    ap₂ _∷_ (ap (head x) p) (steps xs ys n (ap tail p))
```

Since the rest of this proof is a simple case bash,^[5 cases are
reflexivity, 2 assume an impossibility.] we've hidden it on the website.
You can choose to display comments on the side bar, or check out this
module on GitHub.

<!--
```agda
  steps []       []       zero    p = refl
  steps []       []       (suc n) p = refl
  steps []       (x ∷ ys) zero    p = refl
  steps (x ∷ xs) (y ∷ ys) zero    p = refl
  steps (x ∷ xs) []       zero    p = refl
  steps []       (x ∷ ys) (suc n) p = absurd (∷≠[] (sym p))
  steps (x ∷ xs) []       (suc n) p = absurd (∷≠[] p)
```
-->

This example generalises incredibly straightforwardly to possibly
infinite sequences in a set: that is, functions $\bN \to X$. Our
definition of $x \within{n} y$ is now that, for all $k \lt n$, $x(k) =
y(k)$. Once again we are using equality to approximate equality, so this
is levelwise an equivalence relation; surprisingly, the other three
properties are _simpler_ to establish for sequences than for lists!

```agda
Sequences : ∀ {ℓ} {X : Type ℓ} → is-set X → OFE-on ℓ (Nat → X)
Sequences _ .within n xs ys = ∀ k (le : k < n) → xs k ≡ ys k
Sequences {X = X} X-set .has-is-ofe .has-is-prop n xs ys = hlevel 1 where instance
  _ : H-Level X 2
  _ = basic-instance 2 X-set
Sequences _ .has-is-ofe .≈-refl  n k le     = refl
Sequences _ .has-is-ofe .≈-sym   n p k le   = sym (p k le)
Sequences _ .has-is-ofe .≈-trans n p q k le = q k le ∙ p k le

Sequences _ .has-is-ofe .bounded xs ys k ()
Sequences _ .has-is-ofe .step n xs ys p k le = p k (≤-sucr le)
Sequences _ .has-is-ofe .limit xs ys wit     = funext λ k → wit (suc k) k ≤-refl
```

# Contractive maps

<!--
```agda
module
  _ {ℓ ℓ₁ ℓ' ℓ₁'} {X : Type ℓ} {Y : Type ℓ₁} (f : X → Y)
    (O : OFE-on ℓ' X) (P : OFE-on ℓ₁' Y)
  where

  private
    module O = OFE-on O
    module P = OFE-on P
```
-->

```agda
  record is-contractive : Type (ℓ ⊔ ℓ' ⊔ ℓ₁') where
    no-eta-equality
    field
      contract : ∀ {x y n} → O.within n x y → P.within (suc n) (f x) (f y)
```

<!--
```agda
unquoteDecl
  H-Level-is-contractive = declare-record-hlevel 1 H-Level-is-contractive (quote is-contractive)

module _ {ℓa ℓb ℓa' ℓb'} {A : Type ℓa} {B : Type ℓb} (O : OFE-on ℓa' A) (P : OFE-on ℓb' B)
  where

  private
    module O = OFE-on O
    module P = OFE-on P

  record _→ᶜᵒⁿ_ : Type (ℓa ⊔ ℓb ⊔ ℓa' ⊔ ℓb') where
    field
      map      : A → B
      contract : ∀ n {x y} → O.within n x y → P.within (suc n) (map x) (map y)

open _→ᶜᵒⁿ_ public
open is-contractive public
```
-->

<!--
```agda
module OFE-Notation {ℓ ℓ'} {X : Type ℓ} ⦃ O : OFE-on ℓ' X ⦄ where
  private module O = OFE-on O
  _≈[_]_ : X → Nat → X → Type ℓ'
  x ≈[ n ] y = O.within n x y

from-ofe-on : ∀ {ℓ ℓ'} {X : Type ℓ} → OFE-on ℓ' X → OFEs.Ob
∣ from-ofe-on {X = X} O .fst ∣ = X
from-ofe-on O .fst .is-tr = identity-system→hlevel 1 (OFE-on.ofe→ids O) λ x y → Π-is-hlevel 1 λ n → OFE-on.has-is-prop O n x y
from-ofe-on O .snd = O
```
-->
