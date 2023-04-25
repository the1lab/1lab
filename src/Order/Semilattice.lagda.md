<!--
```agda
open import Algebra.Monoid.Category
open import Algebra.Semigroup
open import Algebra.Monoid

open import Cat.Displayed.Univalence.Thin
open import Cat.Instances.Delooping
open import Cat.Prelude

open import Data.Fin.Base hiding (_≤_)

open import Order.Diagram.Glb
open import Order.Base

import Cat.Reasoning

import Order.Reasoning as Poset
```
-->

```agda
module Order.Semilattice where
```

# Semilattices

A **semilattice**^[Really, either a _meet_ semilattice or a _join_
semilattice, when considered ordered-theoretically] is a [partially
ordered set] where every [finite] family of elements has a meet^[Or a
join, depending]. But semilattices-in-general admit an _algebraic_
presentation, as well as an order-theoretic presentation: a semilattice
is a commutative idempotent monoid.

As a concrete example of a semilattice before we get started, consider
the subsets of a fixed type (like $\bb{N}$), under the operation of
subset intersection. If we don't know about the "subset" relation, can
we derive it just from the behaviour of intersection?

Surprisingly, the answer is yes! $X$ is a subset of $Y$ iff. the
intersection of $X$ and $Y$ is $X$. Check this for yourself: The
intersection of (e.g.) $X = \{ 1, 2, 3 \}$ and $Y = \{ 1, 2, 3, 4, 5 \}$
is just $\{ 1, 2, 3 \}$ again, so $X \sube Y$.

Generalising away from subsets and intersection, we can recover a
partial ordering from any commutative monoid in which all elements are
idempotent. That is precisely the definition of a semilattice:

[partially ordered set]: Order.Base.html
[finite]: Data.Fin.Base.html

```agda
record is-semilattice {ℓ} {A : Type ℓ} (⊤ : A) (_∧_ : A → A → A) : Type ℓ where
  no-eta-equality
  field
    has-is-monoid : is-monoid ⊤ _∧_
    idempotent    : ∀ {x}   → x ∧ x ≡ x
    commutative   : ∀ {x y} → x ∧ y ≡ y ∧ x
  open is-monoid has-is-monoid public

record Semilattice-on {ℓ} (A : Type ℓ) : Type ℓ where
  no-eta-equality
  field
    top : A
    _∩_ : A → A → A
    has-is-semilattice : is-semilattice top _∩_
  open is-semilattice has-is-semilattice public
```

<!--
```agda
  to-monoid : Monoid-on A
  to-monoid = record { has-is-monoid = has-is-monoid }

  ⋂ : ∀ {n} (f : Fin n → A) → A
  ⋂ {zero} f  = top
  ⋂ {suc n} f = f fzero ∩ ⋂ (λ i → f (fsuc i))

private unquoteDecl eqv = declare-record-iso eqv (quote is-semilattice)

is-semilattice-is-prop
  : ∀ {ℓ} {A : Type ℓ} (t : A) (m : A → A → A)
  → is-prop (is-semilattice t m)
is-semilattice-is-prop {A = A} t m x = Iso→is-hlevel 1 eqv (hlevel 1) x
  where instance
    h-l-a : H-Level A 2
    h-l-a = basic-instance 2 (is-semilattice.has-is-set x)

instance
  H-Level-is-semilattice
    : ∀ {ℓ} {A : Type ℓ} {top : A} {meet : A → A → A} {n}
    → H-Level (is-semilattice top meet) (suc n)
  H-Level-is-semilattice = prop-instance (is-semilattice-is-prop _ _)
```
-->

Rather than going through the usual displayed structure dance, here we
exhibit semilattices through an embedding into monoids: when $(A, \top,
\cap)$ is considered as a monoid, the information that it is a
semilattice is a proposition. To be a bit more explicit, $f : A \to B$
is a semilattice homomorphism when $f(\top) = \top$ and $f(x \cap y) =
f(x) \cap f(y)$.

```agda
Semilattice-structure : ∀ ℓ → Thin-structure {ℓ = ℓ} ℓ Semilattice-on
Semilattice-structure ℓ =
  Full-substructure ℓ _ _ SLat↪Mon (Monoid-structure ℓ) where
```

<!--
```agda
  SLat↪Mon : ∀ x → Semilattice-on x ↣ Monoid-on x
  SLat↪Mon x .fst = Semilattice-on.to-monoid
  SLat↪Mon x .snd a (S , p) (T , q) = Σ-pathp {A = Semilattice-on x}
    (λ { i .Semilattice-on.top → (p ∙ sym q) i .Monoid-on.identity
       ; i .Semilattice-on._∩_ → (p ∙ sym q) i .Monoid-on._⋆_
       ; i .Semilattice-on.has-is-semilattice → r i
       })
    (λ { i j .Monoid-on.identity → sq j i .Monoid-on.identity
       ; i j .Monoid-on._⋆_ → sq j i .Monoid-on._⋆_
       ; i j .Monoid-on.has-is-monoid →
         is-prop→squarep (λ i j → hlevel {T = is-monoid (sq j i .Monoid-on.identity) (sq j i .Monoid-on._⋆_)} 1)
           (λ i → r i .is-semilattice.has-is-monoid)
           (λ i → p i .Monoid-on.has-is-monoid)
           (λ i → q i .Monoid-on.has-is-monoid)
           (λ _ → a .Monoid-on.has-is-monoid) i j
        })
    where
      r = is-prop→pathp
        (λ i → is-semilattice-is-prop ((p ∙ sym q) i .Monoid-on.identity) ((p ∙ sym q) i .Monoid-on._⋆_))
        (S .Semilattice-on.has-is-semilattice) (T .Semilattice-on.has-is-semilattice)
      sq : Square p (p ∙ sym q) refl q
      sq i j = hcomp (i ∨ ∂ j) λ where
        k (k = i0) → p j
        k (i = i1) → p (j ∨ k)
        k (j = i0) → p (i ∧ k)
        k (j = i1) → q (i ∨ ~ k)
```
-->

One might wonder about the soundness of this definition if we want to
think of semilattices as order-theoretic objects: is a semilattice
homomorphism in the above sense necessarily monotone? A little
calculation tells us that yes: we can expand $f(x) \le f(y)$ to mean
$f(x) = f(x) \cap f(y)$, which by preservation of meets means $f(x) =
f(x \cap y)$ --- which is certainly the casae if $x = x \cap y$, i.e.,
$x \le y$.

```agda
Semilattices : ∀ ℓ → Precategory (lsuc ℓ) ℓ
Semilattices ℓ = Structured-objects (Semilattice-structure ℓ)

Semilattice : ∀ ℓ → Type (lsuc ℓ)
Semilattice ℓ = Precategory.Ob (Semilattices ℓ)
```

<!--
```agda
record make-semilattice {ℓ} (A : Type ℓ) : Type ℓ where
  no-eta-equality
  field
    has-is-set  : is-set A
    top         : A
    op          : A → A → A
    idl         : ∀ {x} → op top x ≡ x
    associative : ∀ {x y z} → op x (op y z) ≡ op (op x y) z
    commutative : ∀ {x y} → op x y ≡ op y x
    idempotent  : ∀ {x} → op x x ≡ x

module _ where
  open Semilattice-on
  open is-semilattice
  open make-semilattice

  to-semilattice-on : ∀ {ℓ} {A : Type ℓ} → make-semilattice A → Semilattice-on A
  to-semilattice-on s .top = s .top
  to-semilattice-on s ._∩_ = s .op
  to-semilattice-on s .has-is-semilattice .has-is-monoid .has-is-semigroup .has-is-magma =
    record { has-is-set = s .has-is-set }
  to-semilattice-on s .has-is-semilattice .has-is-monoid .has-is-semigroup .associative =
    s .associative
  to-semilattice-on s .has-is-semilattice .has-is-monoid .idl = s .idl
  to-semilattice-on s .has-is-semilattice .has-is-monoid .idr = s .commutative ∙ s .idl
  to-semilattice-on s .has-is-semilattice .idempotent = s .idempotent
  to-semilattice-on s .has-is-semilattice .commutative = s .commutative

  to-semilattice : ∀ {ℓ} {A : Type ℓ} → make-semilattice A → Semilattice ℓ
  ∣ to-semilattice s .fst ∣ = _
  to-semilattice s .fst .is-tr = s .has-is-set
  to-semilattice s .snd = to-semilattice-on s

open Functor
```
-->

## As orders

We've already commented that a semilattice structure gives rise to a
partial order on the underlying set --- and, in some sense, this order
is canonical --- by setting $x \le y$ to mean $x = x \cap y$. To justify
their inclusion in the same namespace as thin categories, though, we
have to make this formal, by exhibiting a functor from semilattices to
posets.

```agda
Meet-semi-lattice : ∀ {ℓ} → Functor (Semilattices ℓ) (Posets ℓ ℓ)
Meet-semi-lattice .F₀ X = X .fst , po where
  open Poset-on
  open is-partial-order
  module X = Semilattice-on (X .snd)
  po : Poset-on _ ⌞ X ⌟
  po ._≤_ x y = x ≡ x X.∩ y
  po .has-is-poset .≤-thin = hlevel 1
  po .has-is-poset .≤-refl = sym X.idempotent
```

Proving that our now-familiar semilattice-induced order _is_ a partial
order reduces to a matter of algebra, which is presented without
comment. Note that we do not need idempotence for transitivity or
antisymmetry: it is only for reflexivity, where $x \le x$ directly
translates to $x = x \land x$.

```agda
  po .has-is-poset .≤-trans {x} {y} {z} x=x∧y y=y∧z =
    x                 ≡⟨ x=x∧y ⟩
    x X.∩ ⌜ y ⌝       ≡⟨ ap! y=y∧z ⟩
    x X.∩ (y X.∩ z)   ≡⟨ X.associative ⟩
    ⌜ x X.∩ y ⌝ X.∩ z ≡˘⟨ ap¡ x=x∧y ⟩
    x X.∩ z           ∎
  po .has-is-poset .≤-antisym {x} {y} x=x∧y y=y∧x =
    x       ≡⟨ x=x∧y ⟩
    x X.∩ y ≡⟨ X.commutative ⟩
    y X.∩ x ≡˘⟨ y=y∧x ⟩
    y       ∎
```

And, formalising our comments about monotonicity from before, any
semilattice homomorphism is a monotone map under the induced ordering.

```agda
Meet-semi-lattice .F₁ f .hom = f .hom
Meet-semi-lattice .F₁ f .preserves x y p = ap (f .hom) p ∙ f .preserves .Monoid-hom.pres-⋆ _ _
Meet-semi-lattice .F-id    = Homomorphism-path λ _ → refl
Meet-semi-lattice .F-∘ f g = Homomorphism-path λ _ → refl
```

## The interface

This section is less about the mathematics per se, and more about how we
formalise it. Semilattices (and lattices more generally) are an
interesting structure, in that they are category-like in two different
ways! In one direction, we have the the category structure by taking
having a single Hom-set, and setting $a \cap b$ to be the _composition_
operation --- the delooping of the $\cap$ monoid. In the other
direction, we have the poset structure, with the ordering induced by
meets.

To effectively formalise mathematics to do with lattices, we need a
convenient interface for _both_ of these "categories". We already have a
fantastic module for working with morphisms in nontrivial categories:
instantiating it with the delooping of the $\cap$ monoid means we get,
for free, a bunch of combinators for handling big meet expressions.

```agda
module Semilattice {ℓ} (A : Semilattice ℓ) where
  po : Poset _ _
  po = Meet-semi-lattice .F₀ A
  open Poset po public

  private module X = Semilattice-on (A .snd) renaming
            ( associative to ∩-assoc
            ; idl         to ∩-idl
            ; idr         to ∩-idr
            ; commutative to ∩-commutative
            ; idempotent  to ∩-idempotent
            )
  open X using ( top ; _∩_ ; ∩-assoc ; ∩-idl ; ∩-idr ; ∩-commutative ; ∩-idempotent ; ⋂ )
    public

  open Cat.Reasoning (B (Semilattice-on.to-monoid (A .snd)))
    hiding ( Ob ; Hom ; id ; _∘_ ; assoc ; idl ; idr ) public
```

As an example of reasoning about the lattice operator, let us prove that
$x \cap y$ is indeed the meet of $x$ and $y$ in the induced ordering.
It's reduced to a bit of algebra:

```agda
  ∩-is-meet : ∀ {x y} → is-meet po x y (x ∩ y)
  ∩-is-meet {x} {y} .is-meet.meet≤l =
    x ∩ y       ≡⟨ pushl (sym ∩-idempotent) ⟩
    x ∩ (x ∩ y) ≡⟨ ∩-commutative ⟩
    (x ∩ y) ∩ x ∎
  ∩-is-meet {x} {y} .is-meet.meet≤r =
    x ∩ y       ≡˘⟨ pullr ∩-idempotent ⟩
    (x ∩ y) ∩ y ∎
  ∩-is-meet {x} {y} .is-meet.greatest lb lb=lb∧x lb=lb∧y =
    lb           ≡⟨ lb=lb∧y ⟩
    lb ∩ y       ≡⟨ pushl lb=lb∧x ⟩
    lb ∩ (x ∩ y) ∎
```

<!--
```agda
  private module Y {x} {y} = is-meet (∩-is-meet {x} {y}) renaming (meet≤l to ∩≤l ; meet≤r to ∩≤r ; greatest to ∩-univ)
  open Y public

  ⋂-is-glb : ∀ {n} (f : Fin n → ⌞ A ⌟) → is-glb po f (⋂ f)
  ⋂-is-glb {zero} f .is-glb.glb≤fam ()
  ⋂-is-glb {zero} f .is-glb.greatest lb′ x = sym ∩-idr
  ⋂-is-glb {suc n} f = go where
    those : is-glb po (λ i → f (fsuc i)) _
    those = ⋂-is-glb _

    go : is-glb po f (f fzero ∩ ⋂ (λ i → f (fsuc i)))
    go .is-glb.glb≤fam fzero = ∩≤l
    go .is-glb.glb≤fam (fsuc i) =
      f fzero ∩ ⋂ (λ i → f (fsuc i))   ≤⟨ ∩≤r ⟩
      ⋂ (λ i → f (fsuc i))             ≤⟨ those .is-glb.glb≤fam i ⟩
      f (fsuc i)                       ≤∎
    go .is-glb.greatest lb′ f≤lb′ =
      ∩-univ lb′ (f≤lb′ fzero) (those .is-glb.greatest lb′ (λ i → f≤lb′ (fsuc i)))

module
  _ {ℓ ℓ′} {A : Type ℓ} {B : Type ℓ′}
    (S : Semilattice-on A) (T : Semilattice-on B)
    (f : A → B)
    (fh : Monoid-hom (Semilattice-on.to-monoid S) (Semilattice-on.to-monoid T) f)
  where
  private
    module S = Semilattice-on S
    module T = Semilattice-on T
    open Monoid-hom

  slat-pres-⋂ : ∀ {n} (d : Fin n → A) → f (S.⋂ d) ≡ T.⋂ (λ i → f (d i))
  slat-pres-⋂ {n = zero} d = fh .pres-id
  slat-pres-⋂ {n = suc n} d =
    f (d fzero S.∩ S.⋂ (λ i → d (fsuc i)))     ≡⟨ fh .pres-⋆ _ _ ⟩
    f (d fzero) T.∩ f (S.⋂ λ i → d (fsuc i))   ≡⟨ ap₂ T._∩_ refl (slat-pres-⋂ λ i → d (fsuc i)) ⟩
    f (d fzero) T.∩ T.⋂ (λ i → f (d (fsuc i))) ∎
```
-->
