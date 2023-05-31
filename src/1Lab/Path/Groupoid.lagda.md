---
description: |
  We make explicit the higher groupoid structure of type formers, which
  is derived from their Kan operations.
---
<!--
```agda
open import 1Lab.Path hiding (_∙_)
open import 1Lab.Type
```
-->

```agda
module 1Lab.Path.Groupoid where
```

<!--
```agda
_ = Path
_ = hfill
_ = ap-refl
_ = ap-comp-path
_ = ap-sym
```
-->

# Types are Groupoids

The `Path`{.Agda} types equip every `Type`{.Agda} with the structure of
an _$\infty$-groupoid_. The higher structure of a type begins with its
inhabitants (the 0-cells); Then, there are the paths between inhabitants
- these are inhabitants of the type `Path A x y`, which are the 1-cells
in `A`. Then, we can consider the inhabitants of `Path (Path A x y) p
q`, which are _homotopies_ between paths.

This construction iterates forever - and, at every stage, we have that
the $n$-cells in `A` are the 0-cells of some other type (e.g.: The
1-cells of `A` are the 0-cells of `Path A ...`). Furthermore, this
structure is _weak_: The laws, e.g. associativity of composition, only
hold up to a homotopy. These laws satisfy their own laws --- again using
associativity as an example, the associator satisfies the pentagon
identity.

These laws can be proved in two ways: Using path induction, or directly
with a cubical argument. Here, we do both.

## Book-style

This is the approach taken in the HoTT book. We fix a type, and some
variables of that type, and some paths between variables of that type,
so that each definition doesn't start with 12 parameters.

```agda
module WithJ where
  private variable
    ℓ : Level
    A : Type ℓ
    w x y z : A
```

First, we (re)define the operations using `J`{.Agda}. These will be closer to the
structure given in the book.

```agda
  _∙_ : x ≡ y → y ≡ z → x ≡ z
  _∙_ {x = x} {y} {z} = J (λ y _ → y ≡ z → x ≡ z) (λ x → x)
```

First we define path composition. Then, we can prove that the identity
path - `refl`{.Agda} - acts as an identity for path composition.

```agda
  ∙-id-r : (p : x ≡ y) → p ∙ refl ≡ p
  ∙-id-r {x = x} {y = y} p =
    J (λ _ p → p ∙ refl ≡ p)
      (happly (J-refl (λ y _ → y ≡ y → x ≡ y) (λ x → x)) _)
      p
```

This isn't as straightforward as it would be in "Book HoTT" because -
remember - `J`{.Agda} doesn't compute definitionally, only up to the path
`J-refl`{.Agda}.  Now the other identity law:

```agda
  ∙-id-l : (p : y ≡ z) → refl ∙ p ≡ p
  ∙-id-l {y = y} {z = z} p = happly (J-refl (λ y _ → y ≡ z → y ≡ z) (λ x → x)) p
```

This case we get for less since it's essentially the computation rule for `J`{.Agda}.

```agda
  ∙-assoc : (p : w ≡ x) (q : x ≡ y) (r : y ≡ z)
          → p ∙ (q ∙ r) ≡ (p ∙ q) ∙ r
  ∙-assoc {w = w} {x = x} {y = y} {z = z} p q r =
    J (λ x p → (q : x ≡ y) (r : y ≡ z) → p ∙ (q ∙ r) ≡ (p ∙ q) ∙ r) lemma p q r
    where
      lemma : (q : w ≡ y) (r : y ≡ z)
            → (refl ∙ (q ∙ r)) ≡ ((refl ∙ q) ∙ r)
      lemma q r =
        (refl ∙ (q ∙ r)) ≡⟨ ∙-id-l (q ∙ r) ⟩
        q ∙ r            ≡⟨ sym (ap (λ e → e ∙ r) (∙-id-l q)) ⟩
        (refl ∙ q) ∙ r   ∎
```

The associativity rule is trickier to prove, since we do inductive where
the motive is a dependent product. What we're doing can be summarised
using words: By induction, it suffices to assume `p` is refl. Then, what
we want to show is `(refl ∙ (q ∙ r)) ≡ ((refl ∙ q) ∙ r)`. But both of
those compute to `q ∙ r`, so we are done. This computation isn't
automatic - it's expressed by the `lemma`{.Agda}.

This expresses that the paths behave like morphisms in a category. For a
groupoid, we also need inverses and cancellation:

```agda
  inv : x ≡ y → y ≡ x
  inv {x = x} = J (λ y _ → y ≡ x) refl
```

The operation which assigns inverses has to be involutive, which follows
from two computations.

```agda
  inv-inv : (p : x ≡ y) → inv (inv p) ≡ p
  inv-inv {x = x} =
    J (λ y p → inv (inv p) ≡ p)
      (ap inv (J-refl (λ y _ → y ≡ x) refl) ∙ J-refl (λ y _ → y ≡ x) refl)
```

And we have to prove that composing with an inverse gives the reflexivity path.

```agda
  ∙-inv-r : (p : x ≡ y) → p ∙ inv p ≡ refl
  ∙-inv-r {x = x} = J (λ y p → p ∙ inv p ≡ refl)
                      (∙-id-l (inv refl) ∙ J-refl (λ y _ → y ≡ x) refl)

  ∙-inv-l : (p : x ≡ y) → inv p ∙ p ≡ refl
  ∙-inv-l {x = x} = J (λ y p → inv p ∙ p ≡ refl)
                      (∙-id-r (inv refl) ∙ J-refl (λ y _ → y ≡ x) refl)
```

## Cubically

Now we do the same using `hfill`{.Agda} instead of path induction.

```agda
module _ where
  private variable
    ℓ : Level
    A B : Type ℓ
    w x y z : A

  open 1Lab.Path
```

<!--
```agda
  opaque
    unfolding _∙_
    ∙-filler₂ : ∀ {ℓ} {A : Type ℓ} {x y z : A} (q : x ≡ y) (r : y ≡ z)
              → Square q (q ∙ r) r refl
    ∙-filler₂ q r k i = hcomp (k ∨ ∂ i) λ where
      l (l = i0) → q (i ∨ k)
      l (k = i1) → r (l ∧ i)
      l (i = i0) → q k
      l (i = i1) → r l
```
-->

The left and right identity laws follow directly from the two fillers
for the composition operation.

```agda
    ∙-id-r : (p : x ≡ y) → p ∙ refl ≡ p
    ∙-id-r p = sym (∙-filler p refl)

    ∙-id-l : (p : x ≡ y) → refl ∙ p ≡ p
    ∙-id-l p = sym (∙-filler' refl p)
```

For associativity, we use both:

```agda
    ∙-assoc : (p : w ≡ x) (q : x ≡ y) (r : y ≡ z)
            → p ∙ (q ∙ r) ≡ (p ∙ q) ∙ r
    ∙-assoc p q r i = ∙-filler p q i ∙ ∙-filler' q r (~ i)
```

For cancellation, we need to sketch an open cube where the missing
square expresses the equation we're looking for. Thankfully, we only
have to do this once!

```agda
    ∙-inv-r : ∀ {x y : A} (p : x ≡ y) → p ∙ sym p ≡ refl
    ∙-inv-r {x = x} p i j = hcomp (∂ j ∨ i) λ where
      k (k = i0) → p (j ∧ ~ i)
      k (i = i1) → x
      k (j = i0) → x
      k (j = i1) → p (~ k ∧ ~ i)
```

For the other direction, we use the fact that `p` is definitionally
equal to `sym (sym p)`. In that case, we show that `sym p ∙ sym (sym p)
≡ refl` - which computes to the thing we want!

```agda
    ∙-inv-l : (p : x ≡ y) → sym p ∙ p ≡ refl
    ∙-inv-l p = ∙-inv-r (sym p)
```

In addition to the groupoid identities for paths in a type, it has been
established that functions behave like functors: These are the lemmas
`ap-refl`{.Agda}, `ap-comp-path`{.Agda} and `ap-sym`{.Agda} in the
[1Lab.Path] module.

[1Lab.Path]: 1Lab.Path.html#functorial-action

### Convenient helpers

Since a _lot_ of Homotopy Type Theory is dealing with paths, this
section introduces useful helpers for dealing with $n$-ary compositions.
For instance, we know that $p^{-1} ∙ p ∙ q$ is $q$, but this involves
more than a handful of intermediate steps:

```agda
  ∙-cancel-l
    : ∀ {ℓ} {A : Type ℓ} {x y z : A} (p : x ≡ y) (q : y ≡ z)
    → (sym p ∙ p ∙ q) ≡ q
  ∙-cancel-l {y = y} p q i j = hcomp (∂ i ∨ ∂ j) λ where
    k (k = i0) → p (i ∨ ~ j)
    k (i = i0) → ∙-filler (sym p) (p ∙ q) k j
    k (i = i1) → q (j ∧ k)
    k (j = i0) → y
    k (j = i1) → ∙-filler₂ p q i k

  ∙-cancel-r
    : ∀ {ℓ} {A : Type ℓ} {x y z : A} (p : x ≡ y) (q : z ≡ y)
    → ((p ∙ sym q) ∙ q) ≡ p
  ∙-cancel-r {x = x} {y = y} q p = sym $ ∙-unique _ λ i j →
    ∙-filler q (sym p) (~ i) j

  commutes→square
    : {p : w ≡ x} {q : w ≡ y} {s : x ≡ z} {r : y ≡ z}
    → p ∙ s ≡ q ∙ r
    → Square p q s r
  commutes→square {p = p} {q} {s} {r} fill i j =
    hcomp (∂ i ∨ ∂ j) λ where
      k (k = i0) → fill j i
      k (i = i0) → q (k ∧ j)
      k (i = i1) → s (~ k ∨ j)
      k (j = i0) → ∙-filler p s (~ k) i
      k (j = i1) → ∙-filler₂ q r k i

  square→commutes
    : {p : w ≡ x} {q : w ≡ y} {s : x ≡ z} {r : y ≡ z}
    → Square p q s r → p ∙ s ≡ q ∙ r
  square→commutes {p = p} {q} {s} {r} fill i j = hcomp (∂ i ∨ ∂ j) λ where
    k (k = i0) → fill j i
    k (i = i0) → ∙-filler p s k j
    k (i = i1) → ∙-filler₂ q r (~ k) j
    k (j = i0) → q (~ k ∧ i)
    k (j = i1) → s (k ∨ i)

  ∙-cancel'-l : {x y z : A} (p : x ≡ y) (q r : y ≡ z)
              → p ∙ q ≡ p ∙ r → q ≡ r
  ∙-cancel'-l p q r sq = sym (∙-cancel-l p q) ·· ap (sym p ∙_) sq ·· ∙-cancel-l p r

  ∙-cancel'-r : {x y z : A} (p : y ≡ z) (q r : x ≡ y)
              → q ∙ p ≡ r ∙ p → q ≡ r
  ∙-cancel'-r p q r sq =
       sym (∙-cancel-r q (sym p))
    ·· ap (_∙ sym p) sq
    ·· ∙-cancel-r r (sym p)
```

# Groupoid structure of types (cont.)

A useful fact is that if $H$ is a homotopy $f \sim \id$, then it
"commutes with $f$", in the following sense:

<!--
```agda
open 1Lab.Path
```
-->

```agda
homotopy-invert
  : ∀ {a} {A : Type a} {f : A → A}
  → (H : (x : A) → f x ≡ x) {x : A}
  → H (f x) ≡ ap f (H x)
```

The proof proceeds entirely using $H$ itself, together with the De
Morgan algebra structure on the interval.

```agda
homotopy-invert {f = f} H {x} i j = hcomp (∂ i ∨ ∂ j) λ where
  k (k = i0) → H x       (j ∧ i)
  k (j = i0) → H (f x)   (~ k)
  k (j = i1) → H x       (~ k ∧ i)
  k (i = i0) → H (f x)   (~ k ∨ j)
  k (i = i1) → H (H x j) (~ k)
```
