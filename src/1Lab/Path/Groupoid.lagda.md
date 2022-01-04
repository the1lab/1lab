```agda
open import 1Lab.Equiv
open import 1Lab.Path hiding (_∙_)
open import 1Lab.Type

module 1Lab.Path.Groupoid where
```

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

First, we (re)define the operations using J. These will be closer to the
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
      (happly (JRefl (λ y _ → y ≡ y → x ≡ y) (λ x → x)) _)
      p
```

This isn't as straightforward as it would be in "Book HoTT" because -
remember - J doesn't compute definitionally, only up to the path
`JRefl`{.Agda}.  Now the other identity law:

```agda
  ∙-id-l : (p : y ≡ z) → refl ∙ p ≡ p
  ∙-id-l {y = y} {z = z} p = happly (JRefl (λ y _ → y ≡ z → y ≡ z) (λ x → x)) p
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
      (ap inv (JRefl (λ y _ → y ≡ x) refl) ∙ JRefl (λ y _ → y ≡ x) refl)
```

And we have to prove that composing with an inverse gives the reflexivity path.

```agda
  ∙-inv-l : (p : x ≡ y) → p ∙ inv p ≡ refl
  ∙-inv-l {x = x} = J (λ y p → p ∙ inv p ≡ refl)
                      (∙-id-l (inv refl) ∙ JRefl (λ y _ → y ≡ x) refl)

  ∙-inv-r : (p : x ≡ y) → inv p ∙ p ≡ refl
  ∙-inv-r {x = x} = J (λ y p → inv p ∙ p ≡ refl)
                      (∙-id-r (inv refl) ∙ JRefl (λ y _ → y ≡ x) refl)
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
  ∙-inv-r {x = x} p i j =
    hcomp (λ l → λ { (j = i0) → x
                   ; (j = i1) → p (~ l ∧ ~ i)
                   ; (i = i1) → x
                   })
          (p (j ∧ ~ i)) 
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
`ap-refl`{.Agda} and `ap-sym`{.Agda} in the [1Lab.Path] module.

[1Lab.Path]: 1Lab.Path.html#the-action-on-paths

There, a proof that functions preserve path composition wasn't included,
because it needs `hcomp`{.Agda} to be defined. We fill a cube where the
left face is defined to be `ap f (p ∙ q)` (that's the `(i = i0)` face in
the `hcomp`{.Agda} below), and the remaining structure of the proof
mimics the definition of `_∙_`{.Agda}, so that we indeed get `ap f p ∙
ap f q` as the right face.

<!--
```
  _ = ap-refl
  _ = ap-sym
```
-->

```agda
  ap-comp-path : (f : A → B) {x y z : A} (p : x ≡ y) (q : y ≡ z)
               → ap f (p ∙ q) ≡ ap f p ∙ ap f q
  ap-comp-path f {x} p q i j =
    hcomp (λ k → λ { (i = i0) → f (∙-filler p q k j)
                   ; (j = i0) → f x
                   ; (j = i1) → f (q k)
                   })
          (f (p j))
```

### Convenient helpers

Since a _lot_ of Homotopy Type Theory is dealing with paths, this
section introduces useful helpers for dealing with $n$-ary compositions.
For instance, we know that $p^{-1} ∙ p ∙ q$ is $q$, but this involves
more than a handful of intermediate steps:

```agda
  ∙-cancel-l : {x y z : A} (p : x ≡ y) (q : y ≡ z)
             → (sym p ∙ p ∙ q) ≡ q
  ∙-cancel-l p q =
    sym p ∙ p ∙ q   ≡⟨ ∙-assoc _ _ _ ⟩
    (sym p ∙ p) ∙ q ≡⟨ ap₂ _∙_ (∙-inv-l p) refl ⟩
    refl ∙ q        ≡⟨ ∙-id-l q ⟩
    q               ∎
  
  ∙-cancel'-l : {x y z : A} (p : x ≡ y) (q r : y ≡ z)
              → p ∙ q ≡ p ∙ r → q ≡ r
  ∙-cancel'-l = J (λ y p → (q r : y ≡ _) → p ∙ q ≡ p ∙ r → q ≡ r)
                  (λ q r proof → sym (∙-id-l q) ·· proof ·· ∙-id-l r)

  ∙-cancel'-r : {x y z : A} (p : y ≡ z) (q r : x ≡ y)
              → q ∙ p ≡ r ∙ p → q ≡ r
  ∙-cancel'-r = J (λ y p → (q r : _ ≡ _) → q ∙ p ≡ r ∙ p → q ≡ r)
                  (λ q r proof → sym (∙-id-r q) ·· proof ·· ∙-id-r r)
```

# Groupoid structure of types (cont.)

A useful fact is that if $H$ is a homotopy `f ~ id`, then we can
"invert" it as such:

```agda
open 1Lab.Path

homotopy-invert : ∀ {a} {A : Type a} {f : A → A}
                → (H : (x : A) → f x ≡ x) {x : A}
                → H (f x) ≡ ap f (H x)
homotopy-invert {f = f} H {x = x} =
  sym (
    ap f (H x)                     ≡⟨ sym (∙-id-r _) ⟩
    ap f (H x) ∙ refl              ≡⟨ ap₂ _∙_ refl (sym (∙-inv-r _)) ⟩
    ap f (H x) ∙ H x ∙ sym (H x)   ≡⟨ ∙-assoc _ _ _ ⟩
    (ap f (H x) ∙ H x) ∙ sym (H x) ≡⟨ ap₂ _∙_ (sym (homotopy-natural H _)) refl ⟩
    (H (f x) ∙ H x) ∙ sym (H x)    ≡⟨ sym (∙-assoc _ _ _) ⟩
    H (f x) ∙ H x ∙ sym (H x)      ≡⟨ ap₂ _∙_ refl (∙-inv-r _) ⟩
    H (f x) ∙ refl                 ≡⟨ ∙-id-r _ ⟩
    H (f x)                        ∎
  )
```
