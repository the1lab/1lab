<!--
```
open import 1Lab.Prelude
```
-->

```agda
module Homotopy.Space.Sinfty where
```

# The infinite sphere

The $(n+1)$-sphere can be constructed from the $n$-sphere via suspension.
By writing a recursive HIT, we can define a type which is its own
suspension. It stands to reason that this definition is a good
candidate for being considered the infinitary limit of the process of
iterated suspension and is thus referred to as the $\infty$-sphere.

```agda
data S∞ : Type where
  N S   : S∞
  merid : S∞ → N ≡ S
```

In classical topology, there are several definitions of the $\infty$-sphere.
However, independently of the approach taken, the resulting space is always
contractible. In Homotopy Type Theory, then, the only meaningful statement that
can be made of `S∞`{.Agda} is that it is contractible. We prove this in two
different ways.

## The Book HoTT approach

```agda
open is-contr

private
  pathsS∞' : (x : S∞) → N ≡ x
  pathsS∞' N = refl
  pathsS∞' S = merid N
  pathsS∞' (merid x i) =
```

First we reduce the problem from constructing a dependent path over
`(λ i → N ≡ merid x i)`{.Agda} from `refl`{.Agda} to `merid N`{.Agda}
to the problem of constructing a path in `N ≡ S`{.Agda} from
`transport (λ j → N ≡ merid x j) refl`{.Agda} to `merid N`{.Agda}.

```agda
    to-pathp {A = λ j → N ≡ merid x j}
```

The proof goes as follows: by the characterisation of transport in path
types the LHS is identified with `refl ∙ merid x`{.Agda}. We get rid of
the `refl`{.Agda} and then a a path between `merid x`{.Agda} and `merid
N`{.Agda} can be obtained from applying `merid`{.Agda} to the recursive
call `pathsS∞' x`{.Agda}.

```agda
      (transport (λ j → N ≡ merid x j) refl ≡⟨ subst-path-right refl (merid x) ⟩
      refl ∙ merid x                        ≡⟨ ∙-idl (merid x) ⟩
      merid x                               ≡⟨ ap merid (sym (pathsS∞' x)) ⟩
      merid N                               ∎) i

is-contrS∞' : is-contr S∞
is-contrS∞' .centre = N
is-contrS∞' .paths = pathsS∞'
```

## The cubical approach

The cubical approach essentially accomplishes the same thing as the previous
proof, without using any helper lemmas, by way of drawing a slightly clever
cube. The case of the definition for the higher constructor requires a
square in which two of the sides are `merid N` and `merid x`. We start with
a square in which both of these sides are `merid N` (specifically
`merid N (i ∧ j)`), and then construct a cube in which one of the faces morphs
`merid N ` into `merid x`. This is something that we can easily do since we
have a path `N ≡ x` via the recursive call `pathsS∞ x`.

```agda
private
  pathsS∞ : (x : S∞) → N ≡ x
  pathsS∞ N = refl
  pathsS∞ S = merid N
  pathsS∞ (merid x i) j = hcomp (∂ i ∨ ∂ j) λ where
    k (k = i0) → merid N (i ∧ j)
    k (i = i0) → N
    k (j = i0) → N
    k (i = i1) → merid N j
    k (j = i1) → merid (pathsS∞ x k) i

is-contrS∞ : is-contr S∞
is-contrS∞ .centre = N
is-contrS∞ .paths = pathsS∞
```
