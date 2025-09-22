---
description: |
  Ranges of natural numbers.
---

<!--
```agda
open import 1Lab.Prelude

open import Data.List.Membership
open import Data.Nat.Properties
open import Data.List.NonEmpty
open import Data.List.Base
open import Data.Nat.Order
open import Data.Dec.Base
open import Data.Fin.Base hiding (_≤_; _<_)
open import Data.Nat.Base
open import Data.Sum.Base
```
-->

```agda
module Data.Nat.Range where
```

<!--
```agda
private variable
  x y : Nat
```
-->

# Ranges of natural numbers

This module contains various tools for working with contiguous ranges
of [[natural numbers]]. We are mainly interested in ranges as something
to iterate over when performing other constructions. For example, the
factorial function

$$
n! = \prod_{i=1}^n x
$$

can be expressed as taking the product of all numbers in the range
$[1, n]$.

We will focus our attention on half-open ranges of numbers $[x, y)$.
Ranges of this form have a couple of nice properties:

- If $w$ is a list, then $[0, \mathrm{length}\; w)$ gives us all valid indices into $w$.
  If we used a closed range, then we'd have to subtract 1 from the length of
  $w$ to get the same list.
- If we have two half-open ranges $[x, y)$ and $[y,z)$ with $x \leq y \leq z$,
  then we can directly concatenate them to get the range $[x, z)$.
- All the ranges $[x,y]$, $(x,y)$, and $(x,y]$ can be expressed as a
  half-open range using only successors. In contrast, deriving $[x,y)$
  from any of the other range types requires us to use predecessors,
  which are much more annoying to reason about.

Unfortunately, ranges $[x,y)$ are a bit annoying to construct directly
via structural recursion on $x$ and $y$. The recurrence relation that
defines $[x,y)$ is:

$$
[i,j) =
\begin{cases}
  [] & y \leq x \\
  x \dblcolon [x+1,y)
\end{cases}
$$

Note that $x$ is increasing and $y$ is constant in this recurrence relation,
so Agda's termination checker will reject this definition. Instead, the
termination metric is $y - x$, which decreases by 1 every step.
We could use [[well-founded]] induction to define $[x,y)$, but luckily
there is a simpler solution: we can define an auxiliary function
`count-up`{.Agda} that computes the range $[x,x+n)$, and then define
$[x,y)$ as `count-up x (y - x)`.

```agda
count-up : Nat → Nat → List Nat
count-up x zero = []
count-up x (suc n) = x ∷ count-up (suc x) n

range : Nat → Nat → List Nat
range x y = count-up x (y - x)
```

We can prove that `range`{.Agda} satisfies our recurrence relation
via some elementary results about monus.

```agda
range-≥-empty : ∀ {x y} → .(y ≤ x) → range x y ≡ []
range-≥-empty {x} {y} y≤x =
  count-up x (y - x) ≡⟨ ap (count-up x) (monus-≤-zero y x y≤x) ⟩
  count-up x 0        ≡⟨⟩
  []                  ∎

range-<-∷ : .(x < y) → range x y ≡ x ∷ range (suc x) y
range-<-∷ {x} {suc y} x<y =
  count-up x (suc y - x)        ≡⟨ ap (count-up x) (monus-≤-suc x y (≤-peel x<y)) ⟩
  count-up x (suc (y - x))      ≡⟨⟩
  x ∷ count-up (suc x) (y - x)  ∎
```

## Properties of half-open ranges

The length of $[x,y)$ is $y$ monus $x$.

```agda
length-count-up : ∀ (x n : Nat) → length (count-up x n) ≡ n
length-count-up x zero = refl
length-count-up x (suc n) = ap suc (length-count-up (suc x) n)

length-range : ∀ (x y : Nat) → length (range x y) ≡ y - x
length-range x y = length-count-up x (y - x)
```

The range $[x,x+1)$ is the singleton list $[x]$.

```agda
range-single : ∀ (x : Nat) → range x (suc x) ≡ x ∷ []
range-single x =
  range x (suc x)           ≡⟨ range-<-∷ ≤-refl ⟩
  x ∷ range (suc x) (suc x) ≡⟨ ap (x ∷_) (range-≥-empty ≤-refl) ⟩
  x ∷ []                    ∎
```

If $x \leq y$ and $y \leq z$, then $[x, y) \concat [y, z) = [x, z)$.

First, an auxiliary lemma: if we count `m` numbers up from `x`, and then
count `n` numbers up from `x + m`, then this is the same as counting
`m + n` numbers up from `x`.

```agda
count-up-++ : ∀ (x m n : Nat) → count-up x m ++ count-up (x + m) n ≡ count-up x (m + n)
count-up-++ x zero n =
  count-up ⌜ x + 0 ⌝ n ≡⟨ ap! (+-zeror x) ⟩
  count-up x n         ∎
count-up-++ x (suc m) n =
  x ∷ (count-up (suc x) m ++ count-up ⌜ x + suc m ⌝ n) ≡⟨ ap! (+-sucr x m) ⟩
  x ∷ (count-up (suc x) m ++ count-up (suc x + m) n)   ≡⟨ ap (x ∷_) (count-up-++ (suc x) m n) ⟩
  count-up x (suc m + n)                               ∎
```

Our result on ranges follows immediately from this count-up-index-of after we do
some monus munging.

```agda
range-++ : ∀ {x z : Nat} → (y : Nat) → x ≤ y → y ≤ z → range x y ++ range y z ≡ range x z
range-++ {x = x} {z = z} y x≤y y≤z =
  count-up x (y - x) ++ count-up ⌜ y ⌝  (z - y)        ≡⟨ ap! (sym (monus-+l-inverse x y x≤y)) ⟩
  count-up x (y - x) ++ count-up (x + (y - x)) (z - y) ≡⟨ count-up-++ x (y - x) (z - y) ⟩
  count-up x ⌜ (y - x) + (z - y) ⌝                     ≡⟨ ap! (monus-cancel-outer x y z x≤y y≤z) ⟩
  count-up x (z - x)                                   ∎
```

<!--
```agda
range-∷r : x ≤ y → range x (suc y) ≡ range x y ∷r y
range-∷r {x = x} {y = y} x≤y =
  range x (suc y)                  ≡˘⟨ range-++ y x≤y ≤-ascend ⟩
  range x y ++ ⌜ range y (suc y) ⌝ ≡⟨ ap! (range-single y) ⟩
  range x y ∷r y                   ∎
```
-->

If $[x,y)$ is nonempty, then $x < y$.

```agda
nonempty-range→< : ∀ {x y} → is-nonempty (range x y) → x < y
nonempty-range→< {x = x} {y = y} ne with holds? (x < y)
... | yes x<y = x<y
... | no ¬x<y =
  absurd (is-nonempty→not-empty ne (range-≥-empty (≤-from-not-< x y ¬x<y)))
```

## Membership in half-open ranges

If $i \in [x,y)$, then $x \leq i$.

```agda
count-up-lower
  : ∀ {x n i}
  → i ∈ count-up x n
  → x ≤ i
count-up-lower {n = suc n} (here i=x) = ≤-reflᵢ (symᵢ i=x)
count-up-lower {n = suc n} (there i∈xn) = <-weaken (count-up-lower i∈xn)

range-lower
  : ∀ {x y i : Nat}
  → i ∈ range x y
  → x ≤ i
range-lower x∈ij = count-up-lower x∈ij
```

Likewise, if $i \in [x,y)$, then $i < y$. The argument here is a *bit*
trickier than the previous one due to some annoying monus manipulation.
A short inductive argument shows us that `i ∈ count-up x n` implies
that `i < n + x`. To transfer this to `range x y`, we need to show
that $(y - x) + y = y$, which is only true when $x \leq y$. We can
discharge this side condition by observing that if $i \in [x,y)$,
then $[x,y)$ must be nonempty, and thus $x < y$.

```agda
count-up-upper
  : ∀ {x n i : Nat}
  → i ∈ count-up x n
  → i < n + x
count-up-upper {x = x} {n = suc n} {i = i} (here i=x) =
  s≤s (≤-trans (≤-reflᵢ i=x) (+-≤r n x))
count-up-upper {x = x} {n = suc n} {i = i} (there i∈xy) =
  ≤-trans (count-up-upper i∈xy) (≤-refl' (+-sucr n x))

range-upper
  : ∀ {x y i : Nat}
  → i ∈ range x y
  → i < y
range-upper {x = x} {y = y} {i = i} i∈xy =
  ≤-trans (count-up-upper i∈xy) $ ≤-refl' $ᵢ
    monus-+r-inverse y x $ᵢ
    <-weaken (nonempty-range→< (has-member→nonempty i∈xy))
```

Conversely, if $x \leq i < y$, then $i \in [x, y)$.

```agda
count-up-∈
  : ∀ {x n i}
  → .(x ≤ i) → .(i < n + x)
  → i ∈ count-up x n
count-up-∈ {x = x} {n = zero} {i = i} x≤i i<n+x =
  absurd (<-irrefl refl (≤-trans i<n+x x≤i))
count-up-∈ {x = x} {n = suc n} {i = i} x≤i i<n+x with ≤-strengthen x≤i
... | inl x=i = here (Equiv.from Id≃path (sym x=i))
... | inr x<i = there (count-up-∈ x<i (≤-trans i<n+x (≤-refl' (sym (+-sucr n x)))))

range-∈
  : ∀ {x y i}
  → .(x ≤ i) → .(i < y)
  → i ∈ range x y
range-∈ {x = x} {y = y} {i = i} x≤i i<y =
  count-up-∈ x≤i $ᵢ ≤-trans i<y $ ≤-refl' $ᵢ sym $
    monus-+r-inverse y x (≤-trans x≤i (<-weaken i<y))
```

Next, observe that if $i \in [x,y)$, then the index of $i$
in $[x,y)$ is $i - x$.

```agda
count-up-index-of
  : ∀ {x n i : Nat}
  → (i∈xn : i ∈ count-up x n)
  → index-of i∈xn ≡ i - x
count-up-index-of {x = x} {n = suc n} {i = i} (here i=x) =
  0     ≡˘⟨ monus-≤-zero i x (≤-reflᵢ i=x) ⟩
  i - x ∎
count-up-index-of {x = x} {n = suc n} {i = i} (there i∈xn) =
  suc (index-of i∈xn) ≡⟨ ap suc (count-up-index-of i∈xn) ⟩
  1 + (i - (1 + x))   ≡˘⟨ monus-pres-+l 1 i (1 + x) (count-up-lower i∈xn) ⟩
  (1 + i) - (1 + x)   ≡⟨ monus-cancell 1 i x ⟩
  i - x               ∎

range-index-of
  : ∀ {x y i : Nat}
  → (i∈xn : i ∈ range x y)
  → index-of i∈xn ≡ i - x
range-index-of = count-up-index-of
```

This means that $i \in [x,y)$ is a [[proposition]], as any two possible
indices of $i$ must both be equal to $i - x$.

```agda
range-∈-is-prop
  : ∀ (x y i : Nat)
  → is-prop (i ∈ range x y)
range-∈-is-prop x y i i∈xy i∈xy' =
  Equiv.injective member≃lookup $ Σ-prop-path! $ fin-ap $
    index-of i∈xy  ≡⟨ range-index-of i∈xy ⟩
    i - x          ≡˘⟨ range-index-of i∈xy' ⟩
    index-of i∈xy' ∎
```

This is the last ingredient we need to prove that $i \in [x,y)$
is equivalent to $x \leq i < y$.

```agda
range-∈≃bounded
  : ∀ (x y i : Nat)
  → (i ∈ range x y) ≃ (x ≤ i × i < y)
range-∈≃bounded x y i =
  prop-ext (range-∈-is-prop x y i) (hlevel 1)
    (λ i∈xy → range-lower i∈xy , range-upper i∈xy)
    (λ x≤i<y → range-∈ (x≤i<y .fst) (x≤i<y .snd))
```
