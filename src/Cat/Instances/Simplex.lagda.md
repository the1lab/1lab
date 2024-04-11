---
description: |
  The simplex category.
---
<!--
```agda
open import Meta.Brackets

open import Data.Dec
open import Data.Fin

open import Order.Instances.Nat

open import Cat.Functor.Concrete
open import Cat.Diagram.Initial
open import Cat.Diagram.Terminal
open import Cat.Gaunt

open import Cat.Prelude

import Data.Nat as Nat
import Data.Fin as Fin

import Cat.Reasoning

import Order.Reasoning

```
-->

```agda
module Cat.Instances.Simplex where
```

<!--
```agda
open Precategory
```
-->

# The simplex category {defines="simplex-category semisimplex-category"}

The simplex category, $\Delta$, is generally introduced as the category
of non-empty finite ordinals and order-preserving maps. Though
conceptually simple, this definition is difficult to work with: in particular,
diagrams over $\Delta$ are extremely hard to form! This is why mathematicians
prefer to work with a particular presentation of $\Delta$ as a free category
generated from 2 classes of maps:
- Face maps $\delta^{n}_{i} : [n] \to [n + 1]$ for $0 \leq i \leq n$, $0 < n$
- Degeneracy maps $\sigma^{n}_{i} : [n + 1] \to [n]$ for $0 \leq i < n$, $0 < n$

Intuitively, the face maps $\delta^{n}_{i}$ are injections that skip the $i$th
element of $[n + 1]$, and degeneracy maps are surjections that take both $i$th and
$i+1$-th element of $[n + 1]$ to $i$.

Unfortunately, we need to quotient these generators to get the correct
category; these equations are known as the **simplicial identities**, and
are quite involved.
- For all $i \leq j$, $\delta^{n + 1}_i \circ \delta^{n}_j = \delta^{n+1}_{j+1} \circ \delta^{n}_{i}$; and
- For all $i \leq j$, $\sigma^{n}_j \circ \sigma^{n+1}_i = \sigma^{n}_i \circ \sigma^{n+1}_{j + 1}$; and
- For all $i \leq j$, $\sigma^{n+1}_{j+1} \circ \delta^{n+2}_i = \delta^{n+1}_i \circ \sigma^{n}_{j}$; and
- For all $i, j$ with $i = j$ or $i = j + 1$, $\sigma{n}_j \circ \delta^{n+1}_i = id$; and
- For all $j < i$, $\sigma^{n+1}_j \circ \delta^{n+2}_{i+1} = \delta^{n+1}_{i} \circ \sigma^{n}_{j}$

These identities are extremely painful to work with, and we would need
to deal with them *every* time we eliminated out of the simplex category.
This is a complete non-starter, so we will need to figure out a better approach.

Typically, the way to avoid dealing with quotients by some set of equations
is to find some sort of normal form. Luckily, the simplex category has a
particularly simple normal form: every map can be expressed uniquely as
$$
\delta_{i_1} \circ \cdots \circ \delta_{i_k} \circ \sigma_{j_1} \circ \cdots \sigma_{j_l}
$$
where $0 \leq i_k < \cdots < i_1$ and $0 \leq j_1 < \cdots < j_l$.

<!--
```agda
private variable
  k l m n o l' m' n' o' : Nat
```
-->

These normal forms are relatively straightforward to encode in Agda:
descending chains of face maps can be defined via an indexed inductive,
where `shift⁺`{.Agda} postcomposes the nth face map, and `keep⁺`{.Agda} keeps
the value of 'n' fixed. We call these maps **semisimplicial**, and the
resulting category will be denoted $\Delta^{+}$

```agda
data Δ-Hom⁺ : Nat → Nat → Type where
  done⁺ : Δ-Hom⁺ 0 0
  shift⁺ : ∀ {m n} → Δ-Hom⁺ m n → Δ-Hom⁺ m (suc n)
  keep⁺ : ∀ {m n} → Δ-Hom⁺ m n → Δ-Hom⁺ (suc m) (suc n)
```

Descending chains of degeneracies are defined in a similar fashion, where
where `crush⁻`{.Agda} precomposes the nth degeneracy map. We will call
these maps **demisimplicial**, and the category they form will be denoted
$\Delta^{-}.$

```agda
data Δ-Hom⁻ : Nat → Nat → Type where
  done⁻ : Δ-Hom⁻ 0 0
  crush⁻ : ∀ {m n} → Δ-Hom⁻ (suc m) n → Δ-Hom⁻ (suc (suc m)) n
  keep⁻ : ∀ {m n} → Δ-Hom⁻ m n → Δ-Hom⁻ (suc m) (suc n)
```

Morphisms in $\Delta$ consist of a pair of composable semi and demisimplicial
maps. Note that we allow both `m` and `n` to be 0; this allows us to share
code between the simplex and augmented simplex category.

```agda
record Δ-Hom (m n : Nat) : Type where
  no-eta-equality
  constructor Δ-factor
  field
    {im} : Nat
    hom⁺ : Δ-Hom⁺ im n
    hom⁻ : Δ-Hom⁻ m im

open Δ-Hom
```

<!--
```agda
done : Δ-Hom 0 0
done .im = 0
done .hom⁺ = done⁺
done .hom⁻ = done⁻

crush : Δ-Hom (suc m) n → Δ-Hom (suc (suc m)) n
crush f .im = f .im
crush f .hom⁺ = f .hom⁺
crush f .hom⁻ = crush⁻ (f .hom⁻)

shift : Δ-Hom m n → Δ-Hom m (suc n)
shift f .im = f .im
shift f .hom⁺ = shift⁺ (f .hom⁺)
shift f .hom⁻ = f .hom⁻
```
-->

<!--
```agda
Δ-Hom-pathp
  : {f : Δ-Hom m n} {g : Δ-Hom m' n'}
  → (p : m ≡ m') (q : f .im ≡ g .im) (r : n ≡ n')
  → PathP (λ i → Δ-Hom⁺ (q i) (r i)) (f .hom⁺) (g .hom⁺)
  → PathP (λ i → Δ-Hom⁻ (p i) (q i)) (f .hom⁻) (g .hom⁻)
  → PathP (λ i → Δ-Hom (p i) (r i)) f g
Δ-Hom-pathp p q r s t i .im = q i
Δ-Hom-pathp p q r s t i .hom⁺ = s i
Δ-Hom-pathp p q r s t i .hom⁻ = t i

Δ-Hom-path
  : {f g : Δ-Hom m n}
  → (p : f .im ≡ g .im)
  → PathP (λ i → Δ-Hom⁺ (p i) n) (f .hom⁺) (g .hom⁺)
  → PathP (λ i → Δ-Hom⁻ m (p i)) (f .hom⁻) (g .hom⁻)
  → f ≡ g
Δ-Hom-path p q r = Δ-Hom-pathp refl p refl q r

Δ-Hom-η
  : {f g : Δ-Hom m n}
  → Δ-factor (f .hom⁺) (f .hom⁻) ≡ Δ-factor (g .hom⁺) (g .hom⁻)
  → f ≡ g
Δ-Hom-η p i .im = p i .im
Δ-Hom-η p i .hom⁺ = p i .hom⁺
Δ-Hom-η p i .hom⁻ = p i .hom⁻
```
-->

## Identities and composites

Identity morphisms $[n] \to [n]$ in $\Delta^{+}$ and $\Delta^{-}$ are defined
via induction on $n$, and do not contain any face or degeneracy maps.

```agda
id⁺ : ∀ {n} → Δ-Hom⁺ n n
id⁺ {zero} = done⁺
id⁺ {suc n} = keep⁺ id⁺

id⁻ : ∀ {n} → Δ-Hom⁻ n n
id⁻ {zero} = done⁻
id⁻ {suc n} = keep⁻ id⁻
```

Identity morphisms in $\Delta$ factorize as the identities in $\Delta^{+}$
and $\Delta^{-}$.

```agda
idΔ : Δ-Hom n n
idΔ .im = _
idΔ .hom⁺ = id⁺
idΔ .hom⁻ = id⁻
```

Composites of semi and demisimplicial maps can be defined by a pair of
somewhat tricky inductions.

```agda
_∘⁺_ : Δ-Hom⁺ n o → Δ-Hom⁺ m n → Δ-Hom⁺ m o
f ∘⁺ done⁺ = f
shift⁺ f ∘⁺ shift⁺ g = shift⁺ (f ∘⁺ shift⁺ g)
keep⁺ f ∘⁺ shift⁺ g = shift⁺ (f ∘⁺ g)
shift⁺ f ∘⁺ keep⁺ g = shift⁺ (f ∘⁺ keep⁺ g)
keep⁺ f ∘⁺ keep⁺ g = keep⁺ (f ∘⁺ g)

_∘⁻_ : Δ-Hom⁻ n o → Δ-Hom⁻ m n → Δ-Hom⁻ m o
done⁻ ∘⁻ g = g
crush⁻ f ∘⁻ crush⁻ g = crush⁻ (crush⁻ f ∘⁻ g)
crush⁻ f ∘⁻ keep⁻ (crush⁻ g) = crush⁻ (crush⁻ (f ∘⁻ g))
crush⁻ f ∘⁻ keep⁻ (keep⁻ g) = crush⁻ (f ∘⁻ (keep⁻ g))
keep⁻ f ∘⁻ crush⁻ g = crush⁻ (keep⁻ f ∘⁻ g)
keep⁻ f ∘⁻ keep⁻ g = keep⁻ (f ∘⁻ g)
```

Composites of simplicial maps are even more tricky, as we
need to somehow factor a string of maps $f^{+} \circ f^{-} \circ g^{+} \circ g^{-}$
into a pair of a semisimplicial and demisimplicial maps. The crux of
the problem is factoring $f^{-} \circ g^{+}$ as a semisimplicial map
$h^{+}$ and demisimplicial map $h^{-}$; once we do this, we can
pre and post-compose $g^{-}$ and $f^{+}$, resp.

We begin by computing the image of the putative factorization of $f^{-} \circ g^{+}$.

```agda
imΔ : Δ-Hom⁻ n o → Δ-Hom⁺ m n → Nat
imΔ done⁻ done⁺ = 0
imΔ (crush⁻ f) (shift⁺ g) = imΔ f g
imΔ (crush⁻ f) (keep⁺ (shift⁺ g)) = imΔ f (keep⁺ g)
imΔ (crush⁻ f) (keep⁺ (keep⁺ g)) = imΔ f (keep⁺ g)
imΔ (keep⁻ f) (shift⁺ g) = imΔ f g
imΔ (keep⁻ f) (keep⁺ g) = suc (imΔ f g)
```

Next, we can compute both the semi and demisimplicial components of
the factorization via a pair of gnarly inductions.

```agda
_∘Δ⁺_ : (f⁻ : Δ-Hom⁻ n o) → (f⁺ : Δ-Hom⁺ m n) → Δ-Hom⁺ (imΔ f⁻ f⁺) o
_∘Δ⁺_ done⁻ done⁺ = done⁺
_∘Δ⁺_ (crush⁻ f⁺) (shift⁺ f⁻) = f⁺ ∘Δ⁺ f⁻
_∘Δ⁺_ (crush⁻ f⁺) (keep⁺ (shift⁺ f⁻)) = f⁺ ∘Δ⁺ (keep⁺ f⁻)
_∘Δ⁺_ (crush⁻ f⁺) (keep⁺ (keep⁺ f⁻)) = f⁺ ∘Δ⁺ (keep⁺ f⁻)
_∘Δ⁺_ (keep⁻ f⁺) (shift⁺ f⁻) = shift⁺ (f⁺ ∘Δ⁺ f⁻)
_∘Δ⁺_ (keep⁻ f⁺) (keep⁺ f⁻) = keep⁺ (f⁺ ∘Δ⁺ f⁻)

_∘Δ⁻_ : (f⁻ : Δ-Hom⁻ n o) → (f⁺ : Δ-Hom⁺ m n) → Δ-Hom⁻ m (imΔ f⁻ f⁺)
_∘Δ⁻_ done⁻ done⁺ = done⁻
_∘Δ⁻_ (crush⁻ f⁻) (shift⁺ f⁺) = f⁻ ∘Δ⁻ f⁺
_∘Δ⁻_ (crush⁻ f⁻) (keep⁺ (shift⁺ f⁺)) = f⁻ ∘Δ⁻ (keep⁺ f⁺)
_∘Δ⁻_ (crush⁻ f⁻) (keep⁺ (keep⁺ f⁺)) = crush⁻ (f⁻ ∘Δ⁻ (keep⁺ f⁺))
_∘Δ⁻_ (keep⁻ f⁻) (shift⁺ f⁺) = f⁻ ∘Δ⁻ f⁺
_∘Δ⁻_ (keep⁻ f⁻) (keep⁺ f⁺) = keep⁻ (f⁻ ∘Δ⁻ f⁺)
```

With that hard work out of the way, constructing the composite of
simplicial maps just requires us to pre and post-compose with $g^{-}$
and $f^{+}$, resp.

```agda
_∘Δ_ : Δ-Hom n o → Δ-Hom m n → Δ-Hom m o
(f ∘Δ g) .im = imΔ (f .hom⁻) (g .hom⁺)
(f ∘Δ g) .hom⁺ = f .hom⁺ ∘⁺ (f .hom⁻ ∘Δ⁺ g .hom⁺)
(f ∘Δ g) .hom⁻ = (f .hom⁻ ∘Δ⁻ g .hom⁺) ∘⁻ g .hom⁻
```

## As maps between finite sets

At this point, we could prove the associativity/unitality laws for
$\Delta^{+}, \Delta^{-}$, and $\Delta$ by a series of brutal inductions.
Luckily for us, there is a more elegant approach: all of these maps
have interpretations as maps `Fin m → Fin n`, and these interpretations
are both injective and functorial. This allows us to lift equations from functions
back to equations on their syntactic presentations, which gives us associativity
and unitality "for free".

With that plan outlined, we begin by constructing interpretations
of (semi/demi) simplicial maps as functions.

```agda
Δ-hom⁺ : ∀ {m n} → Δ-Hom⁺ m n → Fin m → Fin n
Δ-hom⁺ (shift⁺ f) = fsuc ⊙ Δ-hom⁺ f
Δ-hom⁺ (keep⁺ f) = fkeep (Δ-hom⁺ f)

Δ-hom⁻ : ∀ {m n} → Δ-Hom⁻ m n → Fin m → Fin n
Δ-hom⁻ (crush⁻ f) = Δ-hom⁻ f ⊙ fpred
Δ-hom⁻ (keep⁻ f) = fkeep (Δ-hom⁻ f)

Δ-hom : ∀ {m n} → Δ-Hom m n → Fin m → Fin n
Δ-hom f = Δ-hom⁺ (f .hom⁺) ⊙ Δ-hom⁻ (f .hom⁻)
```

<!--
```agda
{-# DISPLAY Δ-hom⁺ f = ⟦ f ⟧ #-}
{-# DISPLAY Δ-hom⁻ f = ⟦ f ⟧ #-}
{-# DISPLAY Δ-hom  f = ⟦ f ⟧ #-}
```
-->

We will denote each of these interpretations with `⟦ f ⟧ i` to avoid
too much syntactic overhead.

```agda
instance
  Δ-Hom⁺-⟦⟧-notation
    : ∀ {m n} → ⟦⟧-notation (Δ-Hom⁺ m n)
  Δ-Hom⁻-⟦⟧-notation
    : ∀ {m n} → ⟦⟧-notation (Δ-Hom⁻ m n)
  Δ-Hom-⟦⟧-notation
    : ∀ {m n} → ⟦⟧-notation (Δ-Hom m n)
```

<!--
```agda
  Δ-Hom⁺-⟦⟧-notation {m = m} {n = n} .⟦⟧-notation.lvl = lzero
  Δ-Hom⁺-⟦⟧-notation {m = m} {n = n} .⟦⟧-notation.Sem = Fin m → Fin n
  Δ-Hom⁺-⟦⟧-notation {m = m} {n = n} .⟦⟧-notation.⟦_⟧ = Δ-hom⁺

  Δ-Hom⁻-⟦⟧-notation {m = m} {n = n} .⟦⟧-notation.lvl = lzero
  Δ-Hom⁻-⟦⟧-notation {m = m} {n = n} .⟦⟧-notation.Sem = Fin m → Fin n
  Δ-Hom⁻-⟦⟧-notation {m = m} {n = n} .⟦⟧-notation.⟦_⟧ = Δ-hom⁻

  Δ-Hom-⟦⟧-notation {m = m} {n = n} .⟦⟧-notation.lvl = lzero
  Δ-Hom-⟦⟧-notation {m = m} {n = n} .⟦⟧-notation.Sem = Fin m → Fin n
  Δ-Hom-⟦⟧-notation {m = m} {n = n} .⟦⟧-notation.⟦_⟧ = Δ-hom
```
-->

Note that semisimplicial maps always encode inflationary functions.

```agda
Δ-hom⁺-incr
  : ∀ (f⁺ : Δ-Hom⁺ m n)
  → ∀ i → to-nat i Nat.≤ to-nat (⟦ f⁺ ⟧ i)
Δ-hom⁺-incr (shift⁺ f) i = Nat.≤-sucr (Δ-hom⁺-incr f i)
Δ-hom⁺-incr (keep⁺ f) fzero = Nat.0≤x
Δ-hom⁺-incr (keep⁺ f) (fsuc i) = Nat.s≤s (Δ-hom⁺-incr f i)
```

Likewise, demisimplicial maps always encode deflationary functions.

```agda
Δ-hom⁻-decr
  : ∀ (f⁻ : Δ-Hom⁻ m n)
  → ∀ i → to-nat (⟦ f⁻ ⟧ i) Nat.≤ to-nat i
Δ-hom⁻-decr (crush⁻ f) fzero = Δ-hom⁻-decr f fzero
Δ-hom⁻-decr (crush⁻ f) (fsuc i) = Nat.≤-sucr (Δ-hom⁻-decr f i)
Δ-hom⁻-decr (keep⁻ f) fzero = Nat.0≤x
Δ-hom⁻-decr (keep⁻ f) (fsuc i) = Nat.s≤s (Δ-hom⁻-decr f i)
```

A useful corollary of this is that demisimplicial maps always map 0 to 0.

```agda
Δ-hom⁻-zero
  : ∀ {m n} (f⁻ : Δ-Hom⁻ (suc m) (suc n))
  → ⟦ f⁻ ⟧ fzero ≡ fzero
Δ-hom⁻-zero f⁻ = to-nat-inj (Nat.≤-antisym (Δ-hom⁻-decr f⁻ fzero) Nat.0≤x)
```

Moreover, semisimplicial maps always encode injective functions, and
demisimplicial maps encode *split* surjections.

```agda
Δ-hom⁺-to-inj
  : ∀ {m n}
  → (f : Δ-Hom⁺ m n)
  → injective (Δ-hom⁺ f)
Δ-hom⁻-to-split-surj
  : ∀ {m n}
  → (f : Δ-Hom⁻ m n)
  → ∀ (i : Fin n) → fibre (Δ-hom⁻ f) i
```

<details>
<summary>These both follow directly via induction, so we omit the proofs.
</summary>

```agda
Δ-hom⁺-to-inj (shift⁺ f) p =
  Δ-hom⁺-to-inj f (fsuc-inj p)
Δ-hom⁺-to-inj (keep⁺ f) {fzero} {fzero} p =
  refl
Δ-hom⁺-to-inj (keep⁺ f) {fzero} {fsuc y} p =
  absurd (fzero≠fsuc p)
Δ-hom⁺-to-inj (keep⁺ f) {fsuc x} {fzero} p =
  absurd (fsuc≠fzero p)
Δ-hom⁺-to-inj (keep⁺ f) {fsuc x} {fsuc y} p =
  ap fsuc (Δ-hom⁺-to-inj f (fsuc-inj p))

Δ-hom⁻-to-split-surj {m = suc m} f fzero =
  fzero , Δ-hom⁻-zero f
Δ-hom⁻-to-split-surj (crush⁻ f) (fsuc i) =
  Σ-map fsuc (λ p → p) (Δ-hom⁻-to-split-surj f (fsuc i))
Δ-hom⁻-to-split-surj {m = suc m} (keep⁻ f) (fsuc i) =
  Σ-map fsuc (ap fsuc) (Δ-hom⁻-to-split-surj f i)
```
</details>

We also remark that semi and demisimplicial maps always encode monotonic functions.

```agda
Δ-hom⁺-pres-≤
  : ∀ (f⁺ : Δ-Hom⁺ m n)
  → ∀ {i j} → i ≤ j → ⟦ f⁺ ⟧ i ≤ ⟦ f⁺ ⟧ j
Δ-hom⁺-pres-≤ (shift⁺ f) {i} {j} i≤j = Nat.s≤s (Δ-hom⁺-pres-≤ f i≤j)
Δ-hom⁺-pres-≤ (keep⁺ f) {fzero} {j} i≤j = Nat.0≤x
Δ-hom⁺-pres-≤ (keep⁺ f) {fsuc i} {fsuc j} i≤j = Nat.s≤s (Δ-hom⁺-pres-≤ f (Nat.≤-peel i≤j))

Δ-hom⁻-pres-≤
  : ∀ (f⁻ : Δ-Hom⁻ m n)
  → ∀ {i j} → i ≤ j → ⟦ f⁻ ⟧ i ≤ ⟦ f⁻ ⟧ j
Δ-hom⁻-pres-≤ (crush⁻ f) {fzero} {j} i≤j = Nat.≤-trans (Δ-hom⁻-decr f fzero) Nat.0≤x
Δ-hom⁻-pres-≤ (crush⁻ f) {fsuc i} {fsuc j} i≤j = Δ-hom⁻-pres-≤ f (Nat.≤-peel i≤j)
Δ-hom⁻-pres-≤ (keep⁻ f) {fzero} {j} i≤j = Nat.0≤x
Δ-hom⁻-pres-≤ (keep⁻ f) {fsuc i} {fsuc j} i≤j = Nat.s≤s (Δ-hom⁻-pres-≤ f (Nat.≤-peel i≤j))
```

This in turn implies that simplicial maps also encode monotonic functions.

```agda
Δ-hom-pres-≤
  : ∀ (f : Δ-Hom m n)
  → ∀ {i j} → i ≤ j → ⟦ f ⟧ i ≤ ⟦ f ⟧ j
Δ-hom-pres-≤ f i≤j = Δ-hom⁺-pres-≤ (f .hom⁺) (Δ-hom⁻-pres-≤ (f .hom⁻) i≤j)
```

Semisimplicial maps are not just monotonic; they are *strictly* monotonic!

```agda
Δ-hom⁺-pres-<
  : ∀ (f⁺ : Δ-Hom⁺ m n)
  → ∀ {i j} → i < j → ⟦ f⁺ ⟧ i < ⟦ f⁺ ⟧ j
Δ-hom⁺-pres-< (shift⁺ f⁺) {i} {j} i<j =
  Nat.s≤s (Δ-hom⁺-pres-< f⁺ i<j)
Δ-hom⁺-pres-< (keep⁺ f⁺) {fzero} {fsuc j} i<j =
  Nat.s≤s Nat.0≤x
Δ-hom⁺-pres-< (keep⁺ f⁺) {fsuc i} {fsuc j} i<j =
  Nat.s≤s (Δ-hom⁺-pres-< f⁺ (Nat.≤-peel i<j))
```

Likewise, demisimplicial maps reflect the strict order.

```agda
Δ-hom⁻-reflect-<
  : ∀ (f⁻ : Δ-Hom⁻ m n)
  → ∀ {i j} → ⟦ f⁻ ⟧ i < ⟦ f⁻ ⟧ j → i < j
Δ-hom⁻-reflect-< (crush⁻ f⁻) {i} {fzero} fi<fj =
  absurd (Nat.¬sucx≤0 _ (Nat.≤-trans fi<fj (Δ-hom⁻-decr f⁻ fzero)))
Δ-hom⁻-reflect-< (crush⁻ f⁻) {fzero} {fsuc j} fi<fj =
  Nat.s≤s Nat.0≤x
Δ-hom⁻-reflect-< (crush⁻ f⁻) {fsuc i} {fsuc j} fi<fj =
  Nat.s≤s (Δ-hom⁻-reflect-< f⁻ fi<fj)
Δ-hom⁻-reflect-< (keep⁻ f⁻) {fzero} {fsuc j} fi<fj =
  Nat.s≤s Nat.0≤x
Δ-hom⁻-reflect-< (keep⁻ f⁻) {fsuc i} {fsuc j} fi<fj =
  Nat.s≤s (Δ-hom⁻-reflect-< f⁻ (Nat.≤-peel fi<fj))
```

### Injectivity of interpretations

As noted earlier, each map in $\Delta^{+}, \Delta^{-}$ and $\Delta$ resp.
encode a unique function between finite sets. Proving this for $\Delta^{+}$
and $\Delta^{-}$ is tedious, but straightforward. However, $\Delta$ presents
a more difficult challenge, as we *also* need to show that two factorizations
that are semantically equal factor through the same image.

```agda
Δ-hom-im-unique
  : ∀ {m n n' o}
  → (f⁺ : Δ-Hom⁺ n o) (g⁺ : Δ-Hom⁺ n' o) (f⁻ : Δ-Hom⁻ m n) (g⁻ : Δ-Hom⁻ m n')
  → (∀ i → Δ-hom⁺ f⁺ (Δ-hom⁻ f⁻ i) ≡ Δ-hom⁺ g⁺ (Δ-hom⁻ g⁻ i))
  → n ≡ n'
```

<details>
<summary>We can show this with a rather brutal induction.
</summary>

```agda
Δ-hom-im-unique done⁺ done⁺ f⁻ g⁻ p = refl
Δ-hom-im-unique (shift⁺ f⁺) (shift⁺ g⁺) f⁻ g⁻ p =
  Δ-hom-im-unique f⁺ g⁺ f⁻ g⁻ (fsuc-inj ⊙ p)
Δ-hom-im-unique {m = suc m} (shift⁺ f⁺) (keep⁺ g⁺) f⁻ g⁻ p =
  absurd (fsuc≠fzero (p 0 ∙ ap₂ fkeep refl (Δ-hom⁻-zero g⁻)))
Δ-hom-im-unique {m = suc m} (keep⁺ f⁺) (shift⁺ g⁺) f⁻ g⁻ p =
  absurd (fzero≠fsuc (ap₂ fkeep refl (sym (Δ-hom⁻-zero f⁻)) ∙ p 0))
Δ-hom-im-unique (keep⁺ f⁺) (keep⁺ g⁺) (crush⁻ f⁻) (crush⁻ g⁻) p =
  Δ-hom-im-unique (keep⁺ f⁺) (keep⁺ g⁺) f⁻ g⁻ (p ⊙ fsuc)
Δ-hom-im-unique (keep⁺ f⁺) (keep⁺ g⁺) (crush⁻ f⁻) (keep⁻ g⁻) p =
  absurd (fzero≠fsuc (ap₂ fkeep refl (sym (Δ-hom⁻-zero f⁻)) ∙ p 1))
Δ-hom-im-unique (keep⁺ f⁺) (keep⁺ g⁺) (keep⁻ f⁻) (crush⁻ g⁻) p =
  absurd (fsuc≠fzero (p 1 ∙ ap₂ fkeep refl (Δ-hom⁻-zero g⁻)))
Δ-hom-im-unique (keep⁺ f⁺) (keep⁺ g⁺) (keep⁻ f⁻) (keep⁻ g⁻) p =
  ap suc (Δ-hom-im-unique f⁺ g⁺ f⁻ g⁻ (fsuc-inj ⊙ p ⊙ fsuc))
```
</details>

We also need to show that if a pair of factorizations is semantically
equal, then the semi and demisimplicial components are syntactically equal.

```agda
Δ-hom-unique⁺
  : ∀ {m n o}
  → (f⁺ g⁺ : Δ-Hom⁺ n o) (f⁻ g⁻ : Δ-Hom⁻ m n)
  → (∀ (i : Fin m) → ⟦ f⁺ ⟧ (⟦ f⁻ ⟧ i) ≡ ⟦ g⁺ ⟧ (⟦ g⁻ ⟧ i))
  → f⁺ ≡ g⁺
Δ-hom-unique⁻
  : ∀ {m n o}
  → (f⁺ g⁺ : Δ-Hom⁺ n o) (f⁻ g⁻ : Δ-Hom⁻ m n)
  → (∀ (i : Fin m) → ⟦ f⁺ ⟧ (⟦ f⁻ ⟧ i) ≡ ⟦ g⁺ ⟧ (⟦ g⁻ ⟧ i))
  → f⁻ ≡ g⁻
```

<details>
<summary>These follow by some more brutal inductions that we will
shield the innocent reader from.
</summary>

```agda
Δ-hom-unique⁺ done⁺ done⁺ f⁻ g⁻ p =
  refl
Δ-hom-unique⁺ (shift⁺ f⁺) (shift⁺ g⁺) f⁻ g⁻ p =
  ap shift⁺ (Δ-hom-unique⁺ f⁺ g⁺ f⁻ g⁻ (fsuc-inj ⊙ p))
Δ-hom-unique⁺ {m = suc m} (shift⁺ f⁺) (keep⁺ g⁺) f⁻ g⁻ p =
  absurd (fsuc≠fzero (p 0 ∙ ap₂ fkeep refl (Δ-hom⁻-zero g⁻)))
Δ-hom-unique⁺ {m = suc m} (keep⁺ f⁺) (shift⁺ g⁺) f⁻ g⁻ p =
  absurd (fzero≠fsuc (sym (ap₂ fkeep refl (Δ-hom⁻-zero f⁻)) ∙ p 0))
Δ-hom-unique⁺ (keep⁺ f⁺) (keep⁺ g⁺) (crush⁻ f⁻) (crush⁻ g⁻) p =
  Δ-hom-unique⁺ (keep⁺ f⁺) (keep⁺ g⁺) f⁻ g⁻ (p ⊙ fsuc)
Δ-hom-unique⁺ (keep⁺ f⁺) (keep⁺ g⁺) (crush⁻ f⁻) (keep⁻ g⁻) p =
  absurd (fzero≠fsuc (sym (ap₂ fkeep refl (Δ-hom⁻-zero f⁻)) ∙ p 1))
Δ-hom-unique⁺ (keep⁺ f⁺) (keep⁺ g⁺) (keep⁻ f⁻) (crush⁻ g⁻) p =
  absurd (fsuc≠fzero (p 1 ∙ ap₂ fkeep refl (Δ-hom⁻-zero g⁻)))
Δ-hom-unique⁺ (keep⁺ f⁺) (keep⁺ g⁺) (keep⁻ f⁻) (keep⁻ g⁻) p =
  ap keep⁺ (Δ-hom-unique⁺ f⁺ g⁺ f⁻ g⁻ (fsuc-inj ⊙ p ⊙ fsuc))

Δ-hom-unique⁻ f⁺ g⁺ done⁻ done⁻ p =
  refl
Δ-hom-unique⁻ f⁺ g⁺ (crush⁻ f⁻) (crush⁻ g⁻) p =
  ap crush⁻ (Δ-hom-unique⁻ f⁺ g⁺ f⁻ g⁻ (p ⊙ fsuc))
Δ-hom-unique⁻ f⁺ g⁺ (crush⁻ f⁻) (keep⁻ g⁻) p =
  absurd (fzero≠fsuc (Δ-hom⁺-to-inj g⁺ (sym (p 0) ∙ p 1)))
Δ-hom-unique⁻ f⁺ g⁺ (keep⁻ f⁻) (crush⁻ g⁻) p =
  absurd (fzero≠fsuc (Δ-hom⁺-to-inj f⁺ (p 0 ∙ sym (p 1))))
Δ-hom-unique⁻ (shift⁺ f⁺) (shift⁺ g⁺) (keep⁻ f⁻) (keep⁻ g⁻) p =
  Δ-hom-unique⁻ f⁺ g⁺ (keep⁻ f⁻) (keep⁻ g⁻) (fsuc-inj ⊙ p)
Δ-hom-unique⁻ (shift⁺ f⁺) (keep⁺ g⁺) (keep⁻ f⁻) (keep⁻ g⁻) p =
  absurd (fsuc≠fzero (p 0))
Δ-hom-unique⁻ (keep⁺ f⁺) (shift⁺ g⁺) (keep⁻ f⁻) (keep⁻ g⁻) p =
  absurd (fzero≠fsuc (p 0))
Δ-hom-unique⁻ (keep⁺ f⁺) (keep⁺ g⁺) (keep⁻ f⁻) (keep⁻ g⁻) p =
  ap keep⁻ (Δ-hom-unique⁻ f⁺ g⁺ f⁻ g⁻ (fsuc-inj ⊙ p ⊙ fsuc))
```
</details>

<!--
```agda
Δ-hom-uniquep⁺
  : ∀ {m n' n o}
  → {p : n ≡ n'}
  → (f⁺ : Δ-Hom⁺ n o) (g⁺ : Δ-Hom⁺ n' o) (f⁻ : Δ-Hom⁻ m n) (g⁻ : Δ-Hom⁻ m n')
  → (∀ (i : Fin m) → ⟦ f⁺ ⟧ (⟦ f⁻ ⟧ i) ≡ ⟦ g⁺ ⟧ (⟦ g⁻ ⟧ i))
  → PathP (λ i → Δ-Hom⁺ (p i) o) f⁺ g⁺
Δ-hom-uniquep⁺ {m = m} {o = o} {p = p} =
  J' (λ n n' p →
    ∀ (f⁺ : Δ-Hom⁺ n o) (g⁺ : Δ-Hom⁺ n' o) (f⁻ : Δ-Hom⁻ m n) (g⁻ : Δ-Hom⁻ m n')
    → (∀ i → Δ-hom⁺ f⁺ (Δ-hom⁻ f⁻ i) ≡ Δ-hom⁺ g⁺ (Δ-hom⁻ g⁻ i))
    → PathP (λ i → Δ-Hom⁺ (p i) o) f⁺ g⁺)
    (λ _ → Δ-hom-unique⁺)
    p

Δ-hom-uniquep⁻
  : ∀ {m n' n o}
  → {p : n ≡ n'}
  → (f⁺ : Δ-Hom⁺ n o) (g⁺ : Δ-Hom⁺ n' o) (f⁻ : Δ-Hom⁻ m n) (g⁻ : Δ-Hom⁻ m n')
  → (∀ (i : Fin m) → ⟦ f⁺ ⟧ (⟦ f⁻ ⟧ i) ≡ ⟦ g⁺ ⟧ (⟦ g⁻ ⟧ i))
  → PathP (λ i → Δ-Hom⁻ m (p i)) f⁻ g⁻
Δ-hom-uniquep⁻ {m = m} {o = o} {p = p} =
  J' (λ n n' p →
    ∀ (f⁺ : Δ-Hom⁺ n o) (g⁺ : Δ-Hom⁺ n' o) (f⁻ : Δ-Hom⁻ m n) (g⁻ : Δ-Hom⁻ m n')
    → (∀ i → Δ-hom⁺ f⁺ (Δ-hom⁻ f⁻ i) ≡ Δ-hom⁺ g⁺ (Δ-hom⁻ g⁻ i))
    → PathP (λ i → Δ-Hom⁻ m (p i)) f⁻ g⁻)
    (λ _ → Δ-hom-unique⁻)
    p
```
-->

Injectivity of the interpretation of simplicial maps follows
directly from these lemmas.

```agda
Δ-hom-inj
  : ∀ (f g : Δ-Hom m n)
  → (∀ i → ⟦ f ⟧ i ≡ ⟦ g ⟧ i)
  → f ≡ g
Δ-hom-inj {m} {n} f g p =
  Δ-Hom-path (Δ-hom-im-unique (f .hom⁺) (g .hom⁺) (f .hom⁻) (g .hom⁻) p)
    (Δ-hom-uniquep⁺ (f .hom⁺) (g .hom⁺) (f .hom⁻) (g .hom⁻) p)
    (Δ-hom-uniquep⁻ (f .hom⁺) (g .hom⁺) (f .hom⁻) (g .hom⁻) p)
```

Injectivity the interpretaion of semi and demisimplicial maps follow
neatly as corollaries.

```agda
Δ-hom⁺-inj
  : ∀ (f⁺ g⁺ : Δ-Hom⁺ m n)
  → (∀ i → ⟦ f⁺ ⟧ i ≡ ⟦ g⁺ ⟧ i)
  → f⁺ ≡ g⁺
Δ-hom⁺-inj f⁺ g⁺ p = Δ-hom-unique⁺ f⁺ g⁺ id⁻ id⁻ (p ⊙ Δ-hom⁻ id⁻)

Δ-hom⁻-inj
  : ∀ (f⁻ g⁻ : Δ-Hom⁻ m n)
  → (∀ i → ⟦ f⁻ ⟧ i ≡ ⟦ g⁻ ⟧ i)
  → f⁻ ≡ g⁻
Δ-hom⁻-inj f⁻ g⁻ p = Δ-hom-unique⁻ id⁺ id⁺ f⁻ g⁻ (ap (Δ-hom⁺ id⁺) ⊙ p)
```

### Functoriality of interpretations

Finally, we shall prove functoriality of all of our interpretations.

Identities are mercifully simple.

```agda
Δ-hom⁺-id : ∀ (i : Fin m) → ⟦ id⁺ ⟧ i ≡ i
Δ-hom⁺-id fzero = refl
Δ-hom⁺-id (fsuc i) = ap fsuc (Δ-hom⁺-id i)

Δ-hom⁻-id : ∀ (i : Fin m) → ⟦ id⁻ ⟧ i ≡ i
Δ-hom⁻-id fzero = refl
Δ-hom⁻-id (fsuc i) = ap fsuc (Δ-hom⁻-id i)

Δ-hom-id : ∀ (i : Fin m) → ⟦ idΔ ⟧ i ≡ i
Δ-hom-id i = ap ⟦ id⁺ ⟧ (Δ-hom⁻-id i) ∙ Δ-hom⁺-id i
```

Composites of semi and demisimplicial maps are decidedly less easy.

```agda
Δ-hom⁺-∘
  : (f : Δ-Hom⁺ n o) (g : Δ-Hom⁺ m n)
  → ∀ (i : Fin m) → ⟦ f ∘⁺ g ⟧ i ≡ ⟦ f ⟧ (⟦ g ⟧ i)
Δ-hom⁻-∘
  : (f : Δ-Hom⁻ n o) (g : Δ-Hom⁻ m n)
  → ∀ (i : Fin m) → ⟦ f ∘⁻ g ⟧ i ≡ ⟦ f ⟧ (⟦ g ⟧ i)
```

<details>
<summary>The proofs are not particularly difficult; they both
consist of some (rather large) case bashes.
</summary>

```agda
Δ-hom⁺-∘ done⁺ done⁺ i = fabsurd i
Δ-hom⁺-∘ (shift⁺ f) (shift⁺ g) i = ap fsuc (Δ-hom⁺-∘ f (shift⁺ g) i)
Δ-hom⁺-∘ (shift⁺ f) (keep⁺ g) i = ap fsuc (Δ-hom⁺-∘ f (keep⁺ g) i)
Δ-hom⁺-∘ (keep⁺ f) (shift⁺ g) i = ap fsuc (Δ-hom⁺-∘ f g i)
Δ-hom⁺-∘ (keep⁺ f) (keep⁺ g) fzero = refl
Δ-hom⁺-∘ (keep⁺ f) (keep⁺ g) (fsuc i) = ap fsuc (Δ-hom⁺-∘ f g i)

Δ-hom⁻-∘ done⁻ (crush⁻ g) i = sym (Δ-hom⁻-id (Δ-hom⁻ (crush⁻ g) i))
Δ-hom⁻-∘ (crush⁻ f) (crush⁻ g) i = Δ-hom⁻-∘ (crush⁻ f) g (fpred i)
Δ-hom⁻-∘ (crush⁻ f) (keep⁻ (crush⁻ g)) fzero =
  Δ-hom⁻ (f ∘⁻ g) fzero     ≡⟨ Δ-hom⁻-∘ f g fzero ⟩
  Δ-hom⁻ f (Δ-hom⁻ g fzero) ≡⟨ ap (Δ-hom⁻ f) (Δ-hom⁻-zero g) ⟩
  Δ-hom⁻ f fzero ∎
Δ-hom⁻-∘ (crush⁻ f) (keep⁻ (crush⁻ g)) (fsuc i) = Δ-hom⁻-∘ f g (fpred i)
Δ-hom⁻-∘ (crush⁻ f) (keep⁻ (keep⁻ g)) fzero =
  Δ-hom⁻ (f ∘⁻ keep⁻ g) fzero     ≡⟨ Δ-hom⁻-∘ f (keep⁻ g) fzero ⟩
  Δ-hom⁻ f fzero ∎
Δ-hom⁻-∘ (crush⁻ f) (keep⁻ (keep⁻ g)) (fsuc i) = Δ-hom⁻-∘ f (keep⁻ g) i
Δ-hom⁻-∘ (keep⁻ f) (crush⁻ g) i = Δ-hom⁻-∘ (keep⁻ f) g (fpred i)
Δ-hom⁻-∘ (keep⁻ f) (keep⁻ g) fzero = refl
Δ-hom⁻-∘ (keep⁻ f) (keep⁻ g) (fsuc i) = ap fsuc (Δ-hom⁻-∘ f g i)
```
</details>

Composites of simplicial maps are the most difficult of the bunch. The key lemma
is that the interpretation of the of $f^{-} \circ g^{+}$ is functorial, which
follows from yet another painful induction.

```agda
Δ-hom⁺⁻-comm
  : ∀ (f⁻ : Δ-Hom⁻ n o) (f⁺ : Δ-Hom⁺ m n)
  → ∀ (i : Fin m) → ⟦ f⁻ ∘Δ⁺ f⁺ ⟧ (⟦ f⁻ ∘Δ⁻ f⁺ ⟧ i) ≡ ⟦ f⁻ ⟧ (⟦ f⁺ ⟧ i)
```

<details>
<summary>There really is no intuition to be gained from the proof, so we omit it.
</summary>
```agda
Δ-hom⁺⁻-comm done⁻ done⁺ i = fabsurd i
Δ-hom⁺⁻-comm (crush⁻ f⁻) (shift⁺ f⁺) i = Δ-hom⁺⁻-comm f⁻ f⁺ i
Δ-hom⁺⁻-comm (crush⁻ f⁻) (keep⁺ (shift⁺ f⁺)) fzero = Δ-hom⁺⁻-comm f⁻ (keep⁺ f⁺) fzero
Δ-hom⁺⁻-comm (crush⁻ f⁻) (keep⁺ (shift⁺ f⁺)) (fsuc i) = Δ-hom⁺⁻-comm f⁻ (keep⁺ f⁺) (fsuc i)
Δ-hom⁺⁻-comm (crush⁻ f⁻) (keep⁺ (keep⁺ f⁺)) fzero = Δ-hom⁺⁻-comm f⁻ (keep⁺ f⁺) fzero
Δ-hom⁺⁻-comm (crush⁻ f⁻) (keep⁺ (keep⁺ f⁺)) (fsuc fzero) = Δ-hom⁺⁻-comm f⁻ (keep⁺ f⁺) fzero
Δ-hom⁺⁻-comm (crush⁻ f⁻) (keep⁺ (keep⁺ f⁺)) (fsuc (fsuc i)) = Δ-hom⁺⁻-comm f⁻ (keep⁺ f⁺) (fsuc i)
Δ-hom⁺⁻-comm (keep⁻ f⁻) (shift⁺ f⁺) i = ap fsuc (Δ-hom⁺⁻-comm f⁻ f⁺ i)
Δ-hom⁺⁻-comm (keep⁻ f⁻) (keep⁺ f⁺) fzero = refl
Δ-hom⁺⁻-comm (keep⁻ f⁻) (keep⁺ f⁺) (fsuc i) = ap fsuc (Δ-hom⁺⁻-comm f⁻ f⁺ i)
```
</details>

Luckily, that was our last big induction, and we can get our final functoriality
lemma by piecing together previous results!

```agda
Δ-hom-∘
  : (f : Δ-Hom n o) (g : Δ-Hom m n)
  → ∀ (i : Fin m) → ⟦ (f ∘Δ g) ⟧ i ≡ ⟦ f ⟧ (⟦ g ⟧ i)
Δ-hom-∘ f g i =
  ⟦ f .hom⁺ ∘⁺ (f .hom⁻ ∘Δ⁺ g .hom⁺) ⟧ (⟦ (f .hom⁻ ∘Δ⁻ g .hom⁺) ∘⁻ g .hom⁻ ⟧ i)     ≡⟨ Δ-hom⁺-∘ (f .hom⁺) (f .hom⁻ ∘Δ⁺ g .hom⁺) (⟦ (f .hom⁻ ∘Δ⁻ g .hom⁺) ∘⁻ g .hom⁻ ⟧ i) ⟩
  ⟦ f .hom⁺ ⟧ (⟦ f .hom⁻ ∘Δ⁺ g .hom⁺ ⟧ (⟦ (f .hom⁻ ∘Δ⁻ g .hom⁺) ∘⁻ g .hom⁻ ⟧ i))    ≡⟨ ap (⟦ f .hom⁺ ⟧ ⊙ ⟦ f .hom⁻ ∘Δ⁺ g .hom⁺ ⟧) (Δ-hom⁻-∘ (f .hom⁻ ∘Δ⁻ g .hom⁺) (g .hom⁻) i) ⟩
  ⟦ f .hom⁺ ⟧ (⟦ f .hom⁻ ∘Δ⁺ g .hom⁺ ⟧ (⟦ (f .hom⁻ ∘Δ⁻ g .hom⁺) ⟧ (⟦ g .hom⁻ ⟧ i))) ≡⟨ ap ⟦ f .hom⁺ ⟧ ( Δ-hom⁺⁻-comm (f .hom⁻) (g .hom⁺) (⟦ g .hom⁻ ⟧ i)) ⟩
  ⟦ f .hom⁺ ⟧ (⟦ f .hom⁻ ⟧ (⟦ g .hom⁺ ⟧ (⟦ g .hom⁻ ⟧ i))) ∎
```

## Categories

With all that hard work behind us, it is time to enjoy the fruit
of our labor. All of our putative categories
(both augmented and non-augmented) are equipped with injective functorial
interpretations into functions between sets, which means that they are
bona-fide [[concrete categories]].

```agda
Δₐ⁺-concrete : make-concrete Nat Δ-Hom⁺
Δₐ⁻-concrete : make-concrete Nat Δ-Hom⁻
Δₐ-concrete : make-concrete Nat Δ-Hom

Δ⁺-concrete : make-concrete Nat (λ m n → Δ-Hom⁺ (suc m) (suc n))
Δ⁻-concrete : make-concrete Nat (λ m n → Δ-Hom⁻ (suc m) (suc n))
Δ-concrete : make-concrete Nat (λ m n → Δ-Hom (suc m) (suc n))
```

<details>
<summary>We already have all the results we need, so proving that they
are concrete is just an exercise in building records.
</summary>
```agda
Δₐ⁺-concrete .make-concrete.id = id⁺
Δₐ⁺-concrete .make-concrete._∘_ = _∘⁺_
Δₐ⁺-concrete .make-concrete.lvl = lzero
Δₐ⁺-concrete .make-concrete.F₀ = Fin
Δₐ⁺-concrete .make-concrete.F₀-is-set = hlevel!
Δₐ⁺-concrete .make-concrete.F₁ = Δ-hom⁺
Δₐ⁺-concrete .make-concrete.F₁-inj = Δ-hom⁺-inj _ _
Δₐ⁺-concrete .make-concrete.F-id = Δ-hom⁺-id
Δₐ⁺-concrete .make-concrete.F-∘ = Δ-hom⁺-∘

Δₐ⁻-concrete .make-concrete.id = id⁻
Δₐ⁻-concrete .make-concrete._∘_ = _∘⁻_
Δₐ⁻-concrete .make-concrete.lvl = lzero
Δₐ⁻-concrete .make-concrete.F₀ = Fin
Δₐ⁻-concrete .make-concrete.F₀-is-set = hlevel!
Δₐ⁻-concrete .make-concrete.F₁ = Δ-hom⁻
Δₐ⁻-concrete .make-concrete.F₁-inj = Δ-hom⁻-inj _ _
Δₐ⁻-concrete .make-concrete.F-id = Δ-hom⁻-id
Δₐ⁻-concrete .make-concrete.F-∘ = Δ-hom⁻-∘

Δₐ-concrete .make-concrete.id = idΔ
Δₐ-concrete .make-concrete._∘_ = _∘Δ_
Δₐ-concrete .make-concrete.lvl = lzero
Δₐ-concrete .make-concrete.F₀ = Fin
Δₐ-concrete .make-concrete.F₀-is-set = hlevel!
Δₐ-concrete .make-concrete.F₁ = Δ-hom
Δₐ-concrete .make-concrete.F₁-inj = Δ-hom-inj _ _
Δₐ-concrete .make-concrete.F-id = Δ-hom-id
Δₐ-concrete .make-concrete.F-∘ = Δ-hom-∘

Δ⁺-concrete .make-concrete.id = id⁺
Δ⁺-concrete .make-concrete._∘_ = _∘⁺_
Δ⁺-concrete .make-concrete.lvl = lzero
Δ⁺-concrete .make-concrete.F₀ n = Fin (suc n)
Δ⁺-concrete .make-concrete.F₀-is-set = hlevel!
Δ⁺-concrete .make-concrete.F₁ = Δ-hom⁺
Δ⁺-concrete .make-concrete.F₁-inj = Δ-hom⁺-inj _ _
Δ⁺-concrete .make-concrete.F-id = Δ-hom⁺-id
Δ⁺-concrete .make-concrete.F-∘ = Δ-hom⁺-∘

Δ⁻-concrete .make-concrete.id = id⁻
Δ⁻-concrete .make-concrete._∘_ = _∘⁻_
Δ⁻-concrete .make-concrete.lvl = lzero
Δ⁻-concrete .make-concrete.F₀ n = Fin (suc n)
Δ⁻-concrete .make-concrete.F₀-is-set = hlevel!
Δ⁻-concrete .make-concrete.F₁ = Δ-hom⁻
Δ⁻-concrete .make-concrete.F₁-inj = Δ-hom⁻-inj _ _
Δ⁻-concrete .make-concrete.F-id = Δ-hom⁻-id
Δ⁻-concrete .make-concrete.F-∘ = Δ-hom⁻-∘

Δ-concrete .make-concrete.id = idΔ
Δ-concrete .make-concrete._∘_ = _∘Δ_
Δ-concrete .make-concrete.lvl = lzero
Δ-concrete .make-concrete.F₀ n = Fin (suc n)
Δ-concrete .make-concrete.F₀-is-set = hlevel!
Δ-concrete .make-concrete.F₁ = Δ-hom
Δ-concrete .make-concrete.F₁-inj = Δ-hom-inj _ _
Δ-concrete .make-concrete.F-id = Δ-hom-id
Δ-concrete .make-concrete.F-∘ = Δ-hom-∘
```
</details>

A bit of metaprogramming gives a definition of the
(augmented (demi/semi)) simplex category that will result in pretty
goals.

```agda
Δₐ⁺ : Precategory lzero lzero
Δₐ⁻ : Precategory lzero lzero
Δₐ : Precategory lzero lzero

unquoteDef Δₐ⁺ = define-concrete-category Δₐ⁺ Δₐ⁺-concrete
unquoteDef Δₐ⁻ = define-concrete-category Δₐ⁻ Δₐ⁻-concrete
unquoteDef Δₐ = define-concrete-category Δₐ Δₐ-concrete

Δ⁺ : Precategory lzero lzero
Δ⁻ : Precategory lzero lzero
Δ : Precategory lzero lzero

unquoteDef Δ⁺ = define-concrete-category Δ⁺ Δ⁺-concrete
unquoteDef Δ⁻ = define-concrete-category Δ⁻ Δ⁻-concrete
unquoteDef Δ = define-concrete-category Δ Δ-concrete

module Δₐ⁺ = Cat.Reasoning Δₐ⁺
module Δₐ⁻ = Cat.Reasoning Δₐ⁻
module Δₐ = Cat.Reasoning Δₐ

module Δ⁺ = Cat.Reasoning Δ⁺
module Δ⁻ = Cat.Reasoning Δ⁻
module Δ = Cat.Reasoning Δ
```

## Categorical structure

Now that we actually have categories, we can start to construct some
interesting maps. We begin by constructing more familiar versions of
face and degeneracy map that are parameterized by some $i$.

```
δ⁺ : Fin (suc n) → Δ-Hom⁺ n (suc n)
δ⁺ {n = _} fzero = shift⁺ id⁺
δ⁺ {n = suc _} (fsuc i) = keep⁺ (δ⁺ i)

σ⁻ : Fin n → Δ-Hom⁻ (suc n) n
σ⁻ fzero = crush⁻ id⁻
σ⁻ (fsuc i) = keep⁻ (σ⁻ i)
```

We can extend `δ⁺`{.Agda} and `σ⁻`{.Agda} to simplicial maps by
taking the other component to be the corresponding identity map.

```agda
δ : Fin (suc n) → Δ-Hom n (suc n)
δ i .im = _
δ i .hom⁺ = δ⁺ i
δ i .hom⁻ = id⁻

σ : Fin n → Δ-Hom (suc n) n
σ i .im = _
σ i .hom⁺ = id⁺
σ i .hom⁻ = σ⁻ i
```

The semantic interpretations of `δ i`{.Agda} and `σ i`{.Agda} are the
corresponding face and degenearcy maps between finite sets.

```agda
Δ-hom⁺-δ
  : ∀ (i : Fin (suc n))
  → ∀ (x : Fin n) → ⟦ δ⁺ i ⟧ x ≡ skip i x
Δ-hom-δ
  : ∀ (i : Fin (suc n))
  → ∀ (x : Fin n) → ⟦ δ i ⟧ x ≡ skip i x

Δ-hom⁻-σ
  : ∀ (i : Fin n)
  → ∀ (x : Fin (suc n)) → ⟦ σ⁻ i ⟧ x ≡ squish i x
Δ-hom-σ
  : ∀ (i : Fin n)
  → ∀ (x : Fin (suc n)) → ⟦ σ i ⟧ x ≡ squish i x
```

<details>
<summary>The proofs are straighforward, so we omit them.
</summary>

```agda
Δ-hom⁺-δ fzero x = ap fsuc (Δ-hom⁺-id x)
Δ-hom⁺-δ (fsuc i) fzero = refl
Δ-hom⁺-δ (fsuc i) (fsuc x) = ap fsuc (Δ-hom⁺-δ i x)

Δ-hom-δ i x = ap ⟦ δ⁺ i ⟧ (Δ-hom⁻-id x) ∙ Δ-hom⁺-δ i x

Δ-hom⁻-σ fzero fzero = refl
Δ-hom⁻-σ fzero (fsuc x) =
  ap₂ fkeep (funext Δ-hom⁻-id) refl
  ∙ fkeep-id x
Δ-hom⁻-σ (fsuc i) fzero = refl
Δ-hom⁻-σ (fsuc i) (fsuc x) = ap fsuc (Δ-hom⁻-σ i x)

Δ-hom-σ i x = Δ-hom⁺-id (⟦ σ⁻ i ⟧ x) ∙ Δ-hom⁻-σ i x
```
</details>

Next, note that $0$ is an initial object in the augmented (semi) simplex
category.

```agda
¡⁺ : Δ-Hom⁺ 0 n
¡⁺ {n = zero} = done⁺
¡⁺ {n = suc n} = shift⁺ ¡⁺

¡Δ : Δ-Hom 0 n
¡Δ .im = 0
¡Δ .hom⁺ = ¡⁺
¡Δ .hom⁻ = done⁻
```

There are many ways to prove that these maps are unique, but the most
straightforward approach is to use our semantic interpretations: these
yield functions `Fin 0 → Fin n`, which are extremely easy to prove unique.

```agda
¡⁺-unique : (f : Δ-Hom⁺ 0 n) → f ≡ ¡⁺
¡⁺-unique f = Δ-hom⁺-inj f ¡⁺ (λ i → fabsurd i)

¡Δ-unique : (f : Δ-Hom 0 n) → f ≡ ¡Δ
¡Δ-unique f = Δ-hom-inj f ¡Δ (λ i → fabsurd i)
```

<!--
```agda
Δₐ⁺-initial : Initial Δₐ⁺
Δₐ⁺-initial .Initial.bot = 0
Δₐ⁺-initial .Initial.has⊥ _ .centre = ¡⁺
Δₐ⁺-initial .Initial.has⊥ _ .paths f = sym (¡⁺-unique f)

Δₐ-initial : Initial Δₐ
Δₐ-initial .Initial.bot = 0
Δₐ-initial .Initial.has⊥ _ .centre = ¡Δ
Δₐ-initial .Initial.has⊥ _ .paths f = sym (¡Δ-unique f)
```
-->

```agda
-- FIXME: Rename these
¡⁺-strict : ¬ (Δ-Hom⁺ (suc n) 0)
¡⁺-strict ()

!⁻-strict : ¬ (Δ-Hom⁻ 0 (suc n))
!⁻-strict ()
```


Likewise, $1$ is a terminal object in the (demi) simplex category.

```agda
!⁻ : Δ-Hom⁻ (suc n) 1
!⁻ {n = zero} = id⁻
!⁻ {n = suc n} = crush⁻ !⁻

!Δ : Δ-Hom (suc n) 1
!Δ .im = 1
!Δ .hom⁺ = id⁺
!Δ .hom⁻ = !⁻
```

It is also a terminal object in the augmented simplex category, as
we always have a map $0 \to 1$. However, note that it is *not* terminal
in the augmented demi-simplex category, as there is no surjective map
$0 \to 1$!

```agda
!Δₐ : Δ-Hom n 1
!Δₐ {n = zero} = ¡Δ
!Δₐ {n = suc n} = !Δ
```

We can use the same semantic strategy to prove that these maps are
unique.

```agda
!⁻-unique : (f : Δ-Hom⁻ (suc n) 1) → f ≡ !⁻
!⁻-unique f = Δ-hom⁻-inj f !⁻ λ i → Finite-one-is-prop (⟦ f ⟧ i) (⟦ !⁻ ⟧ i)

!Δ-unique : (f : Δ-Hom (suc n) 1) → f ≡ !Δ
!Δ-unique f = Δ-hom-inj f !Δ λ i → Finite-one-is-prop (⟦ f ⟧ i) (⟦ !Δ ⟧ i)

!Δₐ-unique : (f : Δ-Hom n 1) → f ≡ !Δₐ
!Δₐ-unique {n = zero} = ¡Δ-unique
!Δₐ-unique {n = suc n} = !Δ-unique
```

<!--
```agda
Δ⁻-terminal : Terminal Δ⁻
Δ⁻-terminal .Terminal.top = 0
Δ⁻-terminal .Terminal.has⊤ _ .centre = !⁻
Δ⁻-terminal .Terminal.has⊤ _ .paths f = sym (!⁻-unique f)

Δ-terminal : Terminal Δ
Δ-terminal .Terminal.top = 0
Δ-terminal .Terminal.has⊤ _ .centre = !Δ
Δ-terminal .Terminal.has⊤ _ .paths f = sym (!Δ-unique f)

Δₐ-terminal : Terminal Δₐ
Δₐ-terminal .Terminal.top = 1
Δₐ-terminal .Terminal.has⊤ _ .centre = !Δₐ
Δₐ-terminal .Terminal.has⊤ _ .paths f = sym (!Δₐ-unique f)
```
-->

## Isomorphisms

```agda
Δₐ⁺-iso-is-prop : is-prop (m Δₐ⁺.≅ n)
Δₐ⁺-iso-is-prop {m = m} f g = {!!}
  where
    module f = Δₐ⁺._≅_ f
    module g = Δₐ⁺._≅_ g
    open Order.Reasoning Nat-poset

    cool : ∀ (i : Fin m) → ⟦ f.to ⟧ i Fin.≤ ⟦ g.to ⟧ i
    cool i =
      to-nat (⟦ f.to ⟧ i)                         ≤⟨ {!!} ⟩
      to-nat (⟦ f.to ⟧ (⟦ f.from ⟧ (⟦ g.to ⟧ i))) =⟨ ap to-nat {!!} ⟩
      to-nat (⟦ g.to ⟧ i) ≤∎
```


## Dimension

If $f : [m] \to [n]$ is a semisimplicial map, then $m \leq n$. Conversely,
if $f$ is a demisimplicial map then $m \geq n$. The slogan here is that
semisimplicial maps increase dimension, and demisimplicial maps lower it.

```agda
Δ-dim⁺-≤ : ∀ {m n} → (f : Δ-Hom⁺ m n) → m Nat.≤ n
Δ-dim⁺-≤ done⁺ = Nat.0≤x
Δ-dim⁺-≤ (shift⁺ f) = Nat.≤-sucr (Δ-dim⁺-≤ f)
Δ-dim⁺-≤ (keep⁺ f) = Nat.s≤s (Δ-dim⁺-≤ f)

Δ-dim⁻-≤ : ∀ {m n} → (f : Δ-Hom⁻ m n) → n Nat.≤ m
Δ-dim⁻-≤ done⁻ = Nat.0≤x
Δ-dim⁻-≤ (crush⁻ f) = Nat.≤-sucr (Δ-dim⁻-≤ f)
Δ-dim⁻-≤ (keep⁻ f) = Nat.s≤s (Δ-dim⁻-≤ f)
```

Moreover, if a semi/demisimplicial map contains a face/degeneracy,
then we know it must *strictly* increase/decrease the dimension.

```agda
has-face⁺ : ∀ {m n} → Δ-Hom⁺ m n → Type
has-face⁺ done⁺ = ⊥
has-face⁺ (shift⁺ f) = ⊤
has-face⁺ (keep⁺ f) = has-face⁺ f

has-degeneracy⁻ : ∀ {m n} → Δ-Hom⁻ m n → Type
has-degeneracy⁻ done⁻ = ⊥
has-degeneracy⁻ (crush⁻ f) = ⊤
has-degeneracy⁻ (keep⁻ f) = has-degeneracy⁻ f


Δ-dim⁺-< : ∀ {m n} → (f : Δ-Hom⁺ m n) → has-face⁺ f → m Nat.< n
Δ-dim⁺-< (shift⁺ f) p = Nat.s≤s (Δ-dim⁺-≤ f)
Δ-dim⁺-< (keep⁺ f) p = Nat.s≤s (Δ-dim⁺-< f p)

Δ-dim⁻-< : ∀ {m n} → (f : Δ-Hom⁻ m n) → has-degeneracy⁻ f → n Nat.< m
Δ-dim⁻-< (crush⁻ f) p = Nat.s≤s (Δ-dim⁻-≤ f)
Δ-dim⁻-< (keep⁻ f) p = Nat.s≤s (Δ-dim⁻-< f p)
```

```agda
is-id⁺ : ∀ {m n} → Δ-Hom⁺ m n → Type
is-id⁺ done⁺ = ⊤
is-id⁺ (shift⁺ f) = ⊥
is-id⁺ (keep⁺ f) = is-id⁺ f

is-id⁻ : ∀ {m n} → Δ-Hom⁻ m n → Type
is-id⁻ done⁻ = ⊤
is-id⁻ (crush⁻ f) = ⊥
is-id⁻ (keep⁻ f) = is-id⁻ f
```

Note that these dimension raising/lowering properties immediately imply
that the (augmented) demi/semi simplex categories are categories.

```agda
Δₐ⁺-is-category : is-category Δₐ⁺
Δₐ⁺-is-category = set-identity-system (λ _ _ → Δₐ⁺-iso-is-prop) λ f →
  Nat.≤-antisym (Δ-dim⁺-≤ (Δₐ⁺.to f)) (Δ-dim⁺-≤ (Δₐ⁺.from f))

Δₐ⁺-is-gaunt : is-gaunt Δₐ⁺
Δₐ⁺-is-gaunt .is-gaunt.has-category = Δₐ⁺-is-category
Δₐ⁺-is-gaunt .is-gaunt.has-strict = Nat.Nat-is-set
```

## Decidable equality

<!--
```agda
-- Casts that compute on indices + constructors.
-- Makes decidable equality a bit more well behaved.
cast⁺ : ∀ {n' m' m n} → m ≡ m' → n ≡ n' → Δ-Hom⁺ m n → Δ-Hom⁺ m' n'
cast⁻ : ∀ {m' n' m n} → m ≡ m' → n ≡ n' → Δ-Hom⁻ m n → Δ-Hom⁻ m' n'
castΔ : m ≡ m' → n ≡ n' → Δ-Hom m n → Δ-Hom m' n'

cast⁺ {zero}   {zero}   p q f          = done⁺
cast⁺ {zero}   {suc m'} p q f          = absurd (¡⁺-strict (subst₂ Δ-Hom⁺ p q f))
cast⁺ {suc n'} {m'}     p q done⁺      = absurd (Nat.zero≠suc q)
cast⁺ {suc n'} {m'}     p q (shift⁺ f) = shift⁺ (cast⁺ p (Nat.suc-inj q) f)
cast⁺ {suc n'} {zero}   p q (keep⁺ f)  = absurd (Nat.suc≠zero p)
cast⁺ {suc n'} {suc m'} p q (keep⁺ f)  = keep⁺ (cast⁺ (Nat.suc-inj p) (Nat.suc-inj q) f)

cast⁻ {zero}         {zero}   p q f          = done⁻
cast⁻ {zero}         {suc n'} p q f          = absurd (!⁻-strict (subst₂ Δ-Hom⁻ p q f))
cast⁻ {suc m'}       {n'}     p q done⁻      = absurd (Nat.zero≠suc p)
cast⁻ {suc zero}     {n'}     p q (crush⁻ f) = absurd (Nat.suc≠zero (Nat.suc-inj p))
cast⁻ {suc (suc m')} {n'}     p q (crush⁻ f) = crush⁻ (cast⁻ (Nat.suc-inj p) q f)
cast⁻ {suc m'}       {zero}   p q (keep⁻ f)  = absurd (Nat.suc≠zero q)
cast⁻ {suc m'}       {suc n'} p q (keep⁻ f)  = keep⁻ (cast⁻ (Nat.suc-inj p) (Nat.suc-inj q) f)

castΔ p q f .im = f .im
castΔ p q f .hom⁺ = cast⁺ refl q (f .hom⁺)
castΔ p q f .hom⁻ = cast⁻ p refl (f .hom⁻)

cast⁺-refl : ∀ (f : Δ-Hom⁺ m n) → cast⁺ refl refl f ≡ f
cast⁺-refl done⁺ = refl
cast⁺-refl (shift⁺ f) = ap shift⁺ (cast⁺-refl f)
cast⁺-refl (keep⁺ f) = ap keep⁺ (cast⁺-refl f)

cast⁻-refl : ∀ (f : Δ-Hom⁻ m n) → cast⁻ refl refl f ≡ f
cast⁻-refl done⁻ = refl
cast⁻-refl (crush⁻ f) = ap crush⁻ (cast⁻-refl f)
cast⁻-refl (keep⁻ f) = ap keep⁻ (cast⁻-refl f)

castΔ-refl : ∀ (f : Δ-Hom m n) → castΔ refl refl f ≡ f
castΔ-refl f = Δ-Hom-path refl (cast⁺-refl (f .hom⁺)) (cast⁻-refl (f .hom⁻))

cast⁺≃pathp
  : {f : Δ-Hom⁺ m n} {g : Δ-Hom⁺ m' n'}
  → (p : m ≡ m') (q : n ≡ n')
  → (cast⁺ p q f ≡ g) ≃ PathP (λ i → Δ-Hom⁺ (p i) (q i)) f g
cast⁺≃pathp {m = m} {n = n} {f = f} {g = g} p q =
  J₂ mot (λ f g → ∙-pre-equiv (sym (cast⁺-refl f))) p q f g
  where
    mot : ∀ (m' n' : Nat) → m ≡ m' → n ≡ n' → Type _
    mot m' n' p q =
      ∀ (f : Δ-Hom⁺ m n) (g : Δ-Hom⁺ m' n')
      → (cast⁺ p q f ≡ g) ≃ PathP (λ i → Δ-Hom⁺ (p i) (q i)) f g

cast⁻≃pathp
  : {f : Δ-Hom⁻ m n} {g : Δ-Hom⁻ m' n'}
  → (p : m ≡ m') (q : n ≡ n')
  → (cast⁻ p q f ≡ g) ≃ PathP (λ i → Δ-Hom⁻ (p i) (q i)) f g
cast⁻≃pathp {m = m} {n = n} {f = f} {g = g} p q =
  J₂ mot (λ f g → ∙-pre-equiv (sym (cast⁻-refl f))) p q f g
  where
    mot : ∀ (m' n' : Nat) → m ≡ m' → n ≡ n' → Type _
    mot m' n' p q =
      ∀ (f : Δ-Hom⁻ m n) (g : Δ-Hom⁻ m' n')
      → (cast⁻ p q f ≡ g) ≃ PathP (λ i → Δ-Hom⁻ (p i) (q i)) f g

shift⁺-inj
  : ∀ {f g : Δ-Hom⁺ m n}
  → shift⁺ f ≡ shift⁺ g
  → f ≡ g
shift⁺-inj {m} {n} {f} {g} = ap unshift where
  unshift : Δ-Hom⁺ m (suc n) → Δ-Hom⁺ m n
  unshift (shift⁺ h) = h
  unshift (keep⁺ h) = f

keep⁺-inj
  : ∀ {f g : Δ-Hom⁺ m n}
  → keep⁺ f ≡ keep⁺ g
  → f ≡ g
keep⁺-inj {m} {n} {f} {g} = ap unkeep where
  unkeep : Δ-Hom⁺ (suc m) (suc n) → Δ-Hom⁺ m n
  unkeep (keep⁺ h) = h
  unkeep (shift⁺ h) = f

crush⁻-inj
  : ∀ {f g : Δ-Hom⁻ (suc m) n}
  → crush⁻ f ≡ crush⁻ g
  → f ≡ g
crush⁻-inj {m} {n} {f} {g} = ap uncrush where
  uncrush : Δ-Hom⁻ (suc (suc m)) n → Δ-Hom⁻ (suc m) n
  uncrush (crush⁻ h) = h
  uncrush (keep⁻ h) = f

keep⁻-inj
  : ∀ {f g : Δ-Hom⁻ m n}
  → keep⁻ f ≡ keep⁻ g
  → f ≡ g
keep⁻-inj {m} {n} {f} {g} = ap unkeep where
  unkeep : Δ-Hom⁻ (suc m) (suc n) → Δ-Hom⁻ m n
  unkeep (keep⁻ h) = h
  unkeep (crush⁻ h) = f

is-shift⁺ : Δ-Hom⁺ m n → Type
is-shift⁺ done⁺ = ⊥
is-shift⁺ (shift⁺ _) = ⊤
is-shift⁺ (keep⁺ _) = ⊥

is-keep⁺ : Δ-Hom⁺ m n → Type
is-keep⁺ done⁺ = ⊥
is-keep⁺ (shift⁺ _) = ⊥
is-keep⁺ (keep⁺ _) = ⊤

is-crush⁻ : Δ-Hom⁻ m n → Type
is-crush⁻ done⁻ = ⊥
is-crush⁻ (crush⁻ f) = ⊤
is-crush⁻ (keep⁻ f) = ⊥

is-keep⁻ : Δ-Hom⁻ m n → Type
is-keep⁻ done⁻ = ⊥
is-keep⁻ (crush⁻ f) = ⊥
is-keep⁻ (keep⁻ f) = ⊤

shift⁺≠keep⁺
  : ∀ {f : Δ-Hom⁺ (suc m) n} {g : Δ-Hom⁺ m n}
  → ¬ (shift⁺ f ≡ keep⁺ g)
shift⁺≠keep⁺ p = subst is-shift⁺ p tt

keep⁺≠shift⁺
  : ∀ {f : Δ-Hom⁺ m n} {g : Δ-Hom⁺ (suc m) n}
  → ¬ (keep⁺ f ≡ shift⁺ g)
keep⁺≠shift⁺ p = subst is-keep⁺ p tt

crush⁻≠keep⁻
  : ∀ {f : Δ-Hom⁻ (suc m) (suc n)} {g : Δ-Hom⁻ (suc m) n}
  → ¬ (crush⁻ f ≡ keep⁻ g)
crush⁻≠keep⁻ p = subst is-crush⁻ p tt

keep⁻≠crush⁻
  : ∀ {f : Δ-Hom⁻ (suc m) n} {g : Δ-Hom⁻ (suc m) (suc n)}
  → ¬ (keep⁻ f ≡ crush⁻ g)
keep⁻≠crush⁻ p = subst is-keep⁻ p tt
```
-->

All three classes of maps have decidable equality.

```agda
instance
  Discrete-Δ-Hom⁺ : Discrete (Δ-Hom⁺ m n)
  Discrete-Δ-Hom⁻ : Discrete (Δ-Hom⁻ m n)
  Discrete-Δ-Hom  : Discrete (Δ-Hom m n)
```

<details>
<summary>Proving this is pretty tedious though, especially for
general morphisms.
</summary>

```agda
  Discrete-Δ-Hom⁺ {x = done⁺} {y = done⁺} =
    yes refl
  Discrete-Δ-Hom⁺ {x = shift⁺ x} {y = shift⁺ y} =
    Dec-map (ap shift⁺) shift⁺-inj Discrete-Δ-Hom⁺
  Discrete-Δ-Hom⁺ {x = shift⁺ x} {y = keep⁺ y} =
    no shift⁺≠keep⁺
  Discrete-Δ-Hom⁺ {x = keep⁺ x} {y = shift⁺ y} =
    no keep⁺≠shift⁺
  Discrete-Δ-Hom⁺ {x = keep⁺ x} {y = keep⁺ y} =
    Dec-map (ap keep⁺) keep⁺-inj Discrete-Δ-Hom⁺

  Discrete-Δ-Hom⁻ {x = done⁻} {y = done⁻} =
    yes refl
  Discrete-Δ-Hom⁻ {x = crush⁻ x} {y = crush⁻ y} =
    Dec-map (ap crush⁻) crush⁻-inj Discrete-Δ-Hom⁻
  Discrete-Δ-Hom⁻ {x = crush⁻ x} {y = keep⁻ y} =
    no crush⁻≠keep⁻
  Discrete-Δ-Hom⁻ {x = keep⁻ x} {y = crush⁻ y} =
    no keep⁻≠crush⁻
  Discrete-Δ-Hom⁻ {x = keep⁻ x} {y = keep⁻ y} =
    Dec-map (ap keep⁻) keep⁻-inj Discrete-Δ-Hom⁻

  Discrete-Δ-Hom {x = x} {y = y} with x .im ≡? y .im
  ... | yes p with cast⁺ p refl (x .hom⁺) ≡? (y .hom⁺) | cast⁻ refl p (x .hom⁻) ≡? y .hom⁻
  ... | yes q | yes r =
    yes (Δ-Hom-path p (Equiv.to (cast⁺≃pathp p refl) q) (Equiv.to (cast⁻≃pathp refl p) r))
  ... | yes q | no ¬r =
    no λ s → ¬r $
      subst (λ e → cast⁻ refl e (x .hom⁻) ≡ y .hom⁻)
        (Nat.Nat-is-set _ _ _ _)
        (Equiv.from (cast⁻≃pathp refl (ap im s)) $ ap hom⁻ s)
  ... | no ¬q | r =
    no λ s → ¬q $
      subst (λ e → cast⁺ e refl (x .hom⁺) ≡ y .hom⁺)
        (Nat.Nat-is-set _ _ _ _)
        (Equiv.from (cast⁺≃pathp (ap im s) refl) $ ap hom⁺ s)
  Discrete-Δ-Hom {x = x} {y = y} | no ¬p = no (¬p ⊙ ap im)
```
</details>
