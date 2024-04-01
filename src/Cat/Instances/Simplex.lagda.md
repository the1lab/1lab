---
description: |
  Concrete categories
---
<!--
```agda
open import Meta.Brackets

open import Data.Dec
open import Data.Fin

open import Cat.Functor.Concrete

open import Cat.Prelude

import Data.Nat as Nat
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
element of $[n + 1]$, and degeneracy maps are surjections that take both $i$ and
$i+1$ to $i$.

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
where `shift⁺`{.Agda} introduces the nth face map, and `keep⁺`{.Agda} keeps
the value of 'n' fixed.

```agda
data Δ-Hom⁺ : Nat → Nat → Type where
  done⁺ : Δ-Hom⁺ 0 0
  shift⁺ : ∀ {m n} → Δ-Hom⁺ m n → Δ-Hom⁺ m (suc n)
  keep⁺ : ∀ {m n} → Δ-Hom⁺ m n → Δ-Hom⁺ (suc m) (suc n)
```

Descending chains of degeneracies are defined in a similar fashion, where
where `crush⁻`{.Agda} introduces the nth degeneracy map.

```agda
data Δ-Hom⁻ : Nat → Nat → Type where
  done⁻ : Δ-Hom⁻ 0 0
  crush⁻ : ∀ {m n} → Δ-Hom⁻ m (suc n) → Δ-Hom⁻ (suc m) (suc n)
  keep⁻ : ∀ {m n} → Δ-Hom⁻ m n → Δ-Hom⁻ (suc m) (suc n)
```

Morphisms in $\Delta$ consist of 2 composable chains of face and degeneracy
maps. Note that we allow both `m` and `n` to be 0; this allows us to share
code between the simplex and augmented simplex category.

```agda
record Δ-Hom (m n : Nat) : Type where
  no-eta-equality
  constructor Δ-hom
  field
    {middle} : Nat
    hom⁺ : Δ-Hom⁺ middle n
    hom⁻ : Δ-Hom⁻ m middle

open Δ-Hom
```

<!--
```agda
Δ-Hom-pathp
  : {f : Δ-Hom m n} {g : Δ-Hom m' n'}
  → (p : m ≡ m') (q : f .middle ≡ g .middle) (r : n ≡ n')
  → PathP (λ i → Δ-Hom⁺ (q i) (r i)) (f .hom⁺) (g .hom⁺)
  → PathP (λ i → Δ-Hom⁻ (p i) (q i)) (f .hom⁻) (g .hom⁻)
  → PathP (λ i → Δ-Hom (p i) (r i)) f g
Δ-Hom-pathp p q r s t i .middle = q i
Δ-Hom-pathp p q r s t i .hom⁺ = s i
Δ-Hom-pathp p q r s t i .hom⁻ = t i

Δ-Hom-path
  : {f g : Δ-Hom m n}
  → (p : f .middle ≡ g .middle)
  → PathP (λ i → Δ-Hom⁺ (p i) n) (f .hom⁺) (g .hom⁺)
  → PathP (λ i → Δ-Hom⁻ m (p i)) (f .hom⁻) (g .hom⁻)
  → f ≡ g
Δ-Hom-path p q r = Δ-Hom-pathp refl p refl q r
```
-->

## Face and degeneracy maps

Identity morphisms $[n] \to [n]$ are defined via induction on $n$,
and do not contain any face or degeneracy maps.

```agda
id⁺ : ∀ {n} → Δ-Hom⁺ n n
id⁺ {zero} = done⁺
id⁺ {suc n} = keep⁺ id⁺

id⁻ : ∀ {n} → Δ-Hom⁻ n n
id⁻ {zero} = done⁻
id⁻ {suc n} = keep⁻ id⁻
```

There are also face maps from $0 \to n$ and degeneracies $1 + n \to 1$
for any $n$.

```agda
¡⁺ : Δ-Hom⁺ 0 m
¡⁺ {m = zero} = done⁺
¡⁺ {m = suc m} = shift⁺ ¡⁺

!⁻ : Δ-Hom⁻ (suc m) 1
!⁻ {m = zero} = id⁻
!⁻ {m = suc m} = crush⁻ !⁻
```

We can also define more familiar looking versions of face and degeneracy
map that are parameterized by some $i$.

```
δ⁺ : Fin (suc n) → Δ-Hom⁺ n (suc n)
δ⁺ {n = _} fzero = shift⁺ id⁺
δ⁺ {n = suc _} (fsuc i) = keep⁺ (δ⁺ i)

σ⁻ : Fin n → Δ-Hom⁻ (suc n) n
σ⁻ fzero = crush⁻ id⁻
σ⁻ (fsuc i) = keep⁻ (σ⁻ i)
```

Composites of face and degeneracy maps can be defined by a somewhat
tricky induction: note that both cases are dual to one another.

```agda
_∘⁻_ : Δ-Hom⁻ n o → Δ-Hom⁻ m n → Δ-Hom⁻ m o
done⁻ ∘⁻ g = g
crush⁻ f ∘⁻ crush⁻ g = crush⁻ (crush⁻ f ∘⁻ g)
crush⁻ f ∘⁻ keep⁻ g = crush⁻ (f ∘⁻ g)
keep⁻ f ∘⁻ crush⁻ g = crush⁻ (keep⁻ f ∘⁻ g)
keep⁻ f ∘⁻ keep⁻ g = keep⁻ (f ∘⁻ g)

_∘⁺_ : Δ-Hom⁺ n o → Δ-Hom⁺ m n → Δ-Hom⁺ m o
f ∘⁺ done⁺ = f
shift⁺ f ∘⁺ shift⁺ g = shift⁺ (f ∘⁺ shift⁺ g)
keep⁺ f ∘⁺ shift⁺ g = shift⁺ (f ∘⁺ g)
shift⁺ f ∘⁺ keep⁺ g = shift⁺ (f ∘⁺ keep⁺ g)
keep⁺ f ∘⁺ keep⁺ g = keep⁺ (f ∘⁺ g)
```

### Properties of face and degeneracy maps

If $f : [m] \to [n]$ is a face map, then $m \leq n$. Conversely,
if $f$ is a degeneracy, then $m \geq n$. The slogan here is that
face maps increase dimension, and degeneracies lower it.

```agda
Δ⁺-dim-≤ : ∀ {m n} → (f : Δ-Hom⁺ m n) → m Nat.≤ n
Δ⁺-dim-≤ done⁺ = Nat.0≤x
Δ⁺-dim-≤ (shift⁺ f) = Nat.≤-sucr (Δ⁺-dim-≤ f)
Δ⁺-dim-≤ (keep⁺ f) = Nat.s≤s (Δ⁺-dim-≤ f)

Δ⁻-dim-≤ : ∀ {m n} → (f : Δ-Hom⁻ m n) → n Nat.≤ m
Δ⁻-dim-≤ done⁻ = Nat.0≤x
Δ⁻-dim-≤ (crush⁻ f) = Nat.s≤s (Nat.weaken-< (Δ⁻-dim-≤ f))
Δ⁻-dim-≤ (keep⁻ f) = Nat.s≤s (Δ⁻-dim-≤ f)
```

Moreover, if our face/degeneracy map contains a `shift⁺`/`crush⁻`,
then we know it must *strictly* increase/decrease the dimension.

```
has-shift⁺ : ∀ {m n} → Δ-Hom⁺ m n → Type
has-shift⁺ done⁺ = ⊥
has-shift⁺ (shift⁺ f) = ⊤
has-shift⁺ (keep⁺ f) = has-shift⁺ f

has-crush⁻ : ∀ {m n} → Δ-Hom⁻ m n → Type
has-crush⁻ done⁻ = ⊥
has-crush⁻ (crush⁻ f) = ⊤
has-crush⁻ (keep⁻ f) = has-crush⁻ f

Δ⁺-dim-< : ∀ {m n} → (f : Δ-Hom⁺ m n) → has-shift⁺ f → m Nat.< n
Δ⁺-dim-< (shift⁺ f) p = Nat.s≤s (Δ⁺-dim-≤ f)
Δ⁺-dim-< (keep⁺ f) p = Nat.s≤s (Δ⁺-dim-< f p)

Δ⁻-dim-< : ∀ {m n} → (f : Δ-Hom⁻ m n) → has-crush⁻ f → n Nat.< m
Δ⁻-dim-< (crush⁻ f) p = Nat.s≤s (Δ⁻-dim-≤ f)
Δ⁻-dim-< (keep⁻ f) p = Nat.s≤s (Δ⁻-dim-< f p)
```

### Semantics of face and degeneracy maps

As noted in the introduciton, maps in the simplicial category can also
be represented as maps between `Fin`.

```agda
Δ⁺-map : ∀ {m n} → Δ-Hom⁺ m n → Fin m → Fin n
Δ⁺-map (shift⁺ f) i = fsuc (Δ⁺-map f i)
Δ⁺-map (keep⁺ f) fzero = fzero
Δ⁺-map (keep⁺ f) (fsuc i) = fsuc (Δ⁺-map f i)

Δ⁻-map : ∀ {m n} → Δ-Hom⁻ m n → Fin m → Fin n
Δ⁻-map (crush⁻ f) fzero = fzero
Δ⁻-map (crush⁻ f) (fsuc i) = Δ⁻-map f i
Δ⁻-map (keep⁻ f) fzero = fzero
Δ⁻-map (keep⁻ f) (fsuc i) = fsuc (Δ⁻-map f i)
```

Face maps are always inflationary maps, and degeneracies are always
deflationary.

```agda
Δ⁺-map-incr
  : ∀ {m n} → (f : Δ-Hom⁺ m n)
  → ∀ i → to-nat i Nat.≤ to-nat (Δ⁺-map f i)
Δ⁺-map-incr (shift⁺ f) i = Nat.≤-sucr (Δ⁺-map-incr f i)
Δ⁺-map-incr (keep⁺ f) fzero = Nat.0≤x
Δ⁺-map-incr (keep⁺ f) (fsuc i) = Nat.s≤s (Δ⁺-map-incr f i)

Δ⁻-map-decr
  : ∀ {m n} → (f : Δ-Hom⁻ m n)
  → ∀ i → to-nat (Δ⁻-map f i) Nat.≤ to-nat i
Δ⁻-map-decr (crush⁻ f) fzero = 0≤x
Δ⁻-map-decr (crush⁻ f) (fsuc i) = Nat.≤-sucr (Δ⁻-map-decr f i)
Δ⁻-map-decr (keep⁻ f) fzero = Nat.0≤x
Δ⁻-map-decr (keep⁻ f) (fsuc i) = Nat.s≤s (Δ⁻-map-decr f i)
```

A useful corollary of this is that degeneracies always map 0 to 0.

```agda
Δ⁻-map-zero
  : ∀ {m n} (f : Δ-Hom⁻ (suc m) (suc n))
  → Δ⁻-map f fzero ≡ fzero
Δ⁻-map-zero f = to-nat-inj (Nat.≤-antisym (Δ⁻-map-decr f fzero) Nat.0≤x)
```

Furthermore, the interpretations of face and degeneracy maps are both
injective.

```agda
Δ⁺-map-inj
  : ∀ (f g : Δ-Hom⁺ m n)
  → (∀ i → Δ⁺-map f i ≡ Δ⁺-map g i)
  → f ≡ g
Δ⁻-map-inj
  : ∀ (f g : Δ-Hom⁻ m n)
  → (∀ i → Δ⁻-map f i ≡ Δ⁻-map g i)
  → f ≡ g
```

<details>
<summary>This follows from a giant case bash that isn't particularly
enlightening.
</summary>

```agda
Δ⁺-map-inj done⁺ done⁺ p = refl
Δ⁺-map-inj (shift⁺ f) (shift⁺ g) p =
  ap shift⁺ (Δ⁺-map-inj f g (fsuc-inj ⊙ p))
Δ⁺-map-inj (shift⁺ f) (keep⁺ g) p =
  absurd (fzero≠fsuc (sym (p 0)))
Δ⁺-map-inj (keep⁺ f) (shift⁺ g) p =
  absurd (fzero≠fsuc (p 0))
Δ⁺-map-inj (keep⁺ f) (keep⁺ g) p =
  ap keep⁺ (Δ⁺-map-inj f g (fsuc-inj ⊙ p ⊙ fsuc))

Δ⁻-map-inj {m = zero} done⁻ done⁻ p = refl
Δ⁻-map-inj {m = suc m} (crush⁻ f) (crush⁻ g) p =
  ap crush⁻ (Δ⁻-map-inj f g (p ⊙ fsuc))
Δ⁻-map-inj {m = suc (suc m)} (crush⁻ f) (keep⁻ g) p =
  absurd (fzero≠fsuc (sym (Δ⁻-map-zero f) ∙ p 1))
Δ⁻-map-inj {m = suc (suc m)} (keep⁻ f) (crush⁻ g) p =
  absurd (fsuc≠fzero (p 1 ∙ Δ⁻-map-zero g))
-- Duplicate cases to keep exact split happy
Δ⁻-map-inj {m = suc zero} (keep⁻ f) (keep⁻ g) p =
  ap keep⁻ (Δ⁻-map-inj f g (fsuc-inj ⊙ p ⊙ fsuc))
Δ⁻-map-inj {m = suc (suc m)} (keep⁻ f) (keep⁻ g) p =
  ap keep⁻ (Δ⁻-map-inj f g (fsuc-inj ⊙ p ⊙ fsuc))
```
</details>

With a bit of work, we can show that the interpretations take
identities to identities and composites to composites. Pure more
succinctly, the interpretation functions are functorial.

```agda
Δ⁺-map-id : ∀ (i : Fin m) → Δ⁺-map id⁺ i ≡ i
Δ⁻-map-id : ∀ (i : Fin m) → Δ⁻-map id⁻ i ≡ i

Δ⁺-map-∘
  : (f : Δ-Hom⁺ n o) (g : Δ-Hom⁺ m n)
  → ∀ (i : Fin m) → Δ⁺-map (f ∘⁺ g) i ≡ Δ⁺-map f (Δ⁺-map g i)
Δ⁻-map-∘
  : (f : Δ-Hom⁻ n o) (g : Δ-Hom⁻ m n)
  → ∀ (i : Fin m) → Δ⁻-map (f ∘⁻ g) i ≡ Δ⁻-map f (Δ⁻-map g i)
```

<details>
<summary>This follows from another series of case bashes.
</summary>

```agda
Δ⁺-map-id fzero = refl
Δ⁺-map-id (fsuc i) = ap fsuc (Δ⁺-map-id i)

Δ⁻-map-id fzero = refl
Δ⁻-map-id (fsuc i) = ap fsuc (Δ⁻-map-id i)

Δ⁺-map-∘ done⁺ done⁺ i = fabsurd i
Δ⁺-map-∘ (shift⁺ f) (shift⁺ g) i = ap fsuc (Δ⁺-map-∘ f (shift⁺ g) i)
Δ⁺-map-∘ (shift⁺ f) (keep⁺ g) i = ap fsuc (Δ⁺-map-∘ f (keep⁺ g) i)
Δ⁺-map-∘ (keep⁺ f) (shift⁺ g) i = ap fsuc (Δ⁺-map-∘ f g i)
Δ⁺-map-∘ (keep⁺ f) (keep⁺ g) fzero = refl
Δ⁺-map-∘ (keep⁺ f) (keep⁺ g) (fsuc i) = ap fsuc (Δ⁺-map-∘ f g i)

-- We can reduce the number of cases by handling all 'fzero' cases
-- at once.
Δ⁻-map-∘ {n = zero} {o = zero} done⁻ done⁻ i =
  fabsurd i
Δ⁻-map-∘ {n = suc n} {o = suc o} f g fzero =
  Δ⁻-map (f ∘⁻ g) fzero     ≡⟨ Δ⁻-map-zero (f ∘⁻ g) ⟩
  fzero                     ≡˘⟨ Δ⁻-map-zero f ⟩
  Δ⁻-map f fzero            ≡˘⟨ ap (Δ⁻-map f) (Δ⁻-map-zero g) ⟩
  Δ⁻-map f (Δ⁻-map g fzero) ∎
Δ⁻-map-∘ {n = suc n} {o = suc o} (crush⁻ f) (crush⁻ g) (fsuc i) =
  Δ⁻-map-∘ (crush⁻ f) g i
Δ⁻-map-∘ {n = suc n} {o = suc o} (crush⁻ f) (keep⁻ g) (fsuc i) =
  Δ⁻-map-∘ f g i
Δ⁻-map-∘ {n = suc n} {o = suc o} (keep⁻ f) (crush⁻ g) (fsuc i) =
  Δ⁻-map-∘ (keep⁻ f) g i
Δ⁻-map-∘ {n = suc n} {o = suc o} (keep⁻ f) (keep⁻ g) (fsuc i) =
  ap fsuc (Δ⁻-map-∘ f g i)
```
</details>

## Normal forms of maps

First, note that we can extend all of the operations on face
and degeneracies to operations on normal forms.

```agda
done : Δ-Hom 0 0
done .middle = 0
done .hom⁺ = done⁺
done .hom⁻ = done⁻

crush : Δ-Hom m (suc n) → Δ-Hom (suc m) (suc n)
crush f with f .middle | f .hom⁺ | f .hom⁻
... | zero  | f⁺ | done⁻ = Δ-hom (keep⁺ ¡⁺) id⁻
... | suc x | f⁺ | f⁻ = Δ-hom f⁺ (crush⁻ f⁻)

shift : Δ-Hom m n → Δ-Hom m (suc n)
shift f .middle = f .middle
shift f .hom⁺ = shift⁺ (f .hom⁺)
shift f .hom⁻ = f .hom⁻

keep : Δ-Hom m n → Δ-Hom (suc m) (suc n)
keep f .middle = suc (f .middle)
keep f .hom⁺ = keep⁺ (f .hom⁺)
keep f .hom⁻ = keep⁻ (f .hom⁻)
```

We can also define maps $[0] \to [n]$ and $[n] \to [1]$ for any $n$;
these maps will end up witnessing $[0]$ and $[1]$ as initial and terminal
objects, resp.

```agda
¡Δ : Δ-Hom 0 n
¡Δ {n = zero} = done
¡Δ {n = suc n} = shift ¡Δ

!Δ : Δ-Hom n 1
!Δ {n = zero} = ¡Δ
!Δ {n = suc n} = crush !Δ
```

The identity morphism consists of a the identity face and degeneracy.

```agda
idΔ : Δ-Hom n n
idΔ .middle = _
idΔ .hom⁺ = id⁺
idΔ .hom⁻ = id⁻
```

Unfortunately, composites are not so simple, as we need to transform
an alternating chain of face and degeneracy maps into a single pair of
face and degenerac maps. This requires us to construct the following
4-way composition map.


```agda
composeΔ : Δ-Hom⁺ n o → Δ-Hom⁻ m n → Δ-Hom⁺ l m → Δ-Hom⁻ k l → Δ-Hom k o
```

There are quite a few cases here, so we will go through each individually.
The first case is relatively straightforward: the composite of the chain
$$\id_{-} \circ \id_{0} \circ g^{+} \circ g^{-}$$
is $g^{+} \circ g^{-}$.

```agda
composeΔ done⁺ done⁻ g⁺ g⁻ =
  Δ-hom g⁺ g⁻
```

If the first map in the chain is a composite with a face map ala
$$(\delta \circ f^{+}) \circ f^{-} \circ g^{+} \circ g^{-}$$
then we can reassociate and recurse on the rest of the chain.

```agda
composeΔ (shift⁺ f⁺) f⁻ g⁺ g⁻ =
  shift (composeΔ f⁺ f⁻ g⁺ g⁻)
```

Conversely, if domain of the chain is $0$, then we know that the
entire chain must be equal to the map out of the initial object.

```agda
composeΔ (keep⁺ f⁺) f⁻ g⁺ done⁻ =
  ¡Δ
```

If the final map in the chain is a composite with a degeneracy like
$$f^{+} \circ f^{-} \circ g^{+} \circ (g^{-} \circ \sigma)$$
then we can again reassociate and recurse on the rest of the chain.

```agda
composeΔ (keep⁺ f⁺) f⁻ g⁺ (crush⁻ g⁻) =
  crush (composeΔ (keep⁺ f⁺) f⁻ g⁺ g⁻)
```

If the inner two maps are composites with a face and degeneracy
map like
$$f^{+} \circ (f^{-} \circ \sigma) \circ (\delta \circ g^{+}) \circ g^{-}$$
then we can eliminate the face and degeneracy map, and recurse.

```agda
composeΔ (keep⁺ f⁺) (crush⁻ f⁻) (shift⁺ g⁺) (keep⁻ g⁻) =
  composeΔ (keep⁺ f⁺) f⁻ g⁺ (keep⁻ g⁻)
```

If only one map in the sequence does touches the 0th position, then we can
commute the relevant face/degeneracy outwards and recurse.

```agda
composeΔ (keep⁺ f⁺) (crush⁻ f⁻) (keep⁺ g⁺) (keep⁻ g⁻) =
  crush (composeΔ (keep⁺ f⁺) f⁻ g⁺ g⁻)
composeΔ (keep⁺ f⁺) (keep⁻ f⁻) (shift⁺ g⁺) (keep⁻ g⁻) =
  shift (composeΔ f⁺ f⁻ g⁺ (keep⁻ g⁻))
```

Finally, if none of the maps touch the 0th position, then we can proceed to
compose the rest of those 4 maps.

```agda
composeΔ (keep⁺ f⁺) (keep⁻ f⁻) (keep⁺ g⁺) (keep⁻ g⁻) =
  keep (composeΔ f⁺ f⁻ g⁺ g⁻)
```

We can then use this 4-way composition to construct composites of normal forms.

```agda
_∘Δ_ : Δ-Hom n o → Δ-Hom m n → Δ-Hom m o
f ∘Δ g = composeΔ (f .hom⁺) (f .hom⁻) (g .hom⁺) (g .hom⁻)
```

-- <!--
-- ```agda
-- -- Casts that compute on indices. Makes decidable equality a bit more well behaved.
-- cast⁺ : m ≡ m' → n ≡ n' → Δ-Hom⁺ m n → Δ-Hom⁺ m' n'
-- cast⁻ : m ≡ m' → n ≡ n' → Δ-Hom⁻ m n → Δ-Hom⁻ m' n'
-- castΔ : m ≡ m' → n ≡ n' → Δ-Hom m n → Δ-Hom m' n'

-- cast⁺ {zero}  {zero} {zero} {zero} p q done⁺ = done⁺
-- cast⁺ {zero}  {zero} {zero} {suc n'} p q f = absurd (Nat.zero≠suc q)
-- cast⁺ {zero}  {zero} {suc n} {zero} p q f = absurd (Nat.suc≠zero q)
-- cast⁺ {zero}  {zero} {suc n} {suc n'} p q (shift⁺ f) = shift⁺ (cast⁺ p (Nat.suc-inj q) f)
-- cast⁺ {zero}  {suc m'} {n} {n'} p q f = absurd (Nat.zero≠suc p)
-- cast⁺ {suc m} {zero} {n} {n'} p q f = absurd (Nat.suc≠zero p)
-- cast⁺ {suc m} {suc m'} {suc n} {zero} p q f = absurd (Nat.suc≠zero q)
-- cast⁺ {suc m} {suc m'} {suc n} {suc n'} p q (shift⁺ f) = shift⁺ (cast⁺ p (Nat.suc-inj q) f)
-- cast⁺ {suc m} {suc m'} {suc n} {suc n'} p q (keep⁺ f) = keep⁺ (cast⁺ (Nat.suc-inj p) (Nat.suc-inj q) f)

-- cast⁻ {zero} {zero} {zero} {zero} p q done⁻ = done⁻
-- cast⁻ {zero} {zero} {zero} {suc n'} p q f = absurd (Nat.zero≠suc q)
-- cast⁻ {zero} {suc m'} {n} {n'} p q f = absurd (Nat.zero≠suc p)
-- cast⁻ {suc m} {zero} {n} {n'} p q f = absurd (Nat.suc≠zero p)
-- cast⁻ {suc m} {suc m'} {suc n} {zero} p q f = absurd (Nat.suc≠zero q)
-- cast⁻ {suc m} {suc m'} {suc n} {suc n'} p q (crush⁻ f) = crush⁻ (cast⁻ (Nat.suc-inj p) q f)
-- cast⁻ {suc m} {suc m'} {suc n} {suc n'} p q (keep⁻ f) = keep⁻ (cast⁻ (Nat.suc-inj p) (Nat.suc-inj q) f)

-- castΔ p q f .middle = f .middle
-- castΔ p q f .hom⁺ = cast⁺ refl q (f .hom⁺)
-- castΔ p q f .hom⁻ = cast⁻ p refl (f .hom⁻)

-- cast⁺-refl : ∀ (f : Δ-Hom⁺ m n) → cast⁺ refl refl f ≡ f
-- cast⁺-refl {m = 0} {n = 0} done⁺ = refl
-- cast⁺-refl {m = zero} {n = suc n} (shift⁺ f) = ap shift⁺ (cast⁺-refl f)
-- cast⁺-refl {m = suc m} {n = suc n} (shift⁺ f) = ap shift⁺ (cast⁺-refl f)
-- cast⁺-refl {m = suc m} {n = suc n} (keep⁺ f) = ap keep⁺ (cast⁺-refl f)

-- cast⁻-refl : ∀ (f : Δ-Hom⁻ m n) → cast⁻ refl refl f ≡ f
-- cast⁻-refl {m = 0} {n = 0} done⁻ = refl
-- cast⁻-refl {m = (suc m)} {n = (suc n)} (crush⁻ f) = ap crush⁻ (cast⁻-refl f)
-- cast⁻-refl {m = (suc m)} {n = (suc n)} (keep⁻ f) = ap keep⁻ (cast⁻-refl f)

-- cast⁺≃pathp
--   : {f : Δ-Hom⁺ m n} {g : Δ-Hom⁺ m' n'}
--   → (p : m ≡ m') (q : n ≡ n')
--   → (cast⁺ p q f ≡ g) ≃ PathP (λ i → Δ-Hom⁺ (p i) (q i)) f g
-- cast⁺≃pathp {m = m} {n = n} {f = f} {g = g} p q =
--   J₂ mot (λ f g → ∙-pre-equiv (sym (cast⁺-refl f))) p q f g
--   where
--     mot : ∀ (m' n' : Nat) → m ≡ m' → n ≡ n' → Type _
--     mot m' n' p q =
--       ∀ (f : Δ-Hom⁺ m n) (g : Δ-Hom⁺ m' n')
--       → (cast⁺ p q f ≡ g) ≃ PathP (λ i → Δ-Hom⁺ (p i) (q i)) f g

-- cast⁻≃pathp
--   : {f : Δ-Hom⁻ m n} {g : Δ-Hom⁻ m' n'}
--   → (p : m ≡ m') (q : n ≡ n')
--   → (cast⁻ p q f ≡ g) ≃ PathP (λ i → Δ-Hom⁻ (p i) (q i)) f g
-- cast⁻≃pathp {m = m} {n = n} {f = f} {g = g} p q =
--   J₂ mot (λ f g → ∙-pre-equiv (sym (cast⁻-refl f))) p q f g
--   where
--     mot : ∀ (m' n' : Nat) → m ≡ m' → n ≡ n' → Type _
--     mot m' n' p q =
--       ∀ (f : Δ-Hom⁻ m n) (g : Δ-Hom⁻ m' n')
--       → (cast⁻ p q f ≡ g) ≃ PathP (λ i → Δ-Hom⁻ (p i) (q i)) f g

-- shift⁺-inj
--   : ∀ {f g : Δ-Hom⁺ m n}
--   → shift⁺ f ≡ shift⁺ g
--   → f ≡ g
-- shift⁺-inj {m} {n} {f} {g} = ap unshift where
--   unshift : Δ-Hom⁺ m (suc n) → Δ-Hom⁺ m n
--   unshift (shift⁺ h) = h
--   unshift (keep⁺ h) = f

-- keep⁺-inj
--   : ∀ {f g : Δ-Hom⁺ m n}
--   → keep⁺ f ≡ keep⁺ g
--   → f ≡ g
-- keep⁺-inj {m} {n} {f} {g} = ap unkeep where
--   unkeep : Δ-Hom⁺ (suc m) (suc n) → Δ-Hom⁺ m n
--   unkeep (keep⁺ h) = h
--   unkeep (shift⁺ h) = f

-- crush⁻-inj
--   : ∀ {f g : Δ-Hom⁻ m (suc n)}
--   → crush⁻ f ≡ crush⁻ g
--   → f ≡ g
-- crush⁻-inj {m} {n} {f} {g} = ap uncrush where
--   uncrush : Δ-Hom⁻ (suc m) (suc n) → Δ-Hom⁻ m (suc n)
--   uncrush (crush⁻ h) = h
--   uncrush (keep⁻ h) = f

-- keep⁻-inj
--   : ∀ {f g : Δ-Hom⁻ m n}
--   → keep⁻ f ≡ keep⁻ g
--   → f ≡ g
-- keep⁻-inj {m} {n} {f} {g} = ap unkeep where
--   unkeep : Δ-Hom⁻ (suc m) (suc n) → Δ-Hom⁻ m n
--   unkeep (keep⁻ h) = h
--   unkeep (crush⁻ h) = f

-- is-shift⁺ : Δ-Hom⁺ m n → Type
-- is-shift⁺ done⁺ = ⊥
-- is-shift⁺ (shift⁺ _) = ⊤
-- is-shift⁺ (keep⁺ _) = ⊥

-- is-keep⁺ : Δ-Hom⁺ m n → Type
-- is-keep⁺ done⁺ = ⊥
-- is-keep⁺ (shift⁺ _) = ⊥
-- is-keep⁺ (keep⁺ _) = ⊤

-- is-crush⁻ : Δ-Hom⁻ m n → Type
-- is-crush⁻ done⁻ = ⊥
-- is-crush⁻ (crush⁻ f) = ⊤
-- is-crush⁻ (keep⁻ f) = ⊥

-- is-keep⁻ : Δ-Hom⁻ m n → Type
-- is-keep⁻ done⁻ = ⊥
-- is-keep⁻ (crush⁻ f) = ⊥
-- is-keep⁻ (keep⁻ f) = ⊤

-- shift⁺≠keep⁺
--   : ∀ {f : Δ-Hom⁺ (suc m) n} {g : Δ-Hom⁺ m n}
--   → ¬ (shift⁺ f ≡ keep⁺ g)
-- shift⁺≠keep⁺ p = subst is-shift⁺ p tt

-- keep⁺≠shift⁺
--   : ∀ {f : Δ-Hom⁺ m n} {g : Δ-Hom⁺ (suc m) n}
--   → ¬ (keep⁺ f ≡ shift⁺ g)
-- keep⁺≠shift⁺ p = subst is-keep⁺ p tt

-- crush⁻≠keep⁻
--   : ∀ {f : Δ-Hom⁻ m (suc n)} {g : Δ-Hom⁻ m n}
--   → ¬ (crush⁻ f ≡ keep⁻ g)
-- crush⁻≠keep⁻ p = subst is-crush⁻ p tt

-- keep⁻≠crush⁻
--   : ∀ {f : Δ-Hom⁻ m n} {g : Δ-Hom⁻ m (suc n)}
--   → ¬ (keep⁻ f ≡ crush⁻ g)
-- keep⁻≠crush⁻ p = subst is-keep⁻ p tt
-- ```
-- -->

-- All three classes of maps have decidable equality.

-- ```agda
-- instance
--   Discrete-Δ-Hom⁺ : Discrete (Δ-Hom⁺ m n)
--   Discrete-Δ-Hom⁻ : Discrete (Δ-Hom⁻ m n)
--   Discrete-Δ-Hom  : Discrete (Δ-Hom m n)
-- ```

-- <details>
-- <summary>Proving this is pretty tedious though, especially for
-- general morphisms.
-- </summary>

-- ```agda
--   Discrete-Δ-Hom⁺ {x = done⁺} {y = done⁺} =
--     yes refl
--   Discrete-Δ-Hom⁺ {x = shift⁺ x} {y = shift⁺ y} =
--     Dec-map (ap shift⁺) shift⁺-inj Discrete-Δ-Hom⁺
--   Discrete-Δ-Hom⁺ {x = shift⁺ x} {y = keep⁺ y} =
--     no shift⁺≠keep⁺
--   Discrete-Δ-Hom⁺ {x = keep⁺ x} {y = shift⁺ y} =
--     no keep⁺≠shift⁺
--   Discrete-Δ-Hom⁺ {x = keep⁺ x} {y = keep⁺ y} =
--     Dec-map (ap keep⁺) keep⁺-inj Discrete-Δ-Hom⁺

--   Discrete-Δ-Hom⁻ {x = done⁻} {y = done⁻} =
--     yes refl
--   Discrete-Δ-Hom⁻ {x = crush⁻ x} {y = crush⁻ y} =
--     Dec-map (ap crush⁻) crush⁻-inj Discrete-Δ-Hom⁻
--   Discrete-Δ-Hom⁻ {x = crush⁻ x} {y = keep⁻ y} =
--     no crush⁻≠keep⁻
--   Discrete-Δ-Hom⁻ {x = keep⁻ x} {y = crush⁻ y} =
--     no keep⁻≠crush⁻
--   Discrete-Δ-Hom⁻ {x = keep⁻ x} {y = keep⁻ y} =
--     Dec-map (ap keep⁻) keep⁻-inj Discrete-Δ-Hom⁻

--   Discrete-Δ-Hom {x = x} {y = y} with x .middle ≡? y .middle
--   ... | yes p with cast⁺ p refl (x .hom⁺) ≡? (y .hom⁺) | cast⁻ refl p (x .hom⁻) ≡? y .hom⁻
--   ... | yes q | yes r =
--     yes (Δ-Hom-path p (Equiv.to (cast⁺≃pathp p refl) q) (Equiv.to (cast⁻≃pathp refl p) r))
--   ... | yes q | no ¬r =
--     no λ s → ¬r $
--       subst (λ e → cast⁻ refl e (x .hom⁻) ≡ y .hom⁻)
--         (Nat.Nat-is-set _ _ _ _)
--         (Equiv.from (cast⁻≃pathp refl (ap middle s)) $ ap hom⁻ s)
--   ... | no ¬q | r =
--     no λ s → ¬q $
--       subst (λ e → cast⁺ e refl (x .hom⁺) ≡ y .hom⁺)
--         (Nat.Nat-is-set _ _ _ _)
--         (Equiv.from (cast⁺≃pathp (ap middle s) refl) $ ap hom⁺ s)
--   Discrete-Δ-Hom {x = x} {y = y} | no ¬p = no (¬p ⊙ ap middle)
-- ```
-- </details>

-- By [[Hedberg's theorem]], all of these morphisms form sets.

-- ```agda
-- Δ-Hom⁺-is-set : is-set (Δ-Hom⁺ m n)
-- Δ-Hom⁺-is-set = Discrete→is-set Discrete-Δ-Hom⁺

-- Δ-Hom⁻-is-set : is-set (Δ-Hom⁻ m n)
-- Δ-Hom⁻-is-set = Discrete→is-set Discrete-Δ-Hom⁻

-- Δ-Hom-is-set : is-set (Δ-Hom m n)
-- Δ-Hom-is-set = Discrete→is-set Discrete-Δ-Hom
-- ```








-- -- # Categories

-- -- ```agda
-- -- Δ⁺-concrete : make-concrete Nat Δ-Hom⁺
-- -- Δ⁺-concrete .make-concrete.id = id⁺
-- -- Δ⁺-concrete .make-concrete._∘_ = _∘⁺_
-- -- Δ⁺-concrete .make-concrete.lvl = lzero
-- -- Δ⁺-concrete .make-concrete.F₀ = Fin
-- -- Δ⁺-concrete .make-concrete.F₀-is-set = hlevel!
-- -- Δ⁺-concrete .make-concrete.F₁ = Δ⁺-map
-- -- Δ⁺-concrete .make-concrete.F₁-inj = Δ⁺-map-inj _ _
-- -- Δ⁺-concrete .make-concrete.F-id = Δ⁺-map-id
-- -- Δ⁺-concrete .make-concrete.F-∘ = Δ⁺-map-∘

-- -- Δ⁺ : Precategory lzero lzero
-- -- unquoteDef Δ⁺ = define-concrete-category Δ⁺ Δ⁺-concrete
-- -- ```

-- -- ```agda
-- -- Δ⁻-concrete : make-concrete Nat Δ-Hom⁻
-- -- Δ⁻-concrete .make-concrete.id = id⁻
-- -- Δ⁻-concrete .make-concrete._∘_ = _∘⁻_
-- -- Δ⁻-concrete .make-concrete.lvl = lzero
-- -- Δ⁻-concrete .make-concrete.F₀ = Fin
-- -- Δ⁻-concrete .make-concrete.F₀-is-set = hlevel!
-- -- Δ⁻-concrete .make-concrete.F₁ = Δ⁻-map
-- -- Δ⁻-concrete .make-concrete.F₁-inj = Δ⁻-map-inj _ _
-- -- Δ⁻-concrete .make-concrete.F-id = Δ⁻-map-id
-- -- Δ⁻-concrete .make-concrete.F-∘ = Δ⁻-map-∘

-- -- Δ⁻ : Precategory lzero lzero
-- -- unquoteDef Δ⁻ = define-concrete-category Δ⁻ Δ⁻-concrete
-- -- ```

-- -- # The simplex category

-- -- ```agda
-- -- done : Δ-Hom 0 0
-- -- done .middle = 0
-- -- done .hom⁺ = done⁺
-- -- done .hom⁻ = done⁻

-- -- crush : Δ-Hom m (suc n) → Δ-Hom (suc m) (suc n)
-- -- crush f with f .middle | f .hom⁺ | f .hom⁻
-- -- ... | zero  | f⁺ | done⁻ = Δ-hom (keep⁺ ¡⁺) id⁻
-- -- ... | suc x | f⁺ | f⁻ = Δ-hom f⁺ (crush⁻ f⁻)

-- -- shift : Δ-Hom m n → Δ-Hom m (suc n)
-- -- shift f .middle = f .middle
-- -- shift f .hom⁺ = shift⁺ (f .hom⁺)
-- -- shift f .hom⁻ = f .hom⁻

-- -- keep : Δ-Hom m n → Δ-Hom (suc m) (suc n)
-- -- keep f .middle = suc (f .middle)
-- -- keep f .hom⁺ = keep⁺ (f .hom⁺)
-- -- keep f .hom⁻ = keep⁻ (f .hom⁻)
-- -- ```

-- -- ```agda
-- -- idΔ : ∀ {n} → Δ-Hom n n
-- -- idΔ {n} .middle = n
-- -- idΔ {n} .hom⁺ = id⁺
-- -- idΔ {n} .hom⁻ = id⁻

-- -- exchange
-- --   : ∀ {m n o}
-- --   → Δ-Hom⁻ n o → Δ-Hom⁺ m n
-- --   → Δ-Hom m o
-- -- exchange done⁻ done⁺ = Δ-hom done⁺ done⁻
-- -- exchange (crush⁻ f) (shift⁺ g) = exchange f g
-- -- exchange (crush⁻ f) (keep⁺ g) = crush (exchange f g)
-- -- exchange (keep⁻ f) (shift⁺ g) = shift (exchange f g)
-- -- exchange (keep⁻ f) (keep⁺ g) = keep (exchange f g)
-- -- ```



-- -- -- ```agda
-- -- -- Δ⁺-map-pres-<
-- -- --   : ∀ {m n}
-- -- --   → (f : Δ-Hom⁺ m n)
-- -- --   → ∀ {i j} → i < j → Δ⁺-map f i < Δ⁺-map f j
-- -- -- Δ⁺-map-pres-< (shift⁺ f) {i} {j} i<j =
-- -- --   Nat.s≤s (Δ⁺-map-pres-< f i<j)
-- -- -- Δ⁺-map-pres-< (keep⁺ f) {fzero} {fsuc j} i<j =
-- -- --  Nat.s≤s Nat.0≤x
-- -- -- Δ⁺-map-pres-< (keep⁺ f) {fsuc i} {fsuc j} (Nat.s≤s i<j) =
-- -- --   Nat.s≤s (Δ⁺-map-pres-< f i<j)
-- -- -- ```

-- -- -- ```agda
-- -- -- Δ⁻-map-reflect-<
-- -- --   : ∀ {m n}
-- -- --   → (f : Δ-Hom⁻ m n)
-- -- --   → ∀ {i j} → Δ⁻-map f i < Δ⁻-map f j → i < j
-- -- -- Δ⁻-map-reflect-< (crush⁻ f) {fzero} {fsuc j} fi<fj =
-- -- --   Nat.s≤s Nat.0≤x
-- -- -- Δ⁻-map-reflect-< (crush⁻ f) {fsuc i} {fsuc j} fi<fj =
-- -- --   Nat.s≤s (Δ⁻-map-reflect-< f fi<fj)
-- -- -- Δ⁻-map-reflect-< (keep⁻ f) {fzero} {fsuc j} fi<fj =
-- -- --   Nat.s≤s Nat.0≤x
-- -- -- Δ⁻-map-reflect-< (keep⁻ f) {fsuc i} {fsuc j} (Nat.s≤s fi<fj) =
-- -- --   Nat.s≤s (Δ⁻-map-reflect-< f fi<fj)
-- -- -- ```

-- -- -- ```agda
-- -- -- Δ⁺-map-inj
-- -- --   : ∀ {m n}
-- -- --   → (f : Δ-Hom⁺ m n)
-- -- --   → ∀ {i j} → Δ⁺-map f i ≡ Δ⁺-map f j → i ≡ j
-- -- -- Δ⁺-map-inj (shift⁺ f) {i} {j} p = Δ⁺-map-inj f (fsuc-inj p)
-- -- -- Δ⁺-map-inj (keep⁺ f) {fzero} {fzero} p = refl
-- -- -- Δ⁺-map-inj (keep⁺ f) {fzero} {fsuc j} p = absurd (fzero≠fsuc p)
-- -- -- Δ⁺-map-inj (keep⁺ f) {fsuc i} {fzero} p = absurd (fzero≠fsuc (sym p))
-- -- -- Δ⁺-map-inj (keep⁺ f) {fsuc i} {fsuc j} p = ap fsuc (Δ⁺-map-inj f (fsuc-inj p))

-- -- -- Δ⁻-map-split-surj
-- -- --   : ∀ {m n}
-- -- --   → (f : Δ-Hom⁻ m n)
-- -- --   → ∀ i → fibre (Δ⁻-map f) i
-- -- -- Δ⁻-map-split-surj (crush⁻ f) i with Δ⁻-map-split-surj f i
-- -- -- ... | fzero , p = fsuc fzero , p
-- -- -- ... | fsuc j , p = fsuc (fsuc j) , p
-- -- -- Δ⁻-map-split-surj (keep⁻ f) fzero = fzero , refl
-- -- -- Δ⁻-map-split-surj (keep⁻ f) (fsuc i) =
-- -- --   Σ-map fsuc (ap fsuc) (Δ⁻-map-split-surj f i)
-- -- -- ```

-- -- -- ```agda
-- -- -- test : Fin 2 → Fin 3
-- -- -- test = Δ⁺-map (keep⁺ (shift⁺ id⁺))

-- -- -- foo : Fin 3
-- -- -- foo = {!!}
-- -- -- ```
