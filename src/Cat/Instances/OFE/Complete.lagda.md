<!--
```agda
open import Cat.Instances.OFE
open import Cat.Prelude

open import Data.Nat.Order
open import Data.Nat.Base
```
-->

```agda
module Cat.Instances.OFE.Complete where
```

<!--
```agda
open OFE-Notation

module _ {ℓ ℓ'} {A : Type ℓ} (P : OFE-on ℓ' A) where
  private
    instance _ = P
    module P = OFE-on P
```
-->

# Limits and complete OFEs

Since [OFEs] are metric-space-_like_[^1] structures, there is a natural
notion of sequences getting closer to a value: we say a sequence $f : \bN
\to A$ is a _chain_ if, given $n \le m$, we have $f(m) \within{n} f(n)$.
Looking at the case where $m = 1 + n$, this says that we have a sequence

$$
f(0) \within{0} f(1) \within{1} f(2) \within{2} f(3) \within{3} \dots
$$

where the metric interpretation of OFEs lets us read this as the
_distance_ between successive points approaching
$\lim_{n\to\infty}2^{-n} = 0$.

```agda
  is-chain : (x : Nat → A) → Type _
  is-chain f = ∀ m n → n ≤ m → f m ≈[ n ] f n
```

[^1]: An OFE is a _1-bounded, bisected ultrametric space_.

[OFEs]: Cat.Instances.OFE.html

However, in a general OFE, there is not necessarily anything "at
$\infty$": the values of the sequence get closer to each other, but
there's no specific _point_ they're getting closer to. An example of
chain without limit is as follows: let $a : A$ be an element of a set,
and consider the sequence

$$
f(n) = \underbrace{a,\dots,a}_\text{$n$ times}
$$

in the OFE of finite sequences. Clearly this satisfies the chain
condition: w.l.o.g. we can assume $m = n + k$ for some $k$, and $f(n +
k)$ certainly shares the first $n$ elements with $f(n)$. However, there
is no single list of $A$s $l$ which shares its first $n$ elements
with $f(n)$: $l$ must have a definite length, independent of $n$, which
bounds the size of its prefixes. Choosing any $n > \rm{length}(l)$
results in a value of $f(n)$ has more elements than the length-$n$
prefix of $l$.

The previous paragraph contains an unfolding of the definition of a
sequence having a limit, or, more specifically, it contains a definition
of what it means for a point to be the limit of a sequence: $a$ is the
limit of $f$ if, for all $n$, $a \within{n} f(n)$.

```agda
  is-limit : (x : Nat → A) → A → Type _
  is-limit f a = ∀ n → a ≈[ n ] f n
```

It follows at once that _the_ limit of a sequence is uniquely
determined: if $a$ and $b$ both claim to be limits of $f$, we have, for
arbitrary $n$, $a \within{n} f(n) \within{n} b$, meaning $a = b$.

```agda
  limit-is-unique
    : ∀ (f : Nat → A) {x y}
    → is-limit f x → is-limit f y → x ≡ y
  limit-is-unique f l1 l2 = P.limit _ _ λ n →
    P.≈-trans n (P.≈-sym n (l2 n)) (l1 n)
```

<!--
```agda
  Limit : (Nat → A) → Type _
  Limit f = Σ A (is-limit f)

  Limit-is-prop : (f : Nat → A) → is-prop (Limit f)
  Limit-is-prop f (a , α) (b , β) = Σ-prop-path! (limit-is-unique f α β)

  limit-from-tail
    : ∀ (f : Nat → A) x → is-chain f → is-limit (λ n → f (suc n)) x → is-limit f x
  limit-from-tail f x chain lim zero = P.bounded _ _
  limit-from-tail f x chain lim (suc n) = P.≈-trans _
    (chain (suc (suc n)) (suc n) (≤-sucr ≤-refl))
    (lim (suc n))

  limit-to-tail
    : ∀ (f : Nat → A) x → is-chain f → is-limit f x → is-limit (λ n → f (suc n)) x
  limit-to-tail f x chain lim zero = P.bounded _ _
  limit-to-tail f x chain lim (suc n) = P.step _ _ _ (lim _)
```
-->

However, some OFEs _do_ have limits for all chains: the OFE of infinite
sequences is one, for example. We refer to such an OFE as a **complete
ordered family of equivalences**, or COFE^[Feel free to pronounce it
"coffee".] for short.

```agda
  is-cofe : Type _
  is-cofe = ∀ (f : Nat → A) → is-chain f → Limit f
```

<!--
```agda
module _ {ℓ} {X : Type ℓ} (X-set : is-set X) where
```
-->

We can actually compute the limit of a sequence of sequences pretty
easily: we have a function $s : \bN \times \bN \to A$, our sequence, and
the chain condition says that, given $j \le i$ and $k \lt j$, we get
$s(i,k) = s(j,k)$. Our limit is the sequence $l(i) = s(1 + i, i)$: we
must show that $l \within{n} s(n)$, which means that, given
$k \lt n$, we must have $s(1 + k, k) = s(n,k)$. This follows by the
chain condition: $k \lt 1 + k$, and $(1 + k) \le n$, so we conclude $s(1
+ k, k) = s(n, k)$.

```agda
  Sequences-is-cofe : is-cofe (Sequences X-set)
  Sequences-is-cofe seq chain = (λ j → seq (suc j) j) , λ n k k<n →
    sym (chain _ _ k<n _ ≤-refl)
```

<!--
```agda
module _ {ℓa ℓa' ℓb ℓb'} {A : Type ℓa} {B : Type ℓb} (P : OFE-on ℓa' A) (Q : OFE-on ℓb' B) where
  private
    instance
      _ = P
      _ = Q
    module P = OFE-on P
    module Q = OFE-on P
```
-->

In passing, let us note that non-expansive maps preserve both chains
_and_ their limits.

```agda
  non-expansive→chain
    : (f : A → B) (s : Nat → A)
    → is-non-expansive f P Q → is-chain P s → is-chain Q (λ n → f (s n))
  non-expansive→chain f s ne p m n n≤m = ne .pres-≈ (p m n n≤m)

  non-expansive→limit
    : (f : A → B) (s : Nat → A) (x : A)
    → is-non-expansive f P Q → is-limit P s x → is-limit Q (λ n → f (s n)) (f x)
  non-expansive→limit f s x ne lim n = ne .pres-≈ (lim n)
```

## Banach's fixed point theorem

<!--
```agda
module _ {ℓ ℓ'} {A : Type ℓ} (P : OFE-on ℓ' A) (lim : is-cofe P) where
  private
    instance _ = P
    module P = OFE-on P
```
-->

**Banach's fixed point theorem**, in our setting, says that any
contractive $f : P \to P$ on an _inhabited_ COFE has a unique fixed
point. We'll start with uniqueness: suppose that some $a, b$ satisfy
$f(a) = a$ and $f(b) = b$. It will suffice to show that $f(a) = f(b)$,
and, working in an OFE, this further reduces to $f(a) \within{n} f(b)$
for an arbitrary $n$.

By induction, with a trivial base case, we can assume $f(a) \within{n}
f(b)$ to show $f(a) \within{1+n} f(b)$: but $f$ is contractive, so it
acts on the induction hypothesis to produce $f(f(a)) \within{1+n}
f(f(b))$.  But we assumed both $a$ and $b$ are fixed points, so this is
exactly what we want.

```agda
  banach : ∥ A ∥ → (f : P →ᶜᵒⁿ P) → Σ A λ x → f .map x ≡ x
  banach inhab f = ∥-∥-out fp-unique fp' where
    fp-unique : is-prop (Σ A λ x → f .map x ≡ x)
    fp-unique (a , p) (b , q) =
      Σ-prop-path (λ x → from-ofe-on P .fst .is-tr _ _)
        (sym p ∙∙ P.limit _ _ climb ∙∙ q) where
      climb : ∀ n → f .map a ≈[ n ] f .map b
      climb zero    = P.bounded _ _
      climb (suc n) = transport (λ i → f .map (p i) ≈[ suc n ] f .map (q i)) (f .contract n (climb n))
```

The point of showing uniqueness is that the fixed point is independent
of _how_ $P$ is inhabited: in other words, for a contractive mapping on
a COFE to have a fixed point, we needn't $x : P$ --- $x : \| P \|$ will
suffice. That aside justifes this sentence: Fix a starting point $x_0 :
P$, and consider the sequence

$$
s = x_0, f(x_0), f(f(x_0)), f(f(f(x_0))), \dots
$$

which is a chain again by an inductive argument involving contractivity
(formalised below for the curious).

```agda
    approx : A → Nat → A
    approx a zero    = a
    approx a (suc n) = f .map (approx a n)

    chain : ∀ a → is-chain P (approx a)
    chain a m zero x                = P.bounded (approx a m) a
    chain a (suc m) (suc n) (s≤s x) = f .contract n (chain a m n x)
```

I claim that the limit of $s$ is a fixed point of $f$: we can calculate

$$
f(\lim_n s(n)) = \lim_n f(s(n)) = \lim_n s(n+1) = \lim_n s(n)
$$

where we have, in turn, that non-expansive mappings preserve limits, the
very definition of $s$, and the fact that limits are insensitive to
dropping an element at the start.

```agda
    fp' : ∥ _ ∥
    fp' = do
      pt ← inhab
      let
        (it , is) = lim (approx pt) (chain pt)

        ne : is-non-expansive (f .map) P P
        ne = record { pres-≈ = λ p → P.step _ _ _ (f .contract _ p) }

        prf : f .map it ≡ it
        prf =
          f .map it                               ≡⟨ limit-is-unique P _ (non-expansive→limit _ _ _ _ _ ne is) (lim _ _ .snd) ⟩
          lim (λ n → f .map (approx pt n)) _ .fst ≡⟨ ap fst (ap (lim _) (λ i → non-expansive→chain _ _ _ _ ne (chain pt))) ⟩
          lim (λ n → approx pt (suc n)) _ .fst    ≡⟨ limit-is-unique P _ (lim _ _ .snd) (limit-to-tail P (approx pt) _ (chain pt) is) ⟩
          it                                      ∎

      pure (it , prf)
```
