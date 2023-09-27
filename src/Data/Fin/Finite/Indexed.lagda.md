<!--
```agda
open import 1Lab.Prelude

open import Data.Fin.Closure
open import Data.Fin.Finite
open import Data.Nat.Base
open import Data.Fin.Base
open import Data.Sum.Base
open import Data.Power
```
-->

```agda
module Data.Fin.Finite.Indexed where
```

<!--
```agda
private variable
  ℓ ℓ′ : Level
  S T  : Type ℓ
  P Q  : ℙ S
```
-->

# Finitely-indexed sets {defines="kuratowski-finite-subset finitely-indexed-set"}

Constructively, [[finiteness|finite]] is a pretty strong condition on a
type. Even if a truncated equivalence $\| T \simeq [n] \|$ does not
impose an _order_ on $T$, it does still mean that $T$ has decidable
equality --- if a type can not be shown to have decidable equality, it
can not be shown to be finite. Therefore, the class of finite types, in
constructive mathematics, lacks many closure properties: neither subsets
or quotients of finite types are guaranteed to be finite.

To recover those closure properties, we weaken the requirement for an
equivalence $T \simeq [n]$ to something which expresses an _upper bound_
on the elements of $T$. **Finitely-indexed sets**, also known as
$K$-finite sets since they were introduced by Kuratowski, recover
closure under quotients.

A type $T$ is **finitely indexed** if [[there merely exists|merely]] a
natural number $n$ and a [[surjection|surjection between sets]] $[n]
\epi T$. For this, we define the intermediate notion of **finite
cover**: A finite cover of $T$ is _the data of_ a natural $n$ and a
surjection $[n] \epi T$.

```agda
record Finite-cover {ℓ} (A : Type ℓ) : Type ℓ where
  constructor cover
  field
    {cardinality} : Nat
    cover  : Fin cardinality → A
    covers : ∀ x → ∥ fibre cover x ∥

is-finitely-indexed : ∀ {ℓ} → Type ℓ → Type
is-finitely-indexed T = □ (Finite-cover T)
```

## Closure properties

As mentioned above, the key property that sets aside the
finitely-indexed sets from the finite sets are that the former are
closed under arbitrary quotients. We'll express this using surjections
rather than quotients (or coequalisers) since that is more directly
applicable. If $f : T \epi S$ is any surjection, and $g : [n] \epi T$ is
a finite cover, then

$$
[n] \xepi{g} T \xepi{f} S\text{.}
$$

is still a surjection --- hence, still a finite cover --- so $S$ is
_also_ finitely indexed.

```agda
surjection→finite-cover
  : (f : T → S) → (∀ x → ∥ fibre f x ∥)
  → Finite-cover T
  → Finite-cover S
surjection→finite-cover g surj' (cover f surj) = record { covers = λ x → do
  (y , p) ← surj' x
  (z , q) ← surj y
  pure (z , ap g q ∙ p) }

surjection→finitely-indexed
  : (f : T → S) → (∀ x → ∥ fibre f x ∥)
  → is-finitely-indexed T → is-finitely-indexed S
surjection→finitely-indexed f surj fi = surjection→finite-cover f surj <$> fi
```

Moreover, since any $f : [n] \equiv T$ can be treated as an $f : [n]
\epi T$, any [[finite]] type is finitely-indexed, too.

```agda
Finite→is-finitely-indexed : ⦃ _ : Finite T ⦄ → is-finitely-indexed T
Finite→is-finitely-indexed ⦃ fin eqv ⦄ = tr-□ eqv >>= λ where
  eqv → pure (cover (Equiv.from eqv) λ x → inc (_ , Equiv.η eqv _))
```

### Finitely-indexed subsets

We now turn to the question of finitely-indexed _subsets_. A subset $P :
T \to \Omega$ is finitely-indexed if its total space $\Sigma_{x : T} x
\in P$ is. To disambiguate and keep names short, we refer to types as
finitely-indexed, but to subsets as **K-finite**.

```agda
is-K-finite : ∀ {ℓ} {T : Type ℓ} → (T → Ω) → Type
is-K-finite P = is-finitely-indexed (∫ₚ P)
```

The $K$-finite subsets of $T$ are a sub-join[[semilattice]] of the
[[power-set]] lattice of $T$. That is, the empty subset is $K$-finite,
and any union is $K$-finite as well. Since the empty subset is _finite_,
it's also $K$-finite, of course.

```agda
opaque
  minimal-is-K-finite : is-K-finite (minimal {X = T})
  minimal-is-K-finite = surjection→finitely-indexed (λ ()) (λ ()) $
    Finite→is-finitely-indexed {T = ⊥}
```

But the case of unions is slightly different. Unless $A$ is assumed to
have decidable equality, we can not compute the cardinality of the union
$P \cup Q$, since we can't decide whether or not $P$ and $Q$ have some
intersection --- and we have placed no such assumption on $A$. That's
why $K$-finite subsets express an _upper bound_ on the cardinality of a
(sub)set.

We're justified in doing this by the following observation: If we had a
magical cardinality function $n(-) : (T \to \Omega) \to \bN$, then we
would have the familiar formula

$$
n(A \cup B) = (n(A) + n(B)) - n(A \cap B)\text{.}
$$

Even though we don't, if $a$ and $b$ are upper bounds for the size of
$A$ and $B$ (i.e. $n(A) \le a$ and $n(B) \le B$), then we certainly have
$n(A \cup B) \le a + b$. The fact that our covering might over-count is
not an issue here.

```agda
  union-is-K-finite : is-K-finite P → is-K-finite Q → is-K-finite (P ∪ Q)
  union-is-K-finite {P = P} {Q = Q} p-fin q-fin = do
    cover {Pn} f f-surj ← p-fin
    cover {Qn} g g-surj ← q-fin

    let
      cover' : (Fin Pn ⊎ Fin Qn) → ∫ₚ (P ∪ Q)
      cover' = λ where
        (inl x) → f x .fst , inc (inl (f x .snd))
        (inr x) → g x .fst , inc (inr (g x .snd))

      surj' : ∀ x → ∥ fibre cover' x ∥
      surj' xf = □-tr (xf .snd) >>= λ where
        (inl p) → do
          (ix , p) ← f-surj (xf .fst , p)
          pure (inl ix , Σ-prop-path! (ap fst p))
        (inr q) → do
          (ix , p) ← g-surj (xf .fst , q)
          pure (inr ix , Σ-prop-path! (ap fst p))

    surjection→finitely-indexed cover' surj' Finite→is-finitely-indexed
```

Moreover, we have that a singleton set is $K$-finite, as well.

```agda
  singleton-is-K-finite : is-set T → (x : T) → is-K-finite (λ y → elΩ (x ≡ y))
  singleton-is-K-finite t-set x = inc (cover {cardinality = 1} (λ _ → x , inc refl)
    λ (y , p) → inc (fzero , Σ-prop-path (λ _ → squash) (out! {pa = t-set _ _} p)))
```
