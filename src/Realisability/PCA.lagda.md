<!--
```agda
open import 1Lab.Prelude

open import Data.Partial.Total
open import Data.Partial.Base
open import Data.Fin.Base hiding (_<_ ; _≤_)
open import Data.Vec.Base
```
-->

```agda
module Realisability.PCA where
```

# Partial combinatory algebras {defines="partial-combinatory-algebra"}

<!--
```agda
private variable
  ℓ : Level
  A : Type ℓ
  n : Nat
```
-->

A **partial combinatory algebra** (PCA) $\bA$ is a [[set]] equipped with
enough structure to model universal computation: a [[partial|partiality
monad]] *application* operator[^pas] and a notion of *abstraction
elimination*, which will be defined below. This structure is enough for
$\bA$ to model a simple programming language in the spirit of the
untyped lambda calculus.

[^pas]:
    A set $\bA$ equipped with *only* the application operator, and not
    necessarily with an abstraction elimination procedure, will be
    referred to as a **partial applicative structure**, or `PAS`{.Agda}.

While the definition of PCA is austere, adapting traditional encoding
techniques from untyped lambda calculus lets us show that PCAs support
encoding [[booleans|booleans in a pca]], [[pairs|pairs in a pca]],
[[sums|sums in a pca]], and even [[primitive recursion|numbers in a
pca]].

<!--
```agda
module _ {ℓ} (𝔸 : Type ℓ) where
```
-->

::: note
Formalising the partial application operator is slightly tricky. In the
literature (e.g. following de Jong [-@deJong:Realisability]) one would
imagine that the application operator on $\bA$ has type

```agda
  _ = 𝔸 → 𝔸 → ↯ 𝔸
```

i.e., that it takes two defined elements of $\bA$ and returns a partial
element. However, working with an operator of this type is rather
cumbersome, because we can't form iterated expressions like $\tt{f}\
\tt{x}\ \tt{y}$: the application $\tt{f}\ \tt{x}$ lives in $\zap \bA$,
not $\bA$, and so can not be the left operand in an application.
Instead, we define application to work over *partial* elements, i.e. the
type of our application operators is

```agda
  PAS : Type ℓ
  PAS = ↯ 𝔸 → ↯ 𝔸 → ↯ 𝔸
```
:::

## The inhabitants of a PCA

If $\bA$ is a partial combinatory algebra (or, more generally, a partial
applicative structure), the inhabitants of the type $x : \bA$ often
serve dual purposes: they can be **values** or they can be **programs**.
Of course, since PCAs implement a simple higher-order programming
language, programs are a type of value. However, there are still
situations where it is important to be clear *which* of these two roles
a given $x : \bA$ is serving.

Applying a program to a given value may not result in a value ---
execution could diverge, for example. We think of an arbitrary
application like $\tt{f}~ \tt{x}$ as a **computation**, which may or may
not produce a value --- if it does produce a value, then it comes from
exactly one value in $\bA$.

:::{.definition #values-in-a-pca alias="programs-in-a-pca"}
If $\bA$ is a [[partial combinatory algebra]], we refer to the type
$\bA$ as the type of **values in $\bA$**, or **programs in $\bA$**,
depending on the role that each inhabitant is playing.

We also refer to the type $\zap \bA$ as the type of **computations in
$\bA$**.
:::

## Abstraction elimination

The type of terms over $\bA$ with $n$ free variables is defined
inductively: A term is either one of the variables, a value drawn from
$\bA$, or the application of a term to another.

```agda
data Term (A : Type ℓ) (n : Nat) : Type (level-of A) where
  var   : Fin n → Term A n
  const : ↯⁺ A → Term A n
  app   : Term A n → Term A n → Term A n
```

If we are given a term in $n$ variables and an *environment*, a list of
$n$ values, we can define the `eval`{.Agda}uation of a term to be the
computation obtained by looking each variable up in the environment,
preserving embedded values, and using the partial applicative structure
to interpret the `app`{.Agda} constructor. Moreover, if we have a term
$t$ in $n + 1$ variables and a term $x$ in $n$ variables, we can
`inst`{.Agda}antiate $t$ with $x$ to obtain a term in $n$ variables,
where the zeroth variable used in $t$ has been replaced with $x$
throughout.

```agda
module eval (_%_ : PAS A) where
  eval : Term A n → Vec (↯⁺ A) n → ↯ A
  eval (var x)   ρ = lookup ρ x .fst
  eval (const x) ρ = x .fst
  eval (app f x) ρ = eval f ρ % eval x ρ

  inst : Term A (suc n) → Term A n → Term A n
  inst (var x) a with fin-view x
  ... | zero = a
  ... | suc i = var i
  inst (const a) _ = const a
  inst (app f x) a = app (inst f a) (inst x a)
```

These two operations are connected by the following lemma: evaluating a
term instantiated with a value is the same as evaluating the original
term in an extended environment.

```agda
  abstract
    eval-inst
      : (t : Term A (suc n)) (x : ↯⁺ A) (ρ : Vec (↯⁺ A) n)
      → eval (inst t (const x)) ρ ≡ eval t (x ∷v ρ)
    eval-inst (var i) y ρ with fin-view i
    ... | zero  = refl
    ... | suc j = refl
    eval-inst (const a) y ρ = refl
    eval-inst (app f x) y ρ = ap₂ _%_ (eval-inst f y ρ) (eval-inst x y ρ)
```

A partial applicative structure is a partial combinatory algebra when we
have an operation `abs`{.Agda} sending terms $t$ in $n + 1$ variables to
terms $\langle x \rangle t$ in $n$ variables which behave, under
evaluation, as "functions of $x$". In particular, functions should
always be defined values (`abs↓`{.Agda}), and we have a
restricted $\beta$-reduction law (`abs-β`{.Agda}) saying that applying a
function to a value should be the same as evaluating the body of the
function instantiated with that value, or equivalently in an environment
extended with that value.

```agda
record is-pca (_%_ : PAS A) : Type (level-of A) where
  open eval _%_ public
  field
    abs   : Term A (suc n) → Term A n
    abs↓  : (t : Term A (suc n)) (ρ : Vec (↯⁺ A) n) → ⌞ eval (abs t) ρ ⌟
    abs-β : (t : Term A (suc n)) (ρ : Vec (↯⁺ A) n) (a : ↯⁺ A)
          → eval (abs t) ρ % a .fst ≡ eval (inst t (const a)) ρ
```

::: warning
Traditional texts on realisability (e.g. de Jong op. cit., see also
Bauer [-@Bauer:Realisability]) define partial combinatory algebras in
terms of *combinators*, typically $\tt{S}$ and $\tt{K}$. These can be
defined using the abstraction operator in the typical way, e.g.
$$ \tt{K} = \langle x \rangle \langle y \rangle x $$.

We prefer taking the abstraction elimination procedure as a primitive
since it works better with Agda's type inference, in particular when
working against an arbitrary PCA --- but a [[combinatorially complete]]
partial applicative structure is a PCA in our sense.
:::

<details>
<summary>In the formalisation we often define and apply functions to
many arguments, so we define an $n$-ary version of the abstraction
combinator and of the $\beta$ law.</summary>

```agda
  absₙ : (k : Nat) → Term A (k + n) → Term A n
  absₙ zero    e = e
  absₙ (suc k) e = absₙ k (abs e)

  _%ₙ_ : ∀ {n} → ↯ A → Vec (↯⁺ A) n → ↯ A
  a %ₙ v with vec-view v
  ... | []       = a
  ... | (b ∷ bs) = (a %ₙ bs) % b .fst

  abstract
    abs-βₙ
      : {k n : Nat} {e : Term A (k + n)}
      → (ρ : Vec (↯⁺ A) n) (as : Vec (↯⁺ A) k)
      → (eval (absₙ k e) ρ %ₙ as) ≡ eval e (as ++ ρ)
    abs-βₙ {e = e} ρ v with vec-view v
    ... | [] = refl
    ... | (x ∷ as) = ap (_% x .fst) (abs-βₙ ρ as)
      ∙ abs-β _ (as ++ ρ) x
      ∙ eval-inst e x (as ++ ρ)
```

</details>

<!--
```agda
record PCA-on (A : Type ℓ) : Type ℓ where
  infixl 25 _%_

  field
    has-is-set : is-set A
    _%_        : ↯ A → ↯ A → ↯ A
    has-is-pca : is-pca _%_

  open is-pca has-is-pca public

PCA : (ℓ : Level) → Type (lsuc ℓ)
PCA ℓ = Σ[ X ∈ Set ℓ ] PCA-on ∣ X ∣

module PCA {ℓ} (A : PCA ℓ) where
  open PCA-on (A .snd) public
```
-->
