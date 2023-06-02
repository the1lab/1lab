```agda
open import Rewriting.StronglyNormalising

open import 1Lab.Prelude

open import Data.Rel.Closure
open import Data.Wellfounded.Base
```
-->

```agda
module Rewriting.Confluent where
```

# Confluent Rewriting Systems

<!--
```agda
private variable
  ℓ ℓ' ℓ'' : Level
  A B X : Type ℓ
  R : A → A → Type ℓ
```
-->

Many problems in computer science can be phrased in terms of
**term rewriting systems**. Concretely, these are given by a collection
of terms in some language, along with a collection of rules that describe
how we can simplify terms. As an example, the untyped $\lambda$-calculus
can be naturally presented as a term rewriting system, where only
reduction rule is $\beta$-reduction. More abstractly, a rewriting system
on a type $A$ is simply a relation $\leadsto$ on $A$ which encodes the
rewriting rules. Sequences of rewrites are then described using the
[reflexive transitive closure] of $\leadsto$.

[reflexive transitive closure]: Data.Rel.Closure.html#reflexive-transitive-closure.html

Note that term rewriting systems may be non-deterministic, as multiple
rewrite rules can apply to a term $t$. This means that multiple
strategies of applying the rules may lead to different answers, which is
quite problematic if we want to use the rewriting system to simplify
expressions. It would be useful if we could prove *some* property of the
relation that would guarantee that this situation does not occur.

This leads us to the notion of **confluence**. We say a relation $\leadsto$
is confluent if there for all pairs of reduction chains $a \leadsto^{*} x$
and $a \leadsto^{*} y$, there exists some $z$ such that $x \leadsto^{*} z$
and $y \leadsto^{*} z$, as in the following diagram.

~~~{.quiver}
\begin{tikzcd}
  a && y \\
  \\
  x && {\exists z}
  \arrow["{*}"', from=1-1, to=3-1]
  \arrow["{*}"', dashed, from=3-1, to=3-3]
  \arrow["{*}", dashed, from=1-3, to=3-3]
  \arrow["{*}", from=1-1, to=1-3]
\end{tikzcd}
~~~

```agda
is-confluent : (A → A → Type ℓ) → Type _
is-confluent {A = A} R =
  ∀ {a x y} → Refl-trans R a x → Refl-trans R a y
  → ∃[ z ∈ A ] (Refl-trans R x z × Refl-trans R y z)
```

Note that this does *not* mean that all rewriting sequences terminate
regardless of strategy. For instance, consider the following rewriting
system:

~~~{.quiver}
\begin{tikzcd}
  \bullet & \bullet & \bullet & \cdots \\
  \\
  \bullet
  \arrow[from=1-1, to=3-1]
  \arrow[from=1-2, to=3-1]
  \arrow[from=1-3, to=3-1]
  \arrow[from=1-2, to=1-3]
  \arrow[from=1-1, to=1-2]
  \arrow[from=1-4, to=3-1]
  \arrow[from=1-3, to=1-4]
\end{tikzcd}
~~~

There is an infinitely long sequence of rewrites extending to the right,
so a bad strategy will never terminate. However, we can always reconcile
diverging paths by rewriting to the term at the bottom of the diagram.

<!-- [TODO: Reed M, 02/06/2023] Prove this using Maybe (Nat ^op) -->

## The Church-Rosser Property

A rewriting system $\leadsto$ yields an equivalence relation on terms via
the [reflexive symmetric transitive closure] of $\leadsto$. This leads to
a variant of confluence known as the **Church-Rosser Property**, which
requires a $z$ for every pair of equivalent terms $x$ and $y$ such that
$x \leadsto^{z}$ and $y \leadsto^{z}$.

[reflexive symmetric transitive closure]: Data.Rel.Closure.html#reflexive-symmetric-transitive-closure.html

~~~{.quiver}
\begin{tikzcd}
  x && y \\
  & z
  \arrow["{*}"', dashed, from=1-1, to=2-2]
  \arrow["{*}", dashed, from=1-3, to=2-2]
  \arrow["{*}", tail reversed, from=1-1, to=1-3]
\end{tikzcd}
~~~

```agda
has-church-rosser : (A → A → Type ℓ) → Type _
has-church-rosser {A = A} R =
  ∀ {x y} → Refl-sym-trans R x y
  → ∃[ z ∈ A ] (Refl-trans R x z × Refl-trans R y z)
```

At first glance, this seems like a stronger condition than confluence,
as Church-Rosser also gives us diamonds of the following shape:

~~~{.quiver}
\begin{tikzcd}
  a && y \\
  \\
  x && {\exists z}
  \arrow["{*}", from=3-1, to=1-1]
  \arrow["{*}"', dashed, from=3-1, to=3-3]
  \arrow["{*}", dashed, from=1-3, to=3-3]
  \arrow["{*}"', from=1-3, to=1-1]
\end{tikzcd}
~~~

Somewhat surprisingly, it turns out that the two conditions are equivalent!
Showing that Church-Rosser implies confluence is rather easy: if we
have two reduction sequences $a \leadsto^{*} x$ and $a \leadsto^{*} y$,
we can invert one side to get an equivalence in the reflexive symmetric
transitive closure, and then invoke Church-Rosser to get the desired
pair of reductions.

```agda
church-rosser→confluent : has-church-rosser R → is-confluent R
church-rosser→confluent church-rosser a→*x a→*y =
  church-rosser $
    transitive
      (symmetric (refl-trans→refl-sym-trans a→*x))
      (refl-trans→refl-sym-trans a→*y)
```

The converse is much more tricky, and requires introducing an intermediate
notion of **semiconfluence**, which yields solutions to diamonds of the
following form.

~~~{.quiver}
\begin{tikzcd}
  a && y \\
  \\
  x && {\exists z}
  \arrow["{*}"', from=1-1, to=3-1]
  \arrow["{*}"', dashed, from=3-1, to=3-3]
  \arrow["{*}", dashed, from=1-3, to=3-3]
  \arrow[from=1-1, to=1-3]
\end{tikzcd}
~~~

```agda
is-semi-confluent : (A → A → Type ℓ) → Type _
is-semi-confluent {A = A} R =
  ∀ {a x y} → Refl-trans R a x → R a y
  → ∃[ z ∈ A ] (Refl-trans R x z × Refl-trans R y z)
```

Confluence obviously implies semi-confluence.

```agda
confluent→semiconfluent : is-confluent R → is-semi-confluent R
confluent→semiconfluent conf a→*x a→y = conf a→*x [ a→y ]
```

Furthermore, semi-confluence implies Church-Rosser. Let $\leadsto$ be a
semi-confluent rewriting system, and let $x \leftrightarrow^{*} y$ be a
pair of convertible elements. We proceed by inducting over the reduction
chain $x \leftrightarrow^{*} y$. If the chain is empty, then we can
form the trivial diamond, and we are done.

If we have a reduction chain $x \to x' \leftrightarrow^{*} y$, then
can perform induction on the $x' \leftrightarrow^{*} y$ to obtain
a $v$ with $x' \to^{*} v$ and $y \to^{*} v$, as in the following diagram.

~~~{.quiver}
\begin{tikzcd}
  x && {x'} && y \\
  \\
  && v
  \arrow["{*}"{description}, from=1-3, to=3-3]
  \arrow["{*}"{description}, from=1-5, to=3-3]
  \arrow["{*}"{description}, tail reversed, from=1-3, to=1-5]
  \arrow[from=1-1, to=1-3]
\end{tikzcd}
~~~

Let's re-arrange the diagram a bit, adding in a trivial reduction
of $v$ to $v$.

~~~{.quiver}
\begin{tikzcd}
        {x'} && x && {x'} && y \\
        \\
        && v && v
        \arrow["{*}"{description}, from=1-5, to=3-5]
        \arrow["{*}"{description}, from=1-7, to=3-5]
        \arrow["{*}"{description}, tail reversed, from=1-5, to=1-7]
        \arrow[from=1-3, to=1-5]
        \arrow[from=1-3, to=1-1]
        \arrow["{*}"{description}, from=1-3, to=3-3]
        \arrow["{*}"{description}, from=3-5, to=3-3]
\end{tikzcd}
~~~

We can then apply semi-confluence to the pair $x \to x'$ and $x \to^{*} v$
to get some $w$ with reductions $x' \to^{*} w$ and $v \to^{*} w$.

~~~{.quiver}
\begin{tikzcd}
  {x'} && x && {x'} && y \\
  \\
  && v && v
  \arrow["{*}"{description}, from=1-5, to=3-5]
  \arrow["{*}"{description}, from=1-7, to=3-5]
  \arrow["{*}"{description}, tail reversed, from=1-5, to=1-7]
  \arrow[from=1-3, to=1-5]
  \arrow[from=1-3, to=1-1]
  \arrow["{*}"{description}, from=1-3, to=3-3]
  \arrow["{*}"{description}, from=3-5, to=3-3]
\end{tikzcd}
~~~

This yields a pair of reductions $x \to^{*} w$ and $y \to^{*} w$,
completing this case.

~~~{.quiver}
\begin{tikzcd}
  {x'} && x && {x'} && y \\
  \\
  w && v && v
  \arrow["{*}"{description}, from=1-5, to=3-5]
  \arrow["{*}"{description}, color={rgb,255:red,214;green,92;blue,92}, from=1-7, to=3-5]
  \arrow["{*}"{description}, tail reversed, from=1-5, to=1-7]
  \arrow[from=1-3, to=1-5]
  \arrow[color={rgb,255:red,214;green,92;blue,92}, from=1-3, to=1-1]
  \arrow["{*}"{description}, from=1-3, to=3-3]
  \arrow["{*}"{description}, color={rgb,255:red,214;green,92;blue,92}, from=3-5, to=3-3]
  \arrow["{*}"{description}, color={rgb,255:red,214;green,92;blue,92}, from=3-3, to=3-1]
  \arrow["{*}"{description}, color={rgb,255:red,214;green,92;blue,92}, from=1-1, to=3-1]
\end{tikzcd}
~~~

Finally, suppose we have a reduction chain $x' \to x \leftrightarrow^{*} y$.
We can perform induction on the $x \leftrightarrow^{*} y$ to obtain
a $v$ with $x \to^{*} v$ and $y \to^{*} v$, as in the following diagram.

~~~{.quiver}
\begin{tikzcd}
  x && {x'} && y \\
  \\
  && v
  \arrow["{*}"{description}, from=1-3, to=3-3]
  \arrow["{*}"{description}, from=1-5, to=3-3]
  \arrow["{*}"{description}, tail reversed, from=1-3, to=1-5]
  \arrow[from=1-3, to=1-1]
\end{tikzcd}
~~~

We can then apply semi-confluence to the reduction pair $x \to x'$ and
$x \to^{*} v$, yielding the following diagram.

~~~{.quiver}
\begin{tikzcd}
  x && {x'} && y \\
  \\
  w && v
  \arrow["{*}"{description}, from=1-3, to=3-3]
  \arrow["{*}"{description}, from=1-5, to=3-3]
  \arrow["{*}"{description}, tail reversed, from=1-3, to=1-5]
  \arrow[from=1-3, to=1-1]
  \arrow["{*}"{description}, from=1-1, to=3-1]
  \arrow["{*}"{description}, from=3-3, to=3-1]
\end{tikzcd}
~~~

We can then chase some arrows to determine that we have constructed
a pair of reductions $x \to^{*} w$ and $y \to^{*} w$, completing the proof.

~~~{.quiver}
\begin{tikzcd}
  x && {x'} && y \\
  \\
  w && v
  \arrow["{*}"{description}, from=1-3, to=3-3]
  \arrow["{*}"{description}, color={rgb,255:red,214;green,92;blue,92}, from=1-5, to=3-3]
  \arrow["{*}"{description}, tail reversed, from=1-3, to=1-5]
  \arrow[color={rgb,255:red,214;green,92;blue,92}, from=1-3, to=1-1]
  \arrow["{*}"{description}, color={rgb,255:red,214;green,92;blue,92}, from=1-1, to=3-1]
  \arrow["{*}"{description}, color={rgb,255:red,214;green,92;blue,92}, from=3-3, to=3-1]
\end{tikzcd}
~~~

```agda
semiconfluent→church-rosser : is-semi-confluent R → has-church-rosser R
semiconfluent→church-rosser {R = R} semiconf x↔y =
  Refl-sym-trans-rec-chain
    (λ x y →  ∃[ z ∈ _ ] (Refl-trans R x z × Refl-trans R y z))
    (inc (_ , reflexive , reflexive))
    (λ {x} {x'} {y} x→x' _ x'→*v*←y → do
      v , x'→*v , y→*v ← x'→*v*←y
      w , v→*w , x'→*w ← semiconf (transitive [ x→x' ] x'→*v) x→x'
      pure (w , transitive [ x→x' ] x'→*w , transitive y→*v v→*w))
    (λ {x} {x'} {y} x'→x _ x'→*v*←y → do
      v , x'→*v , y→*v ← x'→*v*←y
      w , v→*w , x→*w ← semiconf x'→*v x'→x 
      pure (w , x→*w , transitive y→*v v→*w))
    squash
    x↔y
```

We can use these 3 proofs to show that confluence, Church-Rosser, and
semi-confluence are equivalent.

```agda
semiconfluent→confluent : is-semi-confluent R → is-confluent R
semiconfluent→confluent conf =
  church-rosser→confluent (semiconfluent→church-rosser conf)

confluent→church-rosser : is-confluent R → has-church-rosser R
confluent→church-rosser conf =
  semiconfluent→church-rosser (confluent→semiconfluent conf)

church-rosser→semiconfluent : has-church-rosser R → is-semi-confluent R
church-rosser→semiconfluent church-rosser =
  confluent→semiconfluent (church-rosser→confluent church-rosser)
```

## Local Confluence and Newman's Lemma

Proving confluence can be difficult, as it requires looking at
forks of arbitrary depth. It is much easier to only consider single-step
forks, which leads to a notion of **local confluence**.

```agda
is-locally-confluent : (A → A → Type ℓ) → Type _
is-locally-confluent {A = A} R =
  ∀ {a x y} → R a x → R a y
  → ∃[ z ∈ A ] (Refl-trans R x z × Refl-trans R y z)
```

Note that local confluence is a weaker property than confluence. As
a concrete example, consider the following rewrite system:

~~~{.quiver}
\begin{tikzcd}
  w & x && y & z \\
  \\
  \\
  && {}
  \arrow[curve={height=-12pt}, from=1-2, to=1-4]
  \arrow[curve={height=-12pt}, from=1-4, to=1-2]
  \arrow[from=1-2, to=1-1]
  \arrow[from=1-4, to=1-5]
\end{tikzcd}
~~~

There are two single-step forks in this system:
$w \leftarrow x \rightarrow y$ and $x \leftarrow y \to z$. Both of
these are locally confluent: We can reduce both to $w$ for the first fork,
and $z$ for the second. However, it is *not* confluent: there is a fork
$w \leftarrow^{*} x \to^{*} z$ that cannot be reconciled.

However, if the rewrite system is [strongly normalising], then local
confluence implies confluence.

[strongly normalising]: Rewriting.StronglyNormalising.html

Let $\to$ be a strongly normalising, locally confluent rewriting system.
Consider some fork $x \leftarrow^{*} a \to^{*} y$. As $\to$ is strongly
normalizing, we can perform well-founded induction, attempting to
produce a common reduct for both sides of the fork.

If either side of tthe fork is a zero-length chain, then we can use the
trivial joins $a \to{*} x \leftarrow^{*} a$ and $a \to{*} y
\leftarrow^{*} a$, resp.  If both chains are non-trivial, we end up with
the following diagram:

~~~{.quiver}
\begin{tikzcd}
  && a \\
  & {x'} && {y'} \\
  x &&&& y
  \arrow[from=1-3, to=2-2]
  \arrow[from=1-3, to=2-4]
  \arrow["{*}"{description}, from=2-2, to=3-1]
  \arrow["{*}"{description}, from=2-4, to=3-5]
\end{tikzcd}
~~~

We can then apply local confluence to $a \to x'$ and $a \to y'$.

~~~{.quiver}
\begin{tikzcd}
  && a \\
  & {x'} && {y'} \\
  x && u && y
  \arrow[from=1-3, to=2-2]
  \arrow[from=1-3, to=2-4]
  \arrow["{*}"{description}, from=2-2, to=3-1]
  \arrow["{*}"{description}, from=2-4, to=3-5]
  \arrow["{*}"{description}, from=2-2, to=3-3]
  \arrow["{*}"{description}, from=2-4, to=3-3]
\end{tikzcd}
~~~

Next, we can recurse on $x' \to^{*} x$ and $x' \to^{*} u$.

~~~{.quiver}
\begin{tikzcd}
  && a \\
  & {x'} && {y'} \\
  x && u && y \\
  & v
  \arrow[from=1-3, to=2-2]
  \arrow[from=1-3, to=2-4]
  \arrow["{*}"{description}, from=2-2, to=3-1]
  \arrow["{*}"{description}, from=2-4, to=3-5]
  \arrow["{*}"{description}, from=2-2, to=3-3]
  \arrow["{*}"{description}, from=2-4, to=3-3]
  \arrow["{*}"{description}, from=3-1, to=4-2]
  \arrow["{*}"{description}, from=3-3, to=4-2]
\end{tikzcd}
~~~

We can recurse yet again on $y' \to^{*} v$ and $y' \to^{*} y$.

~~~{.quiver}
\begin{tikzcd}
  && a \\
  & {x'} && {y'} \\
  x && u && y \\
  & v \\
  && w
  \arrow[from=1-3, to=2-2]
  \arrow[from=1-3, to=2-4]
  \arrow["{*}"{description}, from=2-2, to=3-1]
  \arrow["{*}"{description}, from=2-4, to=3-5]
  \arrow["{*}"{description}, from=2-2, to=3-3]
  \arrow["{*}"{description}, from=2-4, to=3-3]
  \arrow["{*}"{description}, from=3-1, to=4-2]
  \arrow["{*}"{description}, from=3-3, to=4-2]
  \arrow["{*}"{description}, from=3-5, to=5-3]
  \arrow["{*}"{description}, from=4-2, to=5-3]
\end{tikzcd}
~~~

The bottom half of the square yields the desired pair of reductions,
finishing the proof.

~~~{.quiver}
\begin{tikzcd}
\begin{tikzcd}
  && a \\
  & {x'} && {y'} \\
  x && u && y \\
  & v \\
  && w
  \arrow[from=1-3, to=2-2]
  \arrow[from=1-3, to=2-4]
  \arrow["{*}"{description}, from=2-2, to=3-1]
  \arrow["{*}"{description}, from=2-4, to=3-5]
  \arrow["{*}"{description}, from=2-2, to=3-3]
  \arrow["{*}"{description}, from=2-4, to=3-3]
  \arrow["{*}"{description}, color={rgb,255:red,214;green,92;blue,92}, from=3-1, to=4-2]
  \arrow["{*}"{description}, from=3-3, to=4-2]
  \arrow["{*}"{description}, color={rgb,255:red,214;green,92;blue,92}, from=3-5, to=5-3]
  \arrow["{*}"{description}, color={rgb,255:red,214;green,92;blue,92}, from=4-2, to=5-3]
\end{tikzcd}\end{tikzcd}
~~~

```agda
strong-normalising+locally-confluent→confluent
  : is-strongly-normalising R → is-locally-confluent R
  → is-confluent R
strong-normalising+locally-confluent→confluent
  {R = R} sn local-conf {a} {x} {z} a→*x a→*y =
    Wf-induction _ sn
      (λ a →
        ∀ {x y} → Refl-trans R a x → Refl-trans R a y
        → ∃[ z ∈ _ ] (Refl-trans R x z × Refl-trans R y z))
    (λ a ih {x} {y} a→*x a→*y →
      Refl-trans-case-fork
        (λ a x y
          → (∀ a' → Trans R a a'
             → ∀ {x y} → Refl-trans R a' x → Refl-trans R a' y
             → ∃[ z ∈ _ ] (Refl-trans R x z × Refl-trans R y z))
          → ∃[ z ∈ _ ] (Refl-trans R x z × Refl-trans R y z))
        (λ a→*y _ → inc (_ , a→*y , reflexive))
        (λ a→*x _ → inc (_ , reflexive , a→*x))
        (λ a→x' x'→*x a→y' y'→*y ih → do
          u , x'→*u , y'→*u ← local-conf a→x' a→y'
          v , x→*v , u→*v ← ih _ [ a→x' ] x'→*x x'→*u
          w , v→*w , y→*w ← ih _ [ a→y' ] (transitive y'→*u u→*v) y'→*y
          pure (w , transitive x→*v v→*w , y→*w))
        hlevel!
        a→*x a→*y ih)
      a a→*x a→*y
```
