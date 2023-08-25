<!--
```agda
open import Rewriting.StronglyNormalising

open import 1Lab.Prelude

open import Data.Rel.Base
open import Data.Rel.Closure
open import Data.Sum
open import Data.Wellfounded.Base


open import Rewriting.Base
open import Rewriting.Commute
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
  R S : A → A → Type ℓ

open Normal-form
```
-->

Recall that [rewriting systems] may be non-deterministic, as multiple
rewrite rules can apply to a term $t$. This means that multiple
strategies of applying the rules may lead to different answers, which is
quite problematic if we want to use the rewriting system to simplify
expressions. It would be useful if we could prove *some* property of the
relation that would guarantee that this situation does not occur.

[rewriting systems]: Rewriting.Base.html

This leads us to the notion of **confluence**. We say a relation $\to$
is confluent if for all pairs of reduction chains $a \to^{*} x$
and $a \to^{*} y$, there exists some $z$ such that $x \to^{*} z$
and $y \to^{*} z$, as in the following diagram.

~~~{.quiver}
\begin{tikzcd}
  a && y \\
  \\
  x && {\exists z}
  \arrow["{*}"{description}, from=1-1, to=3-1]
  \arrow["{*}"{description}, dashed, from=3-1, to=3-3]
  \arrow["{*}"{description}, dashed, from=1-3, to=3-3]
  \arrow["{*}"{description}, from=1-1, to=1-3]
\end{tikzcd}
~~~

```agda
is-confluent : (A → A → Type ℓ) → Type _
is-confluent {A = A} R =
  commutes-with R R
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

Before getting into the more complicated properties of confluence,
we should get some minor lemmas out of the way. First, if $R^{*}$
is equivalent to $S^{*}$ and $R^{*}$ is confluent, then so is $S^{*}$.
This follows directly from properties of resolutions.

```agda
refl-trans-clo-equiv+confluent→confluent
  : Refl-trans R ≃r Refl-trans S
  → is-confluent R → is-confluent S
refl-trans-clo-equiv+confluent→confluent eqv R-conf {x} {y} {z} =
  resolvable-⊆
    (Equiv.from (eqv {x} {y})) (Equiv.from (eqv {x} {z}))
    (Equiv.to eqv) (Equiv.to eqv)
    R-conf {x} {y} {z}
```

If a rewrite system on a set is confluent, then every element of $A$
has at most one normal form.

To show this, assume that $y$ and $z$ are both normal forms of $x$.
This gives us the following fork:

~~~{.quiver}
\begin{tikzcd}
  & x \\
  y && z
  \arrow["{*}"', from=1-2, to=2-1]
  \arrow["{*}", from=1-2, to=2-3]
\end{tikzcd}
~~~

We can apply confluence to obtain a wedge $y \to^{*} w \leftarrow^{*} z$.

~~~{.quiver}
\begin{tikzcd}
  & x \\
  y && z \\
  & w
  \arrow["{*}"', from=1-2, to=2-1]
  \arrow["{*}", from=1-2, to=2-3]
  \arrow["{*}"', from=2-1, to=3-2]
  \arrow["{*}", from=2-3, to=3-2]
  \arrow["Conf"{description}, color={rgb,255:red,92;green,92;blue,214}, draw=none, from=1-2, to=3-2]
\end{tikzcd}
~~~

Both $y$ and $z$ are normal forms, so this gives us a pair of paths $y = w$ and
$z = w$, which completes the proof.

```agda
confluent→unique-normal-forms
  : ∀ {R : Rel A A ℓ}
  → is-set A
  → is-confluent R 
  → ∀ x → is-prop (Normal-form R x)
confluent→unique-normal-forms {R = R} A-set conf x y-nf z-nf =
  ∥-∥-rec (Normal-form-is-hlevel 0 A-set y-nf z-nf)
    (λ where
      (w , y↝w , z↝w) →
        Normal-form-path y-nf z-nf
          (normal-forms+wedge→path A-set
            (y-nf .has-normal-form) (z-nf .has-normal-form)
            y↝w z↝w))
    (conf (y-nf .reduces) (z-nf .reduces))
```

<!--
```agda
-- Useful for local instances.
H-Level-confluent-normal-form
  : ∀ {R : Rel A A ℓ} {x} {n}
  → is-set A
  → is-confluent R
  → H-Level (Normal-form R x) (suc n)
H-Level-confluent-normal-form set conf =
  prop-instance (confluent→unique-normal-forms set conf _)
```
-->

If $\to$ is a confluent relation and $x \to^{*} w \leftarrow^{*} y$,
then $y$ has a normal form if and only if $x$ does.

To see this, note that we have the following pair of reductions
out of $x$:

~~~{.quiver}
\begin{tikzcd}
        x && w && y \\
        \\
        {x \downarrow}
        \arrow["{*}", from=1-1, to=1-3]
        \arrow["{*}"', from=1-1, to=3-1]
        \arrow["{*}"', from=1-5, to=1-3]
\end{tikzcd}
~~~

We can use confluence to fill in the left-hand square:

~~~{.quiver}
\begin{tikzcd}
  x && w && y \\
  \\
  {x \downarrow} && {w'}
  \arrow["{*}", from=1-1, to=1-3]
  \arrow["{*}"', from=1-1, to=3-1]
  \arrow["{*}"', from=1-5, to=1-3]
  \arrow[from=1-3, to=3-3]
  \arrow[from=3-1, to=3-3]
  \arrow["Conf"{description}, color={rgb,255:red,92;green,92;blue,214}, draw=none, from=1-1, to=3-3]
\end{tikzcd}
~~~

Note that $x \downarrow$ and $y$ both reduce to the same value; this
means that $y$ reduces to $x \downarrow$, as $x \downarrow$ is a normal
form.

```agda
confluent+wedge+normal-form→normal-form
  : ∀ {x y w}
  → is-confluent R
  → Refl-trans R x w → Refl-trans R y w
  → Normal-form R x → Normal-form R y
confluent+wedge+normal-form→normal-form conf x↝w y↝w x↓ .nf =
  x↓ .nf
confluent+wedge+normal-form→normal-form conf x↝w y↝w x↓ .reduces =
  ∥-∥-rec!
    (λ where
      (w' , x↓↝w' , w↝w') →
        normal-form+reduces→reduces (x↓ .has-normal-form)
          x↓↝w' (transitive y↝w w↝w'))
    (conf (x↓ .reduces) x↝w)
confluent+wedge+normal-form→normal-form conf x↝w y↝w x↓ .has-normal-form =
  x↓ .has-normal-form
```

## The Church-Rosser Property

A rewriting system $\to$ yields an equivalence relation on terms via
the [reflexive symmetric transitive closure] of $\to$. This leads to
a variant of confluence known as the **Church-Rosser Property**, which
requires a $z$ for every pair of equivalent terms $x$ and $y$ such that
$x \to^{*} z$ and $y \to^{*} z$.

[reflexive symmetric transitive closure]: Data.Rel.Closure.ReflexiveSymmetricTransitive.html

~~~{.quiver}
\begin{tikzcd}
  x && y \\
  & z
  \arrow["{*}"{description}, dashed, from=1-1, to=2-2]
  \arrow["{*}"{description}, dashed, from=1-3, to=2-2]
  \arrow["{*}"{description}, tail reversed, from=1-1, to=1-3]
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
  \arrow["{*}"{description}, from=3-1, to=1-1]
  \arrow["{*}"{description}', dashed, from=3-1, to=3-3]
  \arrow["{*}"{description}, dashed, from=1-3, to=3-3]
  \arrow["{*}"{description}, from=1-3, to=1-1]
\end{tikzcd}
~~~

Somewhat surprisingly, it turns out that the two conditions are equivalent!
Showing that Church-Rosser implies confluence is rather easy: if we
have two reduction sequences $a \to^{*} x$ and $a \to^{*} y$,
we can invert one side to get an equivalence in the reflexive symmetric
transitive closure, and then invoke Church-Rosser to get the desired
pair of reductions.

```agda
church-rosser→confluent : has-church-rosser R → is-confluent R
church-rosser→confluent church-rosser a→*x a→*y =
  church-rosser $
    transitive
      (symmetric (refl-trans⊆refl-sym-trans a→*x))
      (refl-trans⊆refl-sym-trans a→*y)
```

The converse is much more tricky, and requires introducing an intermediate
notion of **semi-confluence**, which yields solutions to diamonds of the
following form.

~~~{.quiver}
\begin{tikzcd}
  a && y \\
  \\
  x && {\exists z}
  \arrow["{*}"{description}, from=1-1, to=3-1]
  \arrow["{*}"{description}', dashed, from=3-1, to=3-3]
  \arrow["{*}"{description}, dashed, from=1-3, to=3-3]
  \arrow[from=1-1, to=1-3]
\end{tikzcd}
~~~

```agda
is-semi-confluent : (A → A → Type ℓ) → Type _
is-semi-confluent {A = A} R =
  semi-commutes-with R R
```

Confluence obviously implies semi-confluence.

```agda
confluent→semiconfluent : is-confluent R → is-semi-confluent R
confluent→semiconfluent conf a→*x a→y = conf a→*x [ a→y ]
```

Furthermore, semi-confluence implies Church-Rosser. Let $\to$ be a
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
  w && v && v
  \arrow["{*}"{description}, from=1-5, to=3-5]
  \arrow["{*}"{description}, from=1-7, to=3-5]
  \arrow["{*}"{description}, tail reversed, from=1-5, to=1-7]
  \arrow[from=1-3, to=1-5]
  \arrow[from=1-3, to=1-1]
  \arrow["{*}"{description}, from=1-3, to=3-3]
  \arrow["{*}"{description}, from=3-5, to=3-3]
  \arrow["{*}"{description}, from=3-3, to=3-1]
  \arrow["{*}"{description}, from=1-1, to=3-1]
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

This theorem has some very useful consequences; first, if $R$ is
confluent and $x$ and $y$ are convertible, then $x$ reduces to $y$
if $y$ is in normal form.

To see this, note that Church-rosser implies that gives us a $w$ such
that $x \to^{*} w$ and $y \to^{*} w$. We can then perform induction
on the $y \to^{*} w$; if it is empty, then we have $y = w$, and thus
$x \to^{*} y$. If it is non-empty, then we have a contradiction, as
$y$ is a normal form.

```agda
confluent+convertible→reduces-to-normal-form
  : ∀ {x y}
  → is-confluent R
  → Refl-sym-trans R x y
  → is-normal-form R y
  → Refl-trans R x y
confluent+convertible→reduces-to-normal-form {R = R} {x = x} {y = y} conf x↔y y-nf =
  ∥-∥-rec!
    (λ where
      (w , x↝w , y↝w) →
        Refl-trans-rec-chain
          (λ y w → is-normal-form R y → Refl-trans R x w → Refl-trans R x y)
          (λ _ x↝y → x↝y)
          (λ y↝z _ _ y-nf _ → absurd (y-nf (_ , y↝z)))
          hlevel!
          y↝w y-nf x↝w)
    (confluent→church-rosser conf x↔y)
```

Furthermore, if $R$ is a confluent relation on a set, and $x y : A$
are convertible normal forms, then $x = y$. This follows from
`normal-forms+wedge→path`{.Agda} and confluence.

```agda
confluent+convertible→unique-normal-form
  : ∀ {R : Rel A A ℓ} {x y}
  → is-set A
  → is-confluent R
  → Refl-sym-trans R x y
  → is-normal-form R x → is-normal-form R y
  → x ≡ y
confluent+convertible→unique-normal-form set conf x↔y x-nf y-nf =
  ∥-∥-rec (set _ _)
    (λ where
      (w , x↝w , y↝w) →
        normal-forms+wedge→path set x-nf y-nf x↝w y↝w)
    (confluent→church-rosser conf x↔y)
```

We can also show that if $R$ is a confluent relation on a set, and
$x$ and $y$ are convertible, then the their types of normal forms are
equivalent.

```agda
confluent+convertible→normal-form-equiv
  : ∀ {R : Rel A A ℓ} {x y}
  → is-set A
  → is-confluent R
  → Refl-sym-trans R x y
  → Normal-form R x ≃ Normal-form R y
confluent+convertible→normal-form-equiv {R = R} {x = x} {y = y} set conf x↔y =
  ∥-∥-rec!
    (λ where
      (w , x↝w , y↝w) →
        prop-ext!
          (confluent+wedge+normal-form→normal-form conf x↝w y↝w)
          (confluent+wedge+normal-form→normal-form conf y↝w x↝w))
    (confluent→church-rosser conf x↔y)
  where
    instance
      _ : ∀ {x} {n} → H-Level (Normal-form R x) (suc n)
      _ = H-Level-confluent-normal-form set conf
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

~~~{.quiver .tall-2}
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

~~~{.quiver .tall-2}
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

~~~{.quiver .tall-2}
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
\end{tikzcd}
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

## The Commutative Union Lemma

Confluence proofs can be very fiddly, so it would be useful to be able to
modularise the proofs somewhat. Ideally, we would be able to split
a rewriting system $R$ into a union $S \cup T$, and then prove confluence
of $S$ and $T$ separately. This approach is too naïve, but can be repaired
by requiring that $S$ and $T$ [commute].

[commute]: Rewriting.Commute.html

The proof of this fact requires some machinery. We say that a rewrite
system is **strongly confluent** if we can resolve squares of shape (1),
and that it has the **diamond property** if we can resolve squares of shape
(2).

~~~{.quiver}
\begin{tikzcd}
  & x &&&& x \\
  y && z && y && z \\
  & {\exists w} &&&& {\exists w} \\
  & {(1)} &&&& {(2)}
  \arrow[from=1-2, to=2-1]
  \arrow[from=1-2, to=2-3]
  \arrow[dashed, from=2-5, to=3-6]
  \arrow[dashed, from=2-7, to=3-6]
  \arrow[from=1-6, to=2-5]
  \arrow[from=1-6, to=2-7]
  \arrow["{*}", dashed, from=2-3, to=3-2]
  \arrow["{=}"', dashed, from=2-1, to=3-2]
\end{tikzcd}
~~~

```agda
has-diamond : (R : Rel A A ℓ) → Type _
has-diamond R = is-resolvable R R R R

is-strongly-confluent : (R : Rel A A ℓ) → Type _
is-strongly-confluent R = strongly-commutes-with R R
```

The diamond property implies strong confluence, which in turn implies
confluence.

```agda
diamond→strongly-confluent : has-diamond R → is-strongly-confluent R
diamond→strongly-confluent diamond x↝y x↝z = do
  w , y↝w , x↝w ← diamond x↝y x↝z
  pure (w , [ y↝w ] , [ x↝w ])

strongly-confluent→confluent : is-strongly-confluent R → is-confluent R
strongly-confluent→confluent = strongly-commutes→commutes

diamond→confluent : has-diamond R → is-confluent R
diamond→confluent = strongly-confluent→confluent ∘ diamond→strongly-confluent
```

With that bit of machinery out of the way, we can proceed with the
proof.  Recall that if the reflexive-transitive closures of two
relations are equivalent, then we can transfer confluence across the
equivalence. Furthermore, the reflexive transitive-closure of $R \cup S$
is equivalent to the reflexive-transitive closure of $S^{*} \circ
R^{*}$, so it suffices to show that $S^{*} \circ R^{*}$ is confluent.

We shall do so by establishing that $S^{*} \circ R^{*}$ has the diamond
property. Doing so requires filling the following diagram:

~~~{.quiver}
\begin{tikzcd}
  x & {z'} & z \\
  {y'} && \bullet \\
  y & \bullet & \bullet
  \arrow["{R^{*}}"', from=1-1, to=2-1]
  \arrow["{S^{*}}"', from=2-1, to=3-1]
  \arrow["{R^{*}}", from=1-1, to=1-2]
  \arrow["{S^{*}}", from=1-2, to=1-3]
  \arrow["{R^{*}}"', dashed, from=3-1, to=3-2]
  \arrow["{S^{*}}"', dashed, from=3-2, to=3-3]
  \arrow["{R^{*}}", dashed, from=1-3, to=2-3]
  \arrow["{S^{*}}", dashed, from=2-3, to=3-3]
\end{tikzcd}
~~~

We can use confluence of $R^{*}$ to fill in the upper-left square.

~~~{.quiver}
\begin{tikzcd}
  x & {z'} & z \\
  {y'} & a & \bullet \\
  y & \bullet & \bullet
  \arrow["{R^{*}}"', from=1-1, to=2-1]
  \arrow["{S^{*}}"', from=2-1, to=3-1]
  \arrow["{R^{*}}", from=1-1, to=1-2]
  \arrow["{S^{*}}", from=1-2, to=1-3]
  \arrow["{R^{*}}"', dashed, from=3-1, to=3-2]
  \arrow["{S^{*}}"', dashed, from=3-2, to=3-3]
  \arrow["{R^{*}}", dashed, from=1-3, to=2-3]
  \arrow["{S^{*}}", dashed, from=2-3, to=3-3]
  \arrow["{R^{*}}"', from=2-1, to=2-2]
  \arrow["{R^{*}}", from=1-2, to=2-2]
  \arrow["Conf"{description}, color={rgb,255:red,92;green,92;blue,214}, draw=none, from=1-1, to=2-2]
\end{tikzcd}
~~~

We can then use commutativity of $R$ and $S$ to fill in the upper-right
and lower-left squares.

~~~{.quiver}
\begin{tikzcd}
  x & {z'} & z \\
  {y'} & a & c \\
  y & b & \bullet
  \arrow["{R^{*}}"', from=1-1, to=2-1]
  \arrow["{S^{*}}"', from=2-1, to=3-1]
  \arrow["{R^{*}}", from=1-1, to=1-2]
  \arrow["{S^{*}}", from=1-2, to=1-3]
  \arrow["{R^{*}}"', from=3-1, to=3-2]
  \arrow["{S^{*}}"', dashed, from=3-2, to=3-3]
  \arrow["{R^{*}}", from=1-3, to=2-3]
  \arrow["{S^{*}}", dashed, from=2-3, to=3-3]
  \arrow["{R^{*}}", from=2-1, to=2-2]
  \arrow["{R^{*}}"', from=1-2, to=2-2]
  \arrow["{S^{*}}", from=2-2, to=3-2]
  \arrow["{S^{*}}"', from=2-2, to=2-3]
  \arrow["Comm"{description}, color={rgb,255:red,92;green,92;blue,214}, draw=none, from=2-1, to=3-2]
  \arrow["Comm"{description}, color={rgb,255:red,92;green,92;blue,214}, draw=none, from=1-2, to=2-3]
\end{tikzcd}
~~~

Finally, we can use confluence of $S$ to fill in the lower-right square,
finishing the proof.

~~~{.quiver}
\begin{tikzcd}
  x & {z'} & z \\
  {y'} & a & c \\
  y & b & w
  \arrow["{R^{*}}"', from=1-1, to=2-1]
  \arrow["{S^{*}}"', from=2-1, to=3-1]
  \arrow["{R^{*}}", from=1-1, to=1-2]
  \arrow["{S^{*}}", from=1-2, to=1-3]
  \arrow["{R^{*}}"', from=3-1, to=3-2]
  \arrow["{S^{*}}"', from=3-2, to=3-3]
  \arrow["{R^{*}}", from=1-3, to=2-3]
  \arrow["{S^{*}}", from=2-3, to=3-3]
  \arrow["{R^{*}}", from=2-1, to=2-2]
  \arrow["{R^{*}}"', from=1-2, to=2-2]
  \arrow["{S^{*}}"', from=2-2, to=3-2]
  \arrow["{S^{*}}", from=2-2, to=2-3]
  \arrow["Conf"{description}, color={rgb,255:red,92;green,92;blue,214}, draw=none, from=2-2, to=3-3]
\end{tikzcd}
~~~

```agda
commutes+confluent→union-confluent
  : commutes-with R S
  → is-confluent R → is-confluent S
  → is-confluent (R ∪r S)
commutes+confluent→union-confluent {R = R} {S = S} comm R-conf S-conf =
  refl-trans-clo-equiv+confluent→confluent
    refl-trans-clo-union≃refl-trans-clo-comp-refl-trans-clo
    (diamond→confluent S*∘R*-diamond)
  where
    S*∘R*-diamond : has-diamond (Refl-trans S ∘r Refl-trans R)
    S*∘R*-diamond {x} {y} {z} x↝*y x↝*z = do
      y' , x↝₁y' , y'↝₂y ← x↝*y
      z' , x↝₁z' , z'↝₂z ← x↝*z
      a , y'↝₁a , z'↝₁a ← R-conf x↝₁y' x↝₁z'
      b , a↝₂b , y↝₁b ← comm y'↝₁a y'↝₂y
      c , a↝₂c , z↝₁c ← comm z'↝₁a z'↝₂z
      w , b↝₂w , c↝₂w ← S-conf a↝₂b a↝₂c
      pure (w , pure (b , y↝₁b , b↝₂w) , pure (c , z↝₁c , c↝₂w))
```
