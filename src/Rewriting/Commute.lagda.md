<!--
```agda
open import 1Lab.Prelude
open import Data.Rel.Base
open import Data.Rel.Closure

open import Rewriting.Base
```
-->

```agda
module Rewriting.Commute where
```

<!--
```agda
private variable
  ℓ ℓ' ℓ'' : Level
  A B X : Type ℓ
  R S _↝₁_ _↝₂_ : Rel A A ℓ
```
-->

# Commuting Rewrite Systems

Let $R$ and $S$ be a pair of [abstract rewrite systems] on a
type $A$. We say that $R$ **commutes** with $S$ if $R^{*}$ and
$S^{*}$ are resolvable by $S^{*}$ and $R^{*}$, as in the following
diagram.

[abstract rewrite systems]: Rewriting.Base.html

~~~{.quiver}
\begin{tikzcd}
  & x \\
  y && z \\
  & {\exists w}
  \arrow["{S^*}"', dashed, from=2-1, to=3-2]
  \arrow["{R^*}", dashed, from=2-3, to=3-2]
  \arrow["{R^*}"', from=1-2, to=2-1]
  \arrow["{S^*}", from=1-2, to=2-3]
\end{tikzcd}
~~~

```agda
commutes-with : (R : Rel A A ℓ) → (S : Rel A A ℓ') → Type _
commutes-with R S =
  is-resolvable
    (Refl-trans R) (Refl-trans S)
    (Refl-trans S) (Refl-trans R)
```

Intuitively, this condition ensures that applying a sequences of rewrites
from $R$ and $S$ don't let us diverge; we can always reconcile the two
by performing rewrites from $S$ and $R$, resp. This generalizes
[confluence], which states that a relation commutes with itself.

[confluence]: Rewriting.Confluent.html

This condition can be somewhat difficult to work with, so we introduce
an intermediate notion of **semi-commutation**, where one of the reflexive
transitive closures has been removed.

~~~{.quiver}
\begin{tikzcd}
  & x \\
  y && z \\
  & {\exists w}
  \arrow["{S^*}"', dashed, from=2-1, to=3-2]
  \arrow["{R^*}", dashed, from=2-3, to=3-2]
  \arrow["{R^*}"', from=1-2, to=2-1]
  \arrow["S", from=1-2, to=2-3]
\end{tikzcd}
~~~

```agda
semi-commutes-with : (R : Rel A A ℓ) → (S : Rel A A ℓ') → Type _
semi-commutes-with R S =
  is-resolvable
    (Refl-trans R) S
    (Refl-trans S) (Refl-trans R)
```

Commutativity obviously implies semi-commutativity.

```agda
commutes→semi-commutes : commutes-with R S → semi-commutes-with R S
commutes→semi-commutes comm x↝₁*y1 x↝₂y2 =
  comm x↝₁*y1 [ x↝₂y2 ]
```

Furthermore, semi-commutativity implies commutativity. We begin with
the following situation:

~~~{.quiver}
\begin{tikzcd}
  x && {y_2} \\
  \\
  {y_1} && \bullet
  \arrow["{R^*}"', from=1-1, to=3-1]
  \arrow["S", from=1-1, to=1-3]
  \arrow[dashed, from=3-1, to=3-3]
  \arrow[dashed, from=1-3, to=3-3]
\end{tikzcd}
~~~

We then proceed by induction on the $S^*$. If it is an empty sequence of
rewrites, then we are done. If it is non-empty, then we have the following
situation:

~~~{.quiver}
\begin{tikzcd}
  x && {y_2'} && {y_2} \\
  \\
  {y_1} &&&& \bullet
  \arrow["{R^*}"', from=1-1, to=3-1]
  \arrow["S", from=1-1, to=1-3]
  \arrow["{S^*}", from=1-3, to=1-5]
  \arrow[dashed, from=1-5, to=3-5]
  \arrow[dashed, from=3-1, to=3-5]
\end{tikzcd}
~~~

We can apply semi-commutativity to fill in the left-hand square, as
in the following diagram.

~~~{.quiver}
\begin{tikzcd}
  x && {y_2'} && {y_2} \\
  \\
  {y_1} && {z'} && \bullet
  \arrow["{R^*}"', from=1-1, to=3-1]
  \arrow["S", from=1-1, to=1-3]
  \arrow[dashed, from=1-5, to=3-5]
  \arrow["{S^*}", from=1-3, to=1-5]
  \arrow["{S^*}"', from=3-1, to=3-3]
  \arrow["{R^*}", from=1-3, to=3-3]
  \arrow["{S.C.}"{description}, color={rgb,255:red,92;green,92;blue,214}, draw=none, from=1-1, to=3-3]
  \arrow[dashed, from=3-3, to=3-5]
\end{tikzcd}
~~~

Finally, we can use our induction hypothesis to fill in the right-hand
square, completing the proof.

~~~{.quiver}
\begin{tikzcd}
  x && {y_2'} && {y_2} \\
  \\
  {y_1} && {z'} && z
  \arrow["{R^*}"', from=1-1, to=3-1]
  \arrow["S", from=1-1, to=1-3]
  \arrow["{R^*}", from=1-5, to=3-5]
  \arrow["{S^*}", from=1-3, to=1-5]
  \arrow["{S^*}"', from=3-1, to=3-3]
  \arrow["{R^*}", from=1-3, to=3-3]
  \arrow["{S.C.}"{description}, color={rgb,255:red,92;green,92;blue,214}, draw=none, from=1-1, to=3-3]
  \arrow["{S^*}"', from=3-3, to=3-5]
  \arrow["{I.H.}"{description}, color={rgb,255:red,92;green,92;blue,214}, draw=none, from=1-3, to=3-5]
\end{tikzcd}
~~~

```agda
semi-commutes→commutes : semi-commutes-with R S → commutes-with R S
semi-commutes→commutes {R = R} {S = S}  semi-comm x↝₁*y1 x↝₂*y2 =
  Refl-trans-rec-chain
    (λ x y2 →
      ∀ y1 → Refl-trans R x y1
      → is-joinable (Refl-trans S) (Refl-trans R) y1 y2)
    (λ y1 x↝₁*y1 → pure (y1 , reflexive , x↝₁*y1))
    (λ {x} {y2'} {y2} x↝₂y2' y2'↝₂*y2 ih y1 x↝₁*y1 → do
      z' , y1↝₂*z' , y2'↝₁*z' ← semi-comm x↝₁*y1 x↝₂y2'
      z , z'↝₂*z , y2↝₁*z ← ih z' y2'↝₁*z'
      pure (z , transitive y1↝₂*z' z'↝₂*z , y2↝₁*z))
    hlevel!
    x↝₂*y2 _ x↝₁*y1
```

## Strong Commutativity

Semi-commutativity is a useful notion when performing purely
rewrite-theoretic proofs, but it is still difficult to show, as it
is a global property rather than a local one. For this reason, we
introduce the notion of **strong commutativity**, which allows us
to resolve diamonds of the following form:

~~~{.quiver}
\begin{tikzcd}
  & x \\
  y && z \\
  & {\exists w}
  \arrow["R"', from=1-2, to=2-1]
  \arrow["{S^{=}}"', dashed, from=2-1, to=3-2]
  \arrow["{R^{*}}", dashed, from=2-3, to=3-2]
  \arrow["S", from=1-2, to=2-3]
\end{tikzcd}
~~~

```agda
strongly-commutes-with : (R : Rel A A ℓ) → (S : Rel A A ℓ') → Type _
strongly-commutes-with R S =
  is-resolvable
    R S
    (Refl S) (Refl-trans R)
```

This property is generally easier to show, as it only involves resolving
one reduction step on either side, instead of an arbitrarily long chain.

As the name suggests, strong commutativity is a stronger condition
than commutativity. We will prove this by showing that strong
commutativity implies semi-commutativity.

Recall that semi-commutativity involves resolving a diagram of the
following shape:

~~~{.quiver}
\begin{tikzcd}
  x && {y_2} \\
  \\
  {y_1} && \bullet
  \arrow["{R^{*}}"', from=1-1, to=3-1]
  \arrow["{S^{=}}"', dashed, from=3-1, to=3-3]
  \arrow["{R^{*}}", dashed, from=1-3, to=3-3]
  \arrow["S", from=1-1, to=1-3]
\end{tikzcd}
~~~

We proceed by induction on the $R^{*}$; if it is an empty path, then
we are done. If it is non-empty, then we have the following situation:

~~~{.quiver}
\begin{tikzcd}
  x && {y_2} \\
  \\
  {y_1'} \\
  \\
  {y_1} && \bullet
  \arrow["R"', from=1-1, to=3-1]
  \arrow["{R^{*}}", dashed, from=1-3, to=5-3]
  \arrow["S", from=1-1, to=1-3]
  \arrow["{R^{*}}"', from=3-1, to=5-1]
  \arrow[dashed, from=5-1, to=5-3]
\end{tikzcd}
~~~

We can then apply strong commutativity to fill the upper square.

~~~{.quiver}
\begin{tikzcd}
  x && {y_2} \\
  \\
  {y_1'} && {z'} \\
  \\
  {y_1} && \bullet
  \arrow["R"', from=1-1, to=3-1]
  \arrow["S", from=1-1, to=1-3]
  \arrow["{R^{*}}"', from=3-1, to=5-1]
  \arrow["{R{*}}", from=1-3, to=3-3]
  \arrow["{S^{=}}"', from=3-1, to=3-3]
  \arrow[dashed, from=3-3, to=5-3]
  \arrow[dashed, from=5-1, to=5-3]
  \arrow["{S.C.}"{description}, color={rgb,255:red,92;green,92;blue,214}, draw=none, from=1-1, to=3-3]
\end{tikzcd}
~~~

We now perform induction on the $S^{=}$. If it is the reflexive path,
then we have the following situation:

~~~{.quiver}
\begin{tikzcd}
  x && {y_2} \\
  \\
  {y_1'} \\
  \\
  {y_1}
  \arrow["R"', from=1-1, to=3-1]
  \arrow["S", from=1-1, to=1-3]
  \arrow["{R^{*}}"', from=3-1, to=5-1]
  \arrow["{R^{*}}", from=1-3, to=3-1]
\end{tikzcd}
~~~

Thus, we can use $y_1$ as our resolution.

If the $S^{=}$ is not the empty path, then we have the following
diagram:

~~~{.quiver}
\begin{tikzcd}
  x && {y_2} \\
  \\
  {y_1'} && {z'} \\
  \\
  {y_1} && \bullet
  \arrow["R"', from=1-1, to=3-1]
  \arrow["S", from=1-1, to=1-3]
  \arrow["{R^{*}}"', from=3-1, to=5-1]
  \arrow[dashed, from=5-1, to=5-3]
  \arrow["{R{*}}", from=1-3, to=3-3]
  \arrow["S"', from=3-1, to=3-3]
  \arrow[dashed, from=3-3, to=5-3]
  \arrow["{S.C.}"{description}, color={rgb,255:red,92;green,92;blue,214}, draw=none, from=1-1, to=3-3]
\end{tikzcd}
~~~

We can use our induction hypothesis to fill in the lower square,
completing the proof.

~~~{.quiver}
\begin{tikzcd}
  x && {y_2} \\
  \\
  {y_1'} && {z'} \\
  \\
  {y_1} && \bullet
  \arrow["R"', from=1-1, to=3-1]
  \arrow["S", from=1-1, to=1-3]
  \arrow["{R^{*}}"', from=3-1, to=5-1]
  \arrow["{S^{*}}"', from=5-1, to=5-3]
  \arrow["{R{*}}", from=1-3, to=3-3]
  \arrow["S"', from=3-1, to=3-3]
  \arrow["{R^{*}}", from=3-3, to=5-3]
  \arrow["{S.C.}"{description}, color={rgb,255:red,92;green,92;blue,214}, draw=none, from=1-1, to=3-3]
  \arrow["{I.H}"{description}, color={rgb,255:red,92;green,92;blue,214}, draw=none, from=3-1, to=5-3]
\end{tikzcd}
~~~

```agda
strongly-commutes→semi-commutes
  : strongly-commutes-with R S → semi-commutes-with R S
strongly-commutes→semi-commutes {R = R} {S = S} strong-comm x↝₁*y1 x↝₂y2 =
  Refl-trans-rec-chain
    (λ x y1 → ∀ y2 → S x y2 → is-joinable (Refl-trans S) (Refl-trans R) y1 y2)
    (λ {x} y2 x↝₂y2 → pure (y2 , [ x↝₂y2 ] , reflexive))
    (λ {x} {y1'} {y1} x↝₁y1' y1'↝₁*y1 ih y2 x↝₂y2 → do
      z' , y1'↝₂=z , y2↝₁*z ← strong-comm x↝₁y1' x↝₂y2
      Refl-rec
       (λ y1' z'
         → Refl-trans R y2 z' → Refl-trans R y1' y1
         → (∀ y2 → S y1' y2 → is-joinable (Refl-trans S) (Refl-trans R) y1 y2)
         → is-joinable (Refl-trans S) (Refl-trans R) y1 y2)
        (λ {y1'} {z'} y1'↝₂z y2↝₁*z' y1'↝₁*y1 ih → do
          z , y1↝₂*z , z'↝₁*z ← ih z' y1'↝₂z
          pure (z , y1↝₂*z , transitive y2↝₁*z' z'↝₁*z))
       (λ y1' y2↝₁*y1' y1'↝₁*y1 _ →
         pure (y1 , reflexive , transitive y2↝₁*y1' y1'↝₁*y1))
       hlevel!
       y1'↝₂=z y2↝₁*z y1'↝₁*y1 ih)
    hlevel!
    x↝₁*y1 _ x↝₂y2
```

Strong commutativity implies commutativity, as semi-commutativity
is equivalent to commutativity.

```agda
strongly-commutes→commutes
  : strongly-commutes-with R S → commutes-with R S
strongly-commutes→commutes strong-comm =
  semi-commutes→commutes $ strongly-commutes→semi-commutes strong-comm
```
