<!--
```agda
open import Cat.Instances.Sets
open import Cat.Functor.Base
open import Cat.Prelude

open import Order.Morphism
open import Order.Base

import Cat.Reasoning
```
-->

```agda
module Order.Univalent where
```

# Univalence of the category of Posets

This module proves that the category of [[posets]] is actually
[[univalent|univalent category]]. As usual, we begin by constructing a
function that constructs an identification from an isomorphism; this is
the most tedious part of the argument.

```agda
Poset-path : ∀ {o ℓ} {P Q : Poset o ℓ} → P Posets.≅ Q → P ≡ Q
Poset-path {P = P} {Q} f = path where
```

<!--
```agda
  module P = Poset P
  module Q = Poset Q
  open Posets
```
-->

Since the `forgetful functor`{.Agda ident=Forget-poset} maps
isomorphisms of posets onto isomorphisms of their underlying sets, the
first thing to observe is that an isomorphism of posets has an
underlying equivalence of types, from which we can construct a path, by
univalence.

```agda
  P≃Q : ⌞ P ⌟ ≃ ⌞ Q ⌟
  P≃Q = iso→equiv (F-map-iso Forget-poset f)

  ob : ∀ i → Type _
  ob i = ua P≃Q i
```

That handles the first field of the record `Poset`{.Agda}. The next
thing to consider is the order relation. We're looking for a term of the
following type:

```agda
  order : PathP (λ i → ob i → ob i → Type _) P._≤_ Q._≤_
```

That is, an identification between the order relations, which is
displayed over the identification between underlying sets we just
constructed. We do this by an explicit cubical construction. It will
suffice to construct a term

$$
i : \bI, x : \rm{ob}(i), y : \rm{ob}(i) \vdash \rm{order}_i(x,y) : \ty
$$

which reduces to $x \le_P y$ when $i = i0$ (resp. $x \le_Q y$ when $i =
i1$). We begin by observing that, since $x, y$ are inhabitants of a
[[Glue type]], we can `unglue`{.Agda} them to obtain values $qx, qy :
Q$. Moreover, these unglued values reduce to $f(x)$ on $i = i0$ and $x$
on $i = i1$. We can arrange the data at hand and the data we want as the
top and bottom faces in a square:

~~~{.quiver .short-05}
\[\begin{tikzcd}[ampersand replacement=\&]
  {x \le_P y} \&\& {x\le_Q y} \\
  \\
  {f(x) \le_Q f(y)} \&\& {x \le_Q y}
  \arrow[dashed, from=1-1, to=1-3]
  \arrow["{qx \le_Q qy}"', from=3-1, to=3-3]
\end{tikzcd}\]
~~~

We can then obtain the dashed face --- as well as the full square ---
again using a [[Glue type]], as long as we can fill the missing faces by
equivalences. And since the missing left-hand-side is precisely the
statement "$f$ is an order-embedding", we can:

```agda
  order i x y = Glue (unglue (∂ i) x Q.≤ unglue (∂ i) y) λ where
    (i = i0) → x P.≤ y , order-iso-is-order-embedding f
    (i = i1) → x Q.≤ y , _ , id-equiv
```

The definition above corresponds to the top face in the square

~~~{.quiver .short-05}
\[\begin{tikzcd}[ampersand replacement=\&]
  {x \le_P y} \&\& {x\le_Q y} \\
  \\
  {f(x) \le_Q f(y)} \&\& {x \le_Q y}
  \arrow[dashed, from=1-1, to=1-3]
  \arrow["{qx \le_Q qy}"', from=3-1, to=3-3]
  \arrow["\sim"', sloped, from=1-1, to=3-1]
  \arrow[Rightarrow, no head, from=1-3, to=3-3]
\end{tikzcd}\]
~~~

<!--
```agda
  order-thin : ∀ i x y → is-prop (order i x y)
  order-thin i = coe0→i (λ i → (x y : ob i) → is-prop (order i x y)) i hlevel!

  ob-set : ∀ i → is-set (ob i)
  ob-set i = coe0→i (λ i → is-set (ob i)) i hlevel!
```
-->

```agda
  path : P ≡ Q
  path i .Poset.Ob      = ob i
  path i .Poset._≤_ x y = order i x y
```

<details>
<summary>
That handles the fields with actual content. All the proposition-valued
fields are entirely formulaic applications of `is-prop→pathp`{.Agda}, so
we omit them from the page for space.
</summary>

```agda
  path i .Poset.≤-thin {x} {y} =
    is-prop→pathp
      (λ i →
        Π-is-hlevel² {A = ob i} {B = λ _ → ob i} 1 λ x y →
        is-prop-is-prop {A = order i x y})
      (λ _ _ → P.≤-thin)
      (λ _ _ → Q.≤-thin) i x y
  path i .Poset.≤-refl {x = x} =
    is-prop→pathp
      (λ i → Π-is-hlevel {A = ob i} 1 λ x → order-thin i x x)
        (λ _ → P.≤-refl)
        (λ _ → Q.≤-refl) i x
  path i .Poset.≤-trans {x} {y} {z} x≤y y≤z =
    is-prop→pathp
      (λ i →
        Π-is-hlevel³ {A = ob i} {B = λ _ → ob i} {C = λ _ _ → ob i} 1 λ x y z →
        Π-is-hlevel² {A = order i x y} {B = λ _ → order i y z} 1 λ _ _ →
        order-thin i x z)
      (λ _ _ _ → P.≤-trans)
      (λ _ _ _ → Q.≤-trans) i x y z x≤y y≤z
  path i .Poset.≤-antisym {x} {y} x≤y y≤x =
    is-prop→pathp
      (λ i →
        Π-is-hlevel² {A = ob i } {B = λ _ → ob i} 1 λ x y →
        Π-is-hlevel² {A = order i x y} {B = λ _ → order i y x} 1 λ _ _ →
        ob-set i x y)
      (λ _ _ → P.≤-antisym)
      (λ _ _ → Q.≤-antisym) i x y x≤y y≤x
```

</details>

It remains to prove that this construction is coherent: given an
isomorphism $f : P \cong Q$, we've recovered a path $p(f) : P \equiv Q$,
over which we can compare isomorphisms $P \cong P$ with isomorphisms $P
\cong Q$. The necessary coherence datum says that, over $p$, the
identity becomes $f$.

```agda
Posets-is-category : ∀ {o ℓ} → is-category (Posets o ℓ)
Posets-is-category .to-path        = Poset-path
Posets-is-category .to-path-over f = Posets.≅-pathp _ _ $
  Monotone-pathp $ funextP λ x → path→ua-pathp _ refl
```
