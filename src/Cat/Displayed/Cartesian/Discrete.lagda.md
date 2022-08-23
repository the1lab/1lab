```agda
open import Cat.Displayed.Cartesian
open import Cat.Displayed.Fibre
open import Cat.Displayed.Base
open import Cat.Prelude
open import Cat.Thin

import Cat.Reasoning

module Cat.Displayed.Cartesian.Discrete where
```

<!--
```agda
open Cartesian-fibration
open Cartesian-lift
open Cartesian
open is-thin
```
-->

# Discrete fibrations

A **discrete fibration** is a displayed category whose [fibres] are all
_discrete categories_: thin, univalent groupoids. Since thin, univalent
groupoids are sets, a discrete fibration over $\ca{B}$ is an alternate
way of encoding a presheaf over $\ca{B}$, i.e., a functor
$\ca{B}\op\to\sets$. Here, we identify a purely fibrational property
that picks out the discrete fibrations among the displayed categories,
without talking about the fibres directly.

[fibres]: Cat.Displayed.Fibre.html

A discrete fibration is a displayed category such that each type of
displayed objects is a set, and such that, for each right corner

~~~{.quiver}
\[\begin{tikzcd}
  & {y'} \\
  x & {y\text{,}}
  \arrow[Bar-{Triangle[open]}, from=1-2, to=2-2]
  \arrow["f"', from=2-1, to=2-2]
\end{tikzcd}\]
~~~

there is a contractible space of objects $x'$ over $x$ equipped with
maps $x' \to_f y'$.

<!--
```agda
module _ {o ℓ o′ ℓ′} {B : Precategory o ℓ} (E : Displayed B o′ ℓ′) where
  private
    module B = Cat.Reasoning B
    module E = Displayed E
```
-->

```agda
  record Discrete-fibration : Type (o ⊔ ℓ ⊔ o′ ⊔ ℓ′) where
    field
      fibre-set : ∀ x → is-set E.Ob[ x ]
      lifts
        : ∀ {x y} (f : B.Hom x y) (y′ : E.Ob[ y ])
        → is-contr (Σ[ x′ ∈ E.Ob[ x ] ] E.Hom[ f ] x′ y′)
```

## Discrete fibrations are Cartesian

To prove that discrete fibrations deserve the name discrete
_fibrations_, we prove that any discrete fibration is a Cartesian
fibration. By assumption, every right corner has a unique lift, which is
in particular a lift: we just have to show that the lift is Cartesian.

```agda
  discrete→cartesian : Discrete-fibration → Cartesian-fibration E
  discrete→cartesian disc = r where
    open Discrete-fibration disc
    r : Cartesian-fibration E
    r .has-lift f y′ .x′ = lifts f y′ .centre .fst
    r .has-lift f y′ .lifting = lifts f y′ .centre .snd
```

So suppose we have an open diagram

~~~{.quiver .tall-2}
\[\begin{tikzcd}
  {u'} \\
  & {a'} && {b'} \\
  u \\
  & a && {b,}
  \arrow["{f'}"', from=2-2, to=2-4]
  \arrow["f", from=4-2, to=4-4]
  \arrow[Bar-{Triangle[open]}, from=2-2, to=4-2]
  \arrow[Bar-{Triangle[open]}, from=2-4, to=4-4]
  \arrow["m"', from=3-1, to=4-2]
  \arrow[Bar-{Triangle[open]}, from=1-1, to=3-1]
  \arrow["{h'}", curve={height=-12pt}, from=1-1, to=2-4]
\end{tikzcd}\]
~~~

where $f' : a' \to b'$ is the unique lift of $f$ along $b'$. We need to
find a map $u' \to_m a'$. Observe that we have a right corner (with
vertices $u$ and $a'$ over $a$), so that we an object $u_2$ over $u$ and
map $l : u_2 \to_m a'$. Initially, this looks like it might not help,
but observe that $u' \xto{h'}_{f \circ m} b'$ and $u_2 \xto{l}_{u} a'
\xto{f'}_f b'$ are lifts of the right corner with base given by $u \to a
\to b$, so that by uniqueness, $u2 = u'$: thus, we can use $l$ as our
map $u' \to a'$.

```agda
    r .has-lift f y′ .cartesian .universal {u} {u′} m h′ =
      subst (λ x → E.Hom[ m ] x (lifts f y′ .centre .fst))
        (ap fst $ is-contr→is-prop (lifts (f B.∘ m) y′)
          (_ , lifts f y′ .centre .snd E.∘′ lifts m _ .centre .snd)
          (u′ , h′))
        (lifts m (lifts f y′ .centre .fst) .centre .snd)
    r .has-lift f y′ .cartesian .commutes m h′ =
      Σ-inj-set (fibre-set _) $ is-contr→is-prop (lifts (f B.∘ m) y′) _ _
    r .has-lift f y′ .cartesian .unique {u} {u′} {m} m′ x =
      Σ-inj-set (fibre-set u) $ is-contr→is-prop (lifts m _) (u′ , m′) (u′ , _)
```

## Fibres of discrete fibrations

Let $x$ be an object of $\ca{B}$. Let us ponder the fibre $\ca{E}^*(x)$:
we know that it is strict, since by assumption there is a _set_ of
objects over $x$. Let us show also that it is thin: imagine that we have
two parallel, vertical arrows $f, g : a \to_\id{id} b$. These assemble
into a diagram like

~~~{.quiver}
\[\begin{tikzcd}
  {a'} && {b'} && {a'} \\
  \\
  x && x && {x\text{,}}
  \arrow["f", from=1-1, to=1-3]
  \arrow["g"', from=1-5, to=1-3]
  \arrow[Bar-{Triangle[open]}, from=1-1, to=3-1]
  \arrow[Bar-{Triangle[open]}, from=1-3, to=3-3]
  \arrow[Bar-{Triangle[open]}, from=1-5, to=3-5]
  \arrow["{\mathrm{id}}"{description}, from=3-1, to=3-3]
  \arrow["{\mathrm{id}}"{description}, from=3-5, to=3-3]
  \arrow["\lrcorner"{anchor=center, pos=0.125}, draw=none, from=1-1, to=3-3]
  \arrow["\lrcorner"{anchor=center, pos=0.125, rotate=-90}, draw=none, from=1-5, to=3-3]
\end{tikzcd}\]
~~~

whence we see that $(a', f)$ and $(a', g)$ are both lifts for the lower
corner given by lifting the identity map along $b'$ --- so, since lifts
are unique, we have $f = g$.

```agda
  discrete→thin-fibres : ∀ x → Discrete-fibration → is-thin (Fibre E x)
  discrete→thin-fibres x disc = t where
    open Discrete-fibration disc
    t : is-thin (Fibre E x)
    t .Ob-is-set = fibre-set x
    t .Hom-is-prop A B f g = Σ-inj-set (fibre-set x) $
      is-contr→is-prop (lifts B.id B) (A , f) (A , g)
```
