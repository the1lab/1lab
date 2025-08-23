---
description: |
  Two-sided fibrations.
---
<!--
```agda
open import Cat.Displayed.BeckChevalley
open import Cat.Displayed.Cocartesian
open import Cat.Displayed.Cartesian
open import Cat.Instances.Product
open import Cat.Displayed.Base
open import Cat.Prelude

import Cat.Displayed.Reasoning
import Cat.Displayed.Morphism
import Cat.Reasoning
```
-->
```agda
module Cat.Displayed.TwoSided where
```

# Two-sided fibrations

One useful perspective on [[cartesian fibrations]] and [[cocartesian fibrations]]
is that they are (co)presheaves of categories. This raises a natural question: what
is the appropriate generalization of profunctors?

<!--
```agda
module _
  {oa ℓa ob ℓb oe ℓe}
  {A : Precategory oa ℓa} {B : Precategory ob ℓb}
  (E : Displayed (A ×ᶜ B) oe ℓe)
  where
  private
    module A = Cat.Reasoning A
    module B = Cat.Reasoning B
    open Cat.Displayed.Reasoning E
    open Cat.Displayed.Morphism E
```
-->

:::{.definition #two-sided-fibration}
A displayed category $\cE \liesover \cA \times \cB$ is a **two-sided fibration**
when it satisfies the following 3 conditions:

1. We are given an operation assigning [[cartesian lifts]]
$\pi_{u, Y} : \cE_{u, \id}(u^{*}(Y), Y)$ to each $u : \cA(A_1, A_2)$, $B : \cB$, and $Y : \cE_{A_2, B}$.

2. Similarly, to each $A : \cA, v : \cB(B_1, B_2)$ and $X : \cE_{A, B_1}$,
we are equipped with a [[cocartesian lift]] $\iota_{v, X} : \cE_{\id, v}(X, v_{!}(X))$.

3. For every diagram of the form below with $f$ cocartesian and $g$ cartesian,
$h$ is cartesian if and only if $k$ is cocartesian.

~~~{.quiver}
\begin{tikzcd}
  W && X \\
  & Y && Z \\
  {(A_1, B_1)} && {(A_2, B_1)} \\
  & {(A_1, B_2)} && {(A_2, B_2)}
  \arrow["g", from=1-1, to=1-3]
  \arrow["k", from=1-1, to=2-2]
  \arrow[from=1-1, to=3-1]
  \arrow["f", from=1-3, to=2-4]
  \arrow[from=1-3, to=3-3]
  \arrow["h"{pos=0.3}, from=2-2, to=2-4]
  \arrow[from=2-2, to=4-2]
  \arrow[from=2-4, to=4-4]
  \arrow["{(u,\id)}"{pos=0.7}, from=3-1, to=3-3]
  \arrow["{(\id, v)}"', from=3-1, to=4-2]
  \arrow["{(\id, v)}", from=3-3, to=4-4]
  \arrow["{(u,\id)}"', from=4-2, to=4-4]
\end{tikzcd}
~~~
:::


```agda
  record Two-sided-fibration : Type (oa ⊔ ℓa ⊔ ob ⊔ ℓb ⊔ oe ⊔ ℓe) where
    no-eta-equality
    field
      cart-lift
        : ∀ {a₁ a₂ : A.Ob} {b : B.Ob}
        → (u : A.Hom a₁ a₂)
        → (y' : Ob[ a₂ , b ])
        → Cartesian-lift E (u , B.id) y'
      cocart-lift
        : ∀ {a : A.Ob} {b₁ b₂ : B.Ob}
        → (v : B.Hom b₁ b₂)
        → (x' : Ob[ a , b₁ ])
        → Cocartesian-lift E (A.id , v) x'
      cart-beck-chevalley
        : ∀ {a₁ a₂ : A.Ob} {b₁ b₂ : B.Ob}
        → {u : A.Hom a₁ a₂} {v : B.Hom b₁ b₂}
        → right-beck-chevalley E
            (A.id , v) (u , B.id) (u , B.id) (A.id , v)
            (sym A.id-comm ,ₚ B.id-comm)
      cocart-beck-chevalley
        : ∀ {a₁ a₂ : A.Ob} {b₁ b₂ : B.Ob}
        → {u : A.Hom a₁ a₂} {v : B.Hom b₁ b₂}
        → left-beck-chevalley E
            (A.id , v) (u , B.id) (u , B.id) (A.id , v)
            (sym A.id-comm ,ₚ B.id-comm)
```

This definition is rather opaque, so let's break it down. The first two
conditions ensure that we have 2 functorial actions on each of the [[fibre categories]]
$E_{a, b}$: the first acts contravariantly in $\cA$, the second covariantly
in $\cB$. These are analogs to the actions $P(-, \id)$ and $P(\id, -)$ of
a profunctor $P : \cA \times \cB \to \Sets$. The final condition serves to
ensure that the [[base change]] and [[cobase change]] functors
$u^{*} : \cE_{A_2, B} \to \cE_{A_1, B}$ and $v_{!} : \cE_{A, B_1} \to \cE_{A, B_2}$
preserve cocartesian and cartesian morphisms, resp.
