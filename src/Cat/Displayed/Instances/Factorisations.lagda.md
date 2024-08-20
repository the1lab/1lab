---
description: |
  The displayed category of factorisations.
---
<!--
```agda
open import Cat.Displayed.Instances.Comma
open import Cat.Instances.Product
open import Cat.Displayed.Total
open import Cat.Displayed.Base
open import Cat.Prelude

import Cat.Reasoning
```
-->
```agda
module Cat.Displayed.Instances.Factorisations where
```

# The displayed category of factorisations

One of the main objects of study in category theory is **factorisations**
of morphisms $f : \cC(X,Y)$ into pairs of composable morphisms $r \circ l = f$.
We can nicely organize all factorisations of morphisms in a category $\cC$
into a [[displayed category]] over the [[arrow category]] of $\cC$, which
we will denote $\mathrm{Fac}(\cC)$.

<!--
```agda
module _ {o ℓ} (B : Precategory o ℓ) where
  open Cat.Reasoning B
  open Displayed
  open Total-hom

```
-->

Objects of $\mathrm{Fac}(C)$ over some $f : \cC(X,Y)$ are given by
factorisations of $f$.

```agda
  record Factor {x y} (f : Hom x y) : Type (o ⊔ ℓ) where
    no-eta-equality
    field
      {fac} : Ob
      left : Hom x fac
      right : Hom fac y
      factors : right ∘ left ≡ f

  open Factor
```

Morphisms are a bit more sublte. Recall that morphisms in $\cC^{\to}$
between $f : \cC(A,B)$ and $g : \cC(X,Y)$ are given by commuting squares
of the following shape:

~~~{.quiver}
\begin{tikzcd}
  A && C \\
  \\
  B && D
  \arrow["h", from=1-1, to=1-3]
  \arrow["f"', from=1-1, to=3-1]
  \arrow["g", from=1-3, to=3-3]
  \arrow["k"', from=3-1, to=3-3]
\end{tikzcd}
~~~

Objects in $\mathrm{Fac}(\cC)$ are factorisations, so displayed morphisms
in $\mathrm{Fac}(\cC)$ are parameterised the following sort of commutative
squares:

~~~{.quiver}
\begin{tikzcd}
  A && C \\
  \\
  I && J \\
  \\
  B && D
  \arrow["h", from=1-1, to=1-3]
  \arrow["{f_l}"', from=1-1, to=3-1]
  \arrow["f"', curve={height=12pt}, from=1-1, to=5-1]
  \arrow["{g_l}", from=1-3, to=3-3]
  \arrow["g", curve={height=-12pt}, from=1-3, to=5-3]
  \arrow["{f_r}"', from=3-1, to=5-1]
  \arrow["{g_r}", from=3-3, to=5-3]
  \arrow["k"', from=5-1, to=5-3]
\end{tikzcd}
~~~

This suggests that morphisms in $\mathrm{Fac}(\cC)$ ought to be maps
between the midpoints of the two factorisations that make everything
in sight commute. This is most easily thought of diagramatically;

~~~{.quiver}
\begin{tikzcd}
  A && C \\
  \\
  I && J \\
  \\
  B && D
  \arrow["h", from=1-1, to=1-3]
  \arrow["{f_l}"', from=1-1, to=3-1]
  \arrow["f"', curve={height=12pt}, from=1-1, to=5-1]
  \arrow["{g_l}", from=1-3, to=3-3]
  \arrow["g", curve={height=-12pt}, from=1-3, to=5-3]
  \arrow["l", color={rgb,255:red,214;green,92;blue,92}, from=3-1, to=3-3]
  \arrow["{f_r}"', from=3-1, to=5-1]
  \arrow["{g_r}", from=3-3, to=5-3]
  \arrow["k"', from=5-1, to=5-3]
\end{tikzcd}
~~~

```agda
  record Factor-hom
    {a b x y} {f : Hom a b} {g : Hom x y}
    (α : Total-hom (Arrows B) ((a , b) , f) ((x , y) , g))
    (f* : Factor f) (g* : Factor g)
    : Type ℓ
    where
    no-eta-equality
    field
      split : Hom (f* .fac) (g* .fac)
      squarel : split ∘ f* .left ≡ g* .left ∘ α .hom .fst
      squarer : α .hom .snd ∘ f* .right ≡ g* .right ∘ split

  open Factor-hom
```

<!--
```agda
module _ {o ℓ} {B : Precategory o ℓ} where
  open Cat.Reasoning B
  open Displayed
  open Factor-hom
  open Total-hom
  open Factor

  Factor-hom-pathp
    : ∀ {a a' b b' x x' y y'}
    → {f : Hom a b} {f' : Hom a' b'} {g : Hom x y} {g' : Hom x' y'}
    → {sq : Total-hom (Arrows B) ((a , b), f) ((x , y) , g)} {sq' : Total-hom (Arrows B) ((a' , b'), f') ((x' , y') , g')}
    → {f* : Factor B f} {f'* : Factor B f'} {g* : Factor B g} {g'* : Factor B g'}
    → {α : Factor-hom B sq f* g*} {β : Factor-hom B sq' f'* g'*}
    → {pa : a ≡ a'} {pb : b ≡ b'} {px : x ≡ x'} {py : y ≡ y'}
    → {pf : PathP (λ i → Hom (pa i) (pb i)) f f'}
    → {pg : PathP (λ i → Hom (px i) (py i)) g g'}
    → {psq : PathP (λ i → Total-hom (Arrows B) ((pa i , pb i) , pf i) ((px i , py i) , pg i)) sq sq'}
    → {pf* : PathP (λ i → Factor B (pf i)) f* f'*}
    → {pg* : PathP (λ i → Factor B (pg i)) g* g'*}
    → PathP (λ i → Hom (pf* i .fac) (pg* i .fac)) (α .split) (β .split)
    → PathP (λ i → Factor-hom B (psq i) (pf* i) (pg* i)) α β
  Factor-hom-pathp psplit i .split = psplit i
  Factor-hom-pathp {α = α} {β = β} {pa = pa} {psq = psq} {pf* = pf*} {pg* = pg*} psplit i .squarel =
    is-prop→pathp (λ i → Hom-set (pa i) (pg* i .fac) (psplit i ∘ pf* i .left) (pg* i .left ∘ psq i .hom .fst))
      (α .squarel) (β .squarel) i
  Factor-hom-pathp {α = α} {β = β} {py = py} {psq = psq} {pf* = pf*} {pg* = pg*} psplit i .squarer =
    is-prop→pathp (λ i → Hom-set (pf* i .fac) (py i) (psq i .hom .snd ∘ pf* i .right) (pg* i .right ∘ psplit i))
      (α .squarer) (β .squarer) i

unquoteDecl H-Level-Factor-hom = declare-record-hlevel 2 H-Level-Factor-hom (quote Factor-hom)

```
-->

<!--
```agda
module _ {o ℓ} (B : Precategory o ℓ) where
  open Cat.Reasoning B
  open Displayed
  open Factor-hom
  open Total-hom
  open Factor
```
-->

Assembling factorisations and maps between factorisations into a displayed
category is straightforward.

```agda
  Factorisations : Displayed (∫ (Arrows B)) (o ⊔ ℓ) ℓ
  Factorisations .Ob[_] ((x , y) , f) = Factor B f
  Factorisations .Hom[_] = Factor-hom B
  Factorisations .Hom[_]-set _ _ _ = hlevel 2
  Factorisations .id' .split = id
  Factorisations .id' .squarel = id-comm-sym
  Factorisations .id' .squarer = id-comm-sym
  Factorisations ._∘'_ α β .split = α .split ∘ β .split
  Factorisations ._∘'_ α β .squarel = pullr (β .squarel) ∙ extendl (α .squarel)
  Factorisations ._∘'_ α β .squarer = pullr (β .squarer) ∙ extendl (α .squarer)
  Factorisations .idr' α = Factor-hom-pathp (idr _)
  Factorisations .idl' α = Factor-hom-pathp (idl _)
  Factorisations .assoc' α β γ = Factor-hom-pathp (assoc _ _ _)
```
