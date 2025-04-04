---
description: |
  Twisted comma categories.
---
<!--
```agda
open import Cat.Displayed.Cocartesian.Discrete
open import Cat.Displayed.Cocartesian
open import Cat.Displayed.Cartesian
open import Cat.Instances.Product
open import Cat.Displayed.Base
open import Cat.Prelude

import Cat.Functor.Reasoning
import Cat.Reasoning
```
-->
```agda
module Cat.Displayed.Instances.TwistedComma where
```

# Twisted comma categories

:::{.definition #twisted-comma-category}
Let $F : \cA \to \cC$ and $\cB \to \cC$ be a pair of functors with
a common codomain. The **twisted comma category** is a displayed
category $\mathrm{Tw}(F, G) \liesover \cA\op \times \cB$ where
objects over $(A, B)$ are morphisms $\cC(F(A), G(B))$, and morphisms
consist of commutative squares of the following form:

~~~{.quiver}
\begin{tikzcd}
	{F(A_1)} && {F(A_2)} \\
	\\
	{G(B_1)} && {G(B_2)}
	\arrow["f"{description}, from=1-1, to=3-1]
	\arrow["\alpha"{description}, from=1-3, to=1-1]
	\arrow["g"{description}, from=1-3, to=3-3]
	\arrow["\beta"{description}, from=3-1, to=3-3]
\end{tikzcd}
~~~
:::


<!--
```agda
module _
  {oa ℓa ob ℓb oc ℓc}
  {A : Precategory oa ℓa}
  {B : Precategory ob ℓb}
  {C : Precategory oc ℓc}
  (F : Functor A C)
  (G : Functor B C)
  where
  private
    module A = Cat.Reasoning A
    module B = Cat.Reasoning B
    module C = Cat.Reasoning C
    module F = Cat.Functor.Reasoning F
    module G = Cat.Functor.Reasoning G

  open Displayed
```
-->

```agda
  Twisted-comma : Displayed (A ^op ×ᶜ B) ℓc ℓc
  Twisted-comma .Ob[_] (a , b) = C.Hom (F.₀ a) (G.₀ b)
  Twisted-comma .Hom[_] (α , β) f g = G.₁ β C.∘ f C.∘ F.₁ α ≡ g
```

The identity map consists of the evident commutative square
$G(\id) \circ f \circ F(\id) = f$, and composition is given
by composition of squares.

```agda
  Twisted-comma .id' {x = f} =
    G.₁ B.id C.∘ f C.∘ F.₁ A.id ≡⟨ C.elim-outer G.F-id F.F-id ⟩
    f ∎
  Twisted-comma ._∘'_ {x = f} {y = g} {z = h} {f = (α₁ , β₁)} {g = (α₂ , β₂)} p q =
    G.₁ (β₁ B.∘ β₂) C.∘ f C.∘ F.₁ (α₂ A.∘ α₁)         ≡⟨ C.push-outer (G.F-∘ β₁ β₂) (F.F-∘ α₂ α₁) ⟩
    G.₁ β₁ C.∘ ⌜ G.₁ β₂ C.∘ f C.∘ F.₁ α₂ ⌝ C.∘ F.₁ α₁ ≡⟨ ap! q ⟩
    G.₁ β₁ C.∘ g C.∘ F.₁ α₁                           ≡⟨ p ⟩
    h                                                 ∎
```

```agda
  Twisted-comma .Hom[_]-set _ _ _ = hlevel 2
  Twisted-comma .idr' _ = prop!
  Twisted-comma .idl' _ = prop!
  Twisted-comma .assoc' _ _ _ = prop!
```

Twisted comma categories are a useful technical tool for talking
about factorizations of morphisms, as $\mathrm{Tw}(F, G)_{l, r}(\id, f)$
are precisely factorizations of $f$ into a morphism in the image of
$F$ followed by a morphism in the image of $G$.

## Twisted comma categories are discrete cocartesian fibrations

<!--
```agda
module _
  {oa ℓa ob ℓb oc ℓc}
  {A : Precategory oa ℓa}
  {B : Precategory ob ℓb}
  {C : Precategory oc ℓc}
  {F : Functor A C}
  {G : Functor B C}
  where
  private
    module A = Cat.Reasoning A
    module B = Cat.Reasoning B
    module C = Cat.Reasoning C
    module F = Cat.Functor.Reasoning F
    module G = Cat.Functor.Reasoning G

  open Displayed
  open is-discrete-cocartesian-fibration
```
-->

The twisted arrow category is a [[discrete cocartesian fibration]].

```agda
  Twisted-comma-is-discrete-cocartesian-fibration
    : is-discrete-cocartesian-fibration (Twisted-comma F G)
```

Consider some $f : \cC(F(A_1), G(B_1))$, and a pair of maps
$\alpha : \cA(A_2, A_1)$, $\beta : \cB(B_1, B_2)$, fitting into the
following diagram:

~~~{.quiver}
\begin{tikzcd}
  {F(A_1)} && {F(A_2)} \\
  \\
  {G(B_1)} && {G(B_2)}
  \arrow["f"', from=1-1, to=3-1]
  \arrow["{F(\alpha)}"{description}, from=1-3, to=1-1]
  \arrow["{G(\beta)}"{description}, from=3-1, to=3-3]
\end{tikzcd}
~~~

We can obtain our lift by simply composing $G(\beta) \circ f \circ F(\alpha)$!

```agda
  Twisted-comma-is-discrete-cocartesian-fibration .fibre-set _ = hlevel 2
  Twisted-comma-is-discrete-cocartesian-fibration .cocart-lift (α , β) f =
    contr (G.₁ β C.∘ f C.∘ F.₁ α , refl) λ (h , p) →
      Σ-prop-path! p
```

## Twisted Arrow categories

:::{.definition #twisted-arrow-category}
The **twisted arrow category** of a category $\cC$ is the
twisted comma category $\mathrm{Tw}(\Id_{\cC}, \Id_{\cC})$.
:::

```agda
Twisted-arrow
  : ∀ {o ℓ}
  → (C : Precategory o ℓ)
  → Displayed (C ^op ×ᶜ C) ℓ ℓ
Twisted-arrow C = Twisted-comma Id Id
```
