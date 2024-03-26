<!--
```agda
open import Cat.Functor.Naturality
open import Cat.Monoidal.Diagonals
open import Cat.Instances.Product
open import Cat.Monoidal.Braided
open import Cat.Monoidal.Base
open import Cat.Prelude

import Cat.Functor.Reasoning
import Cat.Reasoning
```
-->

```agda
module Cat.Monoidal.Functor {oc ℓc od ℓd}
  {C : Precategory oc ℓc} (Cᵐ : Monoidal-category C)
  {D : Precategory od ℓd} (Dᵐ : Monoidal-category D)
  where
```

# Monoidal functors {defines="monoidal-functor lax-monoidal-functor oplax-monoidal-functor strong-monoidal-functor"}

<!--
```agda
open Cat.Reasoning D

private
  module C = Monoidal-category Cᵐ
  module D = Monoidal-category Dᵐ
```
-->

Categorifying the fact that a morphism between [[monoids]] is expected
to preserve the unit and multiplication, a [[functor]] between [[monoidal
categories]] should come *equipped* with [[natural isomorphisms]]

$$
\begin{align*}
FA \otimes FB &\cong F(A \otimes B) \\
1 &\cong F1
\end{align*}
$$

witnessing that it preserves the tensor product and unit.

However, just like for [[lax functors]] between [[bicategories]], we have
the option of requiring only a natural *transformation* in one direction
or the other.
If we choose the forward direction $FA \otimes FB \to F(A \otimes B)$,
we obtain the notion of a **lax monoidal functor**; choosing the
opposite direction instead would yield an **oplax monoidal functor**.

We begin by defining the *structure* of a lax monoidal functor on a given
functor $F$: this consists of the aforementioned morphisms, as well
as some coherence conditions similar to the ones for a [[lax functor]].

```agda
record Lax-monoidal-functor-on (F : Functor C D) : Type (oc ⊔ ℓc ⊔ od ⊔ ℓd) where
  private module F = Cat.Functor.Reasoning F

  field
    ε : Hom D.Unit (F.₀ C.Unit)
    F-mult : D.-⊗- F∘ (F F× F) => F F∘ C.-⊗-

  module φ = _=>_ F-mult

  φ : ∀ {A B} → Hom (F.₀ A D.⊗ F.₀ B) (F.₀ (A C.⊗ B))
  φ = φ.η _

  field
    F-α→ : ∀ {A B C}
      → F.₁ (C.α→ A B C) ∘ φ ∘ (φ D.⊗₁ id) ≡ φ ∘ (id D.⊗₁ φ) ∘ D.α→ _ _ _
    F-λ← : ∀ {A} → F.₁ (C.λ← {A}) ∘ φ ∘ (ε D.⊗₁ id) ≡ D.λ←
    F-ρ← : ∀ {A} → F.₁ (C.ρ← {A}) ∘ φ ∘ (id D.⊗₁ ε) ≡ D.ρ←
```

<!--
```agda
  F-α← : ∀ {A B C}
    → F.₁ (C.α← A B C) ∘ φ ∘ (id D.⊗₁ φ) ≡ φ ∘ (φ D.⊗₁ id) ∘ D.α← _ _ _
  F-α← = swizzle (sym (F-α→ ∙ assoc _ _ _)) (D.α≅ .invl) (F.F-map-iso C.α≅ .invr)
    ∙ sym (assoc _ _ _)

private unquoteDecl eqv = declare-record-iso eqv (quote Lax-monoidal-functor-on)
Lax-monoidal-functor-on-path
  : ∀ {F} {l l' : Lax-monoidal-functor-on F}
  → l .Lax-monoidal-functor-on.ε ≡ l' .Lax-monoidal-functor-on.ε
  → l .Lax-monoidal-functor-on.F-mult ≡ l' .Lax-monoidal-functor-on.F-mult
  → l ≡ l'
Lax-monoidal-functor-on-path p q = Iso.injective eqv
  (Σ-pathp p (Σ-prop-pathp (λ _ _ → hlevel 1) q))
```
-->

```agda
Lax-monoidal-functor : Type (oc ⊔ ℓc ⊔ od ⊔ ℓd)
Lax-monoidal-functor = Σ (Functor C D) Lax-monoidal-functor-on
```

A **monoidal functor**, or **strong monoidal functor**[^strong], is
then simply a lax monoidal functor whose structure morphisms are
[[invertible]].

[^strong]: Not to be confused with a [[strong|strong functor]] monoidal
functor, in the sense of a monoidal functor equipped with a [[strength]].

```agda
record Monoidal-functor-on (F : Functor C D) : Type (oc ⊔ ℓc ⊔ od ⊔ ℓd) where
  field
    lax : Lax-monoidal-functor-on F

  open Lax-monoidal-functor-on lax public

  field
    ε-inv : is-invertible ε
    F-mult-inv : is-invertibleⁿ F-mult

Monoidal-functor : Type (oc ⊔ ℓc ⊔ od ⊔ ℓd)
Monoidal-functor = Σ (Functor C D) Monoidal-functor-on
```

## Braided and symmetric monoidal functors {defines="braided-monoidal-functor symmetric-monoidal-functor"}

A monoidal functor between [[braided monoidal categories]] can additionally
preserve the braiding in the sense that the following diagram commutes,
yielding the notion of a **braided monoidal functor**.

~~~{.quiver}
\[\begin{tikzcd}
  {FA \otimes FB} & {F(A \otimes B)} \\
  {FB \otimes FA} & {F(B \otimes A)}
  \arrow["\varphi", from=1-1, to=1-2]
  \arrow["\beta"', from=1-1, to=2-1]
  \arrow["\varphi"', from=2-1, to=2-2]
  \arrow["F\beta", from=1-2, to=2-2]
\end{tikzcd}\]
~~~

<!--
```agda
module _
  (Cᵇ : Braided-monoidal Cᵐ)
  (Dᵇ : Braided-monoidal Dᵐ)
  where
  module Cᵇ = Braided-monoidal Cᵇ
  module Dᵇ = Braided-monoidal Dᵇ
```
-->

```agda
  is-braided-functor : Lax-monoidal-functor → Type (oc ⊔ ℓd)
  is-braided-functor (F , lax) = ∀ {A B} → φ ∘ Dᵇ.β→ ≡ F.₁ Cᵇ.β→ ∘ φ {A} {B}
    where
      module F = Functor F
      open Lax-monoidal-functor-on lax
```

A **symmetric monoidal functor** between [[symmetric monoidal categories]]
is just a braided monoidal functor, since there is no extra structure to
preserve.

<!--
```agda
module _
  (Cˢ : Symmetric-monoidal Cᵐ)
  (Dˢ : Symmetric-monoidal Dᵐ)
  where
  open Symmetric-monoidal Cˢ using (Cᵇ)
  open Symmetric-monoidal Dˢ using () renaming (Cᵇ to Dᵇ)
```
-->

```agda
  is-symmetric-functor : Lax-monoidal-functor → Type (oc ⊔ ℓd)
  is-symmetric-functor = is-braided-functor Cᵇ Dᵇ
```

## Diagonal monoidal functors {defines="diagonal-monoidal-functor idempotent-monoidal-functor"}

If the source and target categories are equipped with [[diagonal
morphisms|monoidal category with diagonals]], then a **diagonal
monoidal functor**, or **idempotent monoidal functor** is a monoidal
functor that makes the following diagram commute:

~~~{.quiver}
\[\begin{tikzcd}
  FA \\
  {FA \otimes FA} & {F(A \otimes A)}
  \arrow["\delta"', from=1-1, to=2-1]
  \arrow["\varphi"', from=2-1, to=2-2]
  \arrow["F\delta", from=1-1, to=2-2]
\end{tikzcd}\]
~~~

<!--
```agda
module _
  (Cᵈ : Diagonals Cᵐ)
  (Dᵈ : Diagonals Dᵐ)
  where
  module Cᵈ = Diagonals Cᵈ
  module Dᵈ = Diagonals Dᵈ
```
-->

```agda
  is-diagonal-functor : Lax-monoidal-functor → Type (oc ⊔ ℓd)
  is-diagonal-functor (F , lax) = ∀ {A} → φ ∘ Dᵈ.δ ≡ F.₁ (Cᵈ.δ {A})
    where
      module F = Functor F
      open Lax-monoidal-functor-on lax
```

The "idempotent" terminology comes from the semantics of programming
languages, where lax monoidal functors are used to model certain kinds
of effectful computations, as a "static" alternative to [[monads]].
In that setting, an idempotent monoidal functor (or "idempotent
applicative functor") represents an effect that can be executed
multiple times with the same effect as executing it once: for example,
reading from an immutable data source or throwing an exception.

# Monoidal natural transformations {defines="monoidal-natural-transformation"}

The notion of [[natural transformation]] between functors can also be
refined in the case of monoidal functors: a **monoidal natural
transformation** $\alpha : F \To G$ is one such that the following
diagrams commute.

<div class="mathpar">

~~~{.quiver}
\[\begin{tikzcd}
  {FA \otimes FB} & {GA \otimes GB} \\
  {F(A \otimes B)} & {G(A \otimes B)}
  \arrow[from=1-1, to=2-1]
  \arrow["{\alpha_A \otimes \alpha_B}", from=1-1, to=1-2]
  \arrow[from=1-2, to=2-2]
  \arrow["{\alpha_{A\otimes B}}"', from=2-1, to=2-2]
\end{tikzcd}\]
~~~

~~~{.quiver}
\[\begin{tikzcd}
  1 \\
  F1 & G1
  \arrow[from=1-1, to=2-1]
  \arrow["{\alpha_1}"', from=2-1, to=2-2]
  \arrow[from=1-1, to=2-2]
\end{tikzcd}\]
~~~

</div>

<!--
```agda
module _ ((F , F-monoidal) (G , G-monoidal) : Lax-monoidal-functor) where
  module FM = Lax-monoidal-functor-on F-monoidal
  module GM = Lax-monoidal-functor-on G-monoidal
  open _=>_
```
-->

```agda
  record is-monoidal-transformation (α : F => G) : Type (oc ⊔ ℓc ⊔ ℓd) where
    field
      nat-ε : α .η C.Unit ∘ FM.ε ≡ GM.ε
      nat-φ : ∀ {A B} → α .η _ ∘ FM.φ {A} {B} ≡ GM.φ ∘ (α .η _ D.⊗₁ α .η _)
```

Note that, since monoidal categories can be thought of as one-object
[[bicategories]], we may expect to also have [[modifications]] between
monoidal natural transformations, but this is not the case: the
categorical ladder ends here. This is analogous to the fact that
[[monoids]] only form a category and not a bicategory, even when
viewed as one-object categories: there simply aren't enough objects
to have interesting 3-cells (resp. 2-cells)!
