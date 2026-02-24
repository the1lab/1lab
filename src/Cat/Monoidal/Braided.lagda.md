<!--
```agda
open import Cat.Functor.Naturality
open import Cat.Functor.Bifunctor
open import Cat.Monoidal.Base
open import Cat.Functor.Base
open import Cat.Prelude

import Cat.Functor.Reasoning
import Cat.Reasoning

open _=>_
```
-->

```agda
module Cat.Monoidal.Braided {o ℓ}
  {C : Precategory o ℓ} (Cᵐ : Monoidal-category C)
  where
```

# Braided and symmetric monoidal categories {defines="braided-monoidal-category braiding symmetric-monoidal-category"}

<!--
```agda
open Cat.Reasoning C
open Monoidal Cᵐ
```
-->

A **braided monoidal category** is a [[monoidal category]] equipped with
a *braiding*: a [[natural isomorphism]] $\beta : A \otimes B \cong B
\otimes A$ satisfying some coherence conditions explained below.

```agda
record Braided-monoidal : Type (o ⊔ ℓ) where
  field
    braiding : -⊗- ≅ⁿ Flip -⊗-
```

<!--
```agda
  module β→ = _=>_ (braiding .Isoⁿ.to)
  module β← = _=>_ (braiding .Isoⁿ.from)

  β→ : ∀ {A B} → Hom (A ⊗ B) (B ⊗ A)
  β→ = braiding .Isoⁿ.to ._=>_.η _

  β← : ∀ {A B} → Hom (A ⊗ B) (B ⊗ A)
  β← = braiding .Isoⁿ.from ._=>_.η _

  β≅ : ∀ {A B} → A ⊗ B ≅ B ⊗ A
  β≅ = isoⁿ→iso braiding _
```
-->

The name "braiding" is meant to suggest that flipping $A \otimes B$
twice in the same direction is not necessarily trivial, which we may
represent using *braid diagrams* like this one:

~~~{.quiver}
\begin{tikzpicture}[
  braid/.cd,
  gap=.15,
  every strand/.style={ultra thick},
  strand 1/.style={cyan},
  strand 2/.style={magenta}
]
  \pic (braid) {braid={s_1^{-1} s_1^{-1}}};
  \node[above,color=diagramfg,at=(braid-1-s)] {$A$};
  \node[below,color=diagramfg,at=(braid-1-e)] {$A$};
  \node[above,color=diagramfg,at=(braid-2-s)] {$B$};
  \node[below,color=diagramfg,at=(braid-2-e)] {$B$};
\end{tikzpicture}
~~~

The above diagram represents the morphism $\beta \circ \beta : A \otimes
B \to A \otimes B$; if the braiding *is* symmetric in the sense that this
morphism is an identity (that is, if we can "untangle" the braid above
by pulling the strands through each other), then we have a **symmetric
monoidal category**, and it does not matter which direction we braid in.

Our definition of a braided *monoidal category* is not complete yet: we
also require coherences saying that the braiding interacts nicely with
the associator, in the sense that the following hexagon commutes:

~~~{.quiver}
\[\begin{tikzcd}
  & {A \otimes (B \otimes C)} & {(B \otimes C) \otimes A} \\
  {(A \otimes B) \otimes C} &&& {B \otimes (C \otimes A)} \\
  & {(B \otimes A) \otimes C} & {B \otimes (A \otimes C)}
  \arrow["{\beta \otimes C}"', from=2-1, to=3-2]
  \arrow["\alpha"', from=3-2, to=3-3]
  \arrow["{B \otimes \beta}"', from=3-3, to=2-4]
  \arrow["\alpha", from=2-1, to=1-2]
  \arrow["\beta", from=1-2, to=1-3]
  \arrow["\alpha", from=1-3, to=2-4]
\end{tikzcd}\]
~~~

```agda
  field
    braiding-α→ : ∀ {A B C}
      → (id ⊗₁ β→) ∘ α→ B A C ∘ (β→ ⊗₁ id) ≡ α→ B C A ∘ β→ ∘ α→ A B C
```

If the braiding is symmetric, then we're done. However, in general we
also need a *second* hexagon expressing the same condition with the
"backwards" braiding (or, equivalently, with the braiding and the
backwards associator), which might not be the same as the forward
braiding.

```agda
  field
    unbraiding-α→ : ∀ {A B C}
      → (id ⊗₁ β←) ∘ α→ B A C ∘ (β← ⊗₁ id) ≡ α→ B C A ∘ β← ∘ α→ A B C
```

<!--
```agda
  β←-α← : ∀ {A B C}
    → (β← ⊗₁ id) ∘ α← B A C ∘ (id ⊗₁ β←) ≡ α← A B C ∘ β← ∘ α← B C A
  β←-α← = inverse-unique₀
    (◀.F-map-iso β≅ ∙Iso α≅ ∙Iso ▶.F-map-iso β≅)
    (α≅ ∙Iso β≅ ∙Iso α≅)
    (sym (assoc _ _ _) ∙∙ braiding-α→ ∙∙ assoc _ _ _)
```
-->

A symmetric monoidal category simply bundles up a braided monoidal
category with the property that its braiding is symmetric.

```agda
is-symmetric-braiding : -⊗- ≅ⁿ Flip -⊗- → Type (o ⊔ ℓ)
is-symmetric-braiding braiding = ∀ {A B} → β→ ∘ β→ {A} {B} ≡ id
  where
    β→ : ∀ {A B} → Hom (A ⊗ B) (B ⊗ A)
    β→ = braiding .Isoⁿ.to ._=>_.η _

record Symmetric-monoidal : Type (o ⊔ ℓ) where
  field
    Cᵇ : Braided-monoidal

  open Braided-monoidal Cᵇ hiding (β≅) public

  field
    has-is-symmetric : is-symmetric-braiding braiding

  β≅ : ∀ {A B} → A ⊗ B ≅ B ⊗ A
  β≅ = make-iso β→ β→ has-is-symmetric has-is-symmetric
```

In order to *construct* a symmetric monoidal category, as we discussed
above, it is sufficient to give one of the hexagons: the other one
follows by uniqueness of inverses.

```agda
record make-symmetric-monoidal : Type (o ⊔ ℓ) where
  field
    has-braiding : -⊗- ≅ⁿ Flip -⊗-
    symmetric : is-symmetric-braiding has-braiding
```

<!--
```agda
  β→ : ∀ {A B} → Hom (A ⊗ B) (B ⊗ A)
  β→ = has-braiding .Isoⁿ.to ._=>_.η _
  β← : ∀ {A B} → Hom (A ⊗ B) (B ⊗ A)
  β← = has-braiding .Isoⁿ.from ._=>_.η _

  β→≡β← : Path (∀ {A B} → Hom (A ⊗ B) (B ⊗ A)) β→ β←
  β→≡β← = ext λ {_} {_} → inverse-unique₀
    (make-iso β→ β→ symmetric symmetric)
    (isoⁿ→iso has-braiding _)
    refl

  open Braided-monoidal hiding (β→)
  open Symmetric-monoidal hiding (β→)
```
-->

```agda
  field
    has-braiding-α→ : ∀ {A B C}
      → (id ⊗₁ β→) ∘ α→ B A C ∘ (β→ ⊗₁ id) ≡ α→ B C A ∘ β→ ∘ α→ A B C

  to-symmetric-monoidal : Symmetric-monoidal
  to-symmetric-monoidal .Cᵇ .braiding = has-braiding
  to-symmetric-monoidal .Cᵇ .braiding-α→ = has-braiding-α→
  to-symmetric-monoidal .Cᵇ .unbraiding-α→ {A} {B} {C} =
    subst (λ β → (id ⊗₁ β {_} {_}) ∘ α→ B A C ∘ (β {_} {_} ⊗₁ id) ≡ α→ _ _ _ ∘ β {_} {_} ∘ α→ _ _ _)
      β→≡β← has-braiding-α→
  to-symmetric-monoidal .has-is-symmetric = symmetric

open make-symmetric-monoidal using (to-symmetric-monoidal) public
```

## Properties

<!--
```agda
module Braided (Cᵇ : Braided-monoidal) where
  open Braided-monoidal Cᵇ public
```
-->

Just like with [[monoidal categories]], the two hexagons relating the
braiding with the associator automatically give us a whole lot of extra
coherence, but it still takes a bit of work.

::: {.definition #yang-baxter-equation}
We start by proving the **Yang-Baxter equation**, which says,
pictorially, that the following two ways of going from $A \otimes B
\otimes C$ to $C \otimes B \otimes A$ are the same:
:::

<div class="mathpar">

~~~{.quiver}
\begin{tikzpicture}[
  braid/.cd,
  gap=.15,
  every strand/.style={ultra thick},
  strand 1/.style={cyan},
  strand 2/.style={diagramfg},
  strand 3/.style={magenta}
]
  \pic (braid) {braid={s_1^{-1} s_2^{-1} s_1^{-1}}};
  \node[above,color=diagramfg,at=(braid-1-s)] {$A$};
  \node[below,color=diagramfg,at=(braid-1-e)] {$A$};
  \node[above,color=diagramfg,at=(braid-2-s)] {$B$};
  \node[below,color=diagramfg,at=(braid-2-e)] {$B$};
  \node[above,color=diagramfg,at=(braid-3-s)] {$C$};
  \node[below,color=diagramfg,at=(braid-3-e)] {$C$};
\end{tikzpicture}
~~~

$\equiv$

~~~{.quiver}
\begin{tikzpicture}[
  braid/.cd,
  gap=.15,
  every strand/.style={ultra thick},
  strand 1/.style={cyan},
  strand 2/.style={diagramfg},
  strand 3/.style={magenta}
]
  \pic (braid) {braid={s_2^{-1} s_1^{-1} s_2^{-1}}};
  \node[above,color=diagramfg,at=(braid-1-s)] {$A$};
  \node[below,color=diagramfg,at=(braid-1-e)] {$A$};
  \node[above,color=diagramfg,at=(braid-2-s)] {$B$};
  \node[below,color=diagramfg,at=(braid-2-e)] {$B$};
  \node[above,color=diagramfg,at=(braid-3-s)] {$C$};
  \node[below,color=diagramfg,at=(braid-3-e)] {$C$};
\end{tikzpicture}
~~~

</div>

That is, morally, $(\id \otimes \beta) \circ (\beta \otimes \id) \circ
(\id \otimes \beta) \equiv (\beta \otimes \id) \circ (\id \otimes \beta)
\circ (\beta \otimes \id)$, except we have to insert associators
*everywhere* in order for this equation to make sense.

```agda
  yang-baxter : ∀ {A B C}
    → (id ⊗₁ β→) ∘ α→ C A B ∘ (β→ ⊗₁ id) ∘ α← A C B ∘ (id ⊗₁ β→) ∘ α→ A B C
    ≡ α→ C B A ∘ (β→ ⊗₁ id) ∘ α← B C A ∘ (id ⊗₁ β→) ∘ α→ B A C ∘ (β→ ⊗₁ id)
  yang-baxter =
    (id ⊗₁ β→) ∘ α→ _ _ _ ∘ (β→ ⊗₁ id) ∘ α← _ _ _ ∘ (id ⊗₁ β→) ∘ α→ _ _ _   ≡⟨ pushr (pushr refl) ⟩
    ((id ⊗₁ β→) ∘ α→ _ _ _ ∘ (β→ ⊗₁ id)) ∘ α← _ _ _ ∘ (id ⊗₁ β→) ∘ α→ _ _ _ ≡⟨ extendl (rswizzle (braiding-α→ ∙ assoc _ _ _) (α≅ .invl)) ⟩
    α→ _ _ _ ∘ β→ ∘ (id ⊗₁ β→) ∘ α→ _ _ _                                   ≡⟨ refl⟩∘⟨ extendl (β→.is-natural _ _ _) ⟩
    α→ _ _ _ ∘ (β→ ⊗₁ id) ∘ β→ ∘ α→ _ _ _                                   ≡˘⟨ refl⟩∘⟨ refl⟩∘⟨ lswizzle braiding-α→ (α≅ .invr) ⟩
    α→ _ _ _ ∘ (β→ ⊗₁ id) ∘ α← _ _ _ ∘ (id ⊗₁ β→) ∘ α→ _ _ _ ∘ (β→ ⊗₁ id)   ∎
```

We also derive more equations relating the braiding with the associator.

```agda
  β←-β←⊗id-α← : ∀ {A B C} → β← ∘ (β← ⊗₁ id) ∘ α← A B C ≡ α→ C B A ∘ (β← ⊗₁ id) ∘ β←
  β←-β←⊗id-α← =
    β← ∘ (β← ⊗₁ id) ∘ α← _ _ _                     ≡⟨ refl⟩∘⟨ sym (swizzle (sym (assoc _ _ _) ∙ sym unbraiding-α→ ∙ assoc _ _ _) (α≅ .invl) (pullr (▶.cancell (β≅ .invl)) ∙ α≅ .invr)) ⟩
    β← ∘ (α← _ _ _ ∘ (id ⊗₁ β→)) ∘ α→ _ _ _ ∘ β←   ≡⟨ pushr (pullr (pushr refl)) ⟩
    (β← ∘ α← _ _ _) ∘ ((id ⊗₁ β→) ∘ α→ _ _ _) ∘ β← ≡⟨ extendl (sym (swizzle β←-α← (pullr (▶.cancell (β≅ .invr)) ∙ α≅ .invr) (α≅ .invl))) ⟩
    α→ _ _ _ ∘ (β← ⊗₁ id) ∘ β←                     ∎

  β→-id⊗β→-α→ : ∀ {A B C} → β→ ∘ (id ⊗₁ β→) ∘ α→ A B C ≡ α← _ _ _ ∘ β→ ∘ (β→ ⊗₁ id)
  β→-id⊗β→-α→ =
    β→ ∘ (id ⊗₁ β→) ∘ α→ _ _ _   ≡⟨ pulll (β→.is-natural _ _ _) ⟩
    ((β→ ⊗₁ id) ∘ β→) ∘ α→ _ _ _ ≡⟨ swizzle (sym β←-β←⊗id-α← ∙ assoc _ _ _)
      (pullr (cancell (β≅ .invr)) ∙ ◀.annihilate (β≅ .invr))
      (pullr (cancell (β≅ .invl)) ∙ ◀.annihilate (β≅ .invl)) ⟩
    α← _ _ _ ∘ β→ ∘ (β→ ⊗₁ id)   ∎
```

We can also show that the unitors are related to each other via the
braiding, which requires a surprising amount of work.

::: source
These proofs are adapted from [`braiding-coherence⊗unit`][agda-cats] in
the agda-categories library: see there for an explanation and diagram.
:::

[agda-cats]: https://agda.github.io/agda-categories/Categories.Category.Monoidal.Braided.Properties.html#braiding-coherence%E2%8A%97unit

```agda
  λ←-β→ : ∀ {A} → λ← {A} ∘ β→ ≡ ρ←
  λ←-β→ = push-eqⁿ (unitor-r ni⁻¹) $
    (λ← ∘ β→) ⊗₁ id                                ≡⟨ insertl (β≅ .invr) ⟩
    β← ∘ β→ ∘ ((λ← ∘ β→) ⊗₁ id)                    ≡⟨ refl⟩∘⟨ refl⟩∘⟨ ◀.F-∘ _ _ ∙ (sym triangle-λ← ⟩∘⟨refl) ⟩
    β← ∘ β→ ∘ (λ← ∘ α→ _ _ _) ∘ (β→ ⊗₁ id)         ≡⟨ refl⟩∘⟨ extendl (pulll (sym (unitor-l .Isoⁿ.from .is-natural _ _ _))) ⟩
    β← ∘ (λ← ∘ (id ⊗₁ β→)) ∘ α→ _ _ _ ∘ (β→ ⊗₁ id) ≡⟨ refl⟩∘⟨ pullr braiding-α→ ⟩
    β← ∘ λ← ∘ α→ _ _ _ ∘ β→ ∘ α→ _ _ _             ≡⟨ refl⟩∘⟨ pulll triangle-λ← ⟩
    β← ∘ (λ← ⊗₁ id) ∘ β→ ∘ α→ _ _ _                ≡⟨ refl⟩∘⟨ extendl (sym (β→.is-natural _ _ _)) ⟩
    β← ∘ β→ ∘ (id ⊗₁ λ←) ∘ α→ _ _ _                ≡⟨ refl⟩∘⟨ refl⟩∘⟨ triangle-α→ ⟩
    β← ∘ β→ ∘ (ρ← ⊗₁ id)                           ≡⟨ cancell (β≅ .invr) ⟩
    ρ← ⊗₁ id                                       ∎

  λ←-β← : ∀ {A} → λ← {A} ∘ β← ≡ ρ←
  λ←-β← = push-eqⁿ (unitor-r ni⁻¹) $
    (λ← ∘ β←) ⊗₁ id                                ≡⟨ insertl (β≅ .invl) ⟩
    β→ ∘ β← ∘ ((λ← ∘ β←) ⊗₁ id)                    ≡⟨ refl⟩∘⟨ refl⟩∘⟨ ◀.F-∘ _ _ ∙ (sym triangle-λ← ⟩∘⟨refl) ⟩
    β→ ∘ β← ∘ (λ← ∘ α→ _ _ _) ∘ (β← ⊗₁ id)         ≡⟨ refl⟩∘⟨ extendl (pulll (sym (unitor-l .Isoⁿ.from .is-natural _ _ _))) ⟩
    β→ ∘ (λ← ∘ (id ⊗₁ β←)) ∘ α→ _ _ _ ∘ (β← ⊗₁ id) ≡⟨ refl⟩∘⟨ pullr unbraiding-α→ ⟩
    β→ ∘ λ← ∘ α→ _ _ _ ∘ β← ∘ α→ _ _ _             ≡⟨ refl⟩∘⟨ pulll triangle-λ← ⟩
    β→ ∘ (λ← ⊗₁ id) ∘ β← ∘ α→ _ _ _                ≡⟨ refl⟩∘⟨ extendl (sym (β←.is-natural _ _ _)) ⟩
    β→ ∘ β← ∘ (id ⊗₁ λ←) ∘ α→ _ _ _                ≡⟨ refl⟩∘⟨ refl⟩∘⟨ triangle-α→ ⟩
    β→ ∘ β← ∘ (ρ← ⊗₁ id)                           ≡⟨ cancell (β≅ .invl) ⟩
    ρ← ⊗₁ id                                       ∎

  ρ←-β← : ∀ {A} → ρ← {A} ∘ β← ≡ λ←
  ρ←-β← = rswizzle (sym λ←-β→) (β≅ .invl)

  ρ←-β→ : ∀ {A} → ρ← {A} ∘ β→ ≡ λ←
  ρ←-β→ = rswizzle (sym λ←-β←) (β≅ .invr)
```
