<!--
```agda
open import Cat.Univalent
open import Cat.Prelude

import Cat.Reasoning as Cat
```
-->

```agda
module Cat.Instances.Discrete.Pre where
```

# Fundamental pregroupoids

<!--
```agda
module _ where
  open Precategory
```
-->

If $X$ is a type with no known [[h-level]], we can not directly define a
[[precategory]] where the type of objects is $X$ and $\hom(x, y)$ is the
type of paths $x \is y$, since we will not know that this type is a
[[set]]. However, we can still define an interesting precategory with
type of objects $X$ by defining $\hom(x, y)$ to be the [[set
truncation]] $\| x \is y \|_0$.

Since under [[Rezk completion]] this precategory presents the "path
groupoid" of the [[groupoid truncation|truncation]] $\| X \|_1$, we
refer to it as the **fundamental pregroupoid** of $X$, and denote it
$\Pi_1(X)$. The naming and notation refers to the [[fundamental groups]]
of $X$. Indeed, if $x : X$ is a point, then the endomorphism space
$\hom_{\Pi_1(X)}(x, x)$ is exactly the fundamental group $\pi_1(X, x)$.

<!--
:::{.definition #fundamental-pregroupoid}
The **fundamental pregroupoid** of a type $X$ is the [[precategory]]
$\Pi_1(X)$ with type of objects $X$, where the [[set]] of morphisms
$$\hom_{\Pi_1}(X)(x, y) = \| x \is y \|_0$$ is given by the [[set
truncation]] of the path space $x \is y$.
:::
-->

```agda
  Π₁ : ∀ {ℓ} → Type ℓ → Precategory ℓ ℓ
  Π₁ X .Ob          = X
  Π₁ X .Hom     x y = ∥ x ≡ y ∥₀
  Π₁ X .Hom-set x y = hlevel 2

  Π₁ X .id      = inc refl
  Π₁ X ._∘_ p q = ⦇ q ∙ p ⦈

  Π₁ X .idr   = elim! λ p     → ap ∥_∥₀.inc (∙-idl p)
  Π₁ X .idl   = elim! λ p     → ap ∥_∥₀.inc (∙-idr p)
  Π₁ X .assoc = elim! λ p q r → ap ∥_∥₀.inc (sym (∙-assoc r q p))
```

<!--
```agda
module _ {ℓx o ℓ} {X : Type ℓx} (C : Precategory o ℓ) where
  open Functor
  open Cat C
```
-->

As for discrete categories, we can extend functions $X \to
\operatorname{Ob}(\cC)$ to functors $\Pi_1(X) \to \cC$. Turning families
of objects into diagrams is the primary motivation for the construction
of $\Pi_1(-)$: if $\operatorname{Ob}(\cC)$ was known to be a groupoid,
we could replace $X$ with its groupoid truncation, and use the ordinary
"discrete category" construction as the domain of the diagram; but since
we will not be able to eliminate $\| X \|_1$ in general, we have to
choose a different domain instead.

```agda
  Π₁-adjunct₁ : {x y : X} (F : X → ⌞ C ⌟) → ∥ x ≡ y ∥₀ → Hom (F x) (F y)
  Π₁-adjunct₁ F (inc x) = path→iso (ap F x) .to
  Π₁-adjunct₁ F (squash x y p q i j) = Hom-set _ _
    (Π₁-adjunct₁ F x) (Π₁-adjunct₁ F y)
    (λ i → Π₁-adjunct₁ F (p i)) (λ i → Π₁-adjunct₁ F (q i)) i j

  Π₁-adjunct : (X → ⌞ C ⌟) → Functor (Π₁ X) C
  Π₁-adjunct F .F₀   = F
  Π₁-adjunct F .F₁   = Π₁-adjunct₁ F
  Π₁-adjunct F .F-id = transport-refl _
  Π₁-adjunct F .F-∘ {x = x} = elim! λ p q →
    path→iso (ap F (q ∙ p)) .to                     ≡⟨ ap (λ e → subst (Hom (F x)) e id) (ap-∙ F q p) ⟩
    path→iso (ap F q ∙ ap F p) .to                  ≡⟨ path→to-∙ C (ap F q) (ap F p) ⟩
    (path→iso (ap F p) .to ∘ path→iso (ap F q) .to) ∎
```
