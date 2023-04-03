```agda
open import Cat.Instances.Product
open import Cat.Displayed.Solver
open import Cat.Displayed.Fibre
open import Cat.Displayed.Total
open import Cat.Displayed.Base
open import Cat.Prelude

import Cat.Reasoning
import Cat.Displayed.Reasoning

module Cat.Functor.Hom.Displayed
  {o ℓ o′ ℓ′} {ℬ : Precategory o ℓ} (ℰ : Displayed ℬ o′ ℓ′)
  where
```

<!--
```agda
open Cat.Reasoning ℬ
open Displayed ℰ
open Cat.Displayed.Reasoning ℰ
open Functor
```
-->

# Displayed Hom Functors

Let $\cE$ be a displayed category over $\cB$. For every $u : x \to y$
in the base, we can obtain a bifunctor from $\cE_{x}\op \times \cE_{y}$
to $\Sets$, where $\cE_{x}$ denotes the [fibre category] of $\cE$ at $x$.
The action of $(f, h)$ on $g$ is given by $h \circ g \circ f$, just as
in the [non-displayed case].

[bifunctor]: Cat.Functor.Bifunctor.html
[fibre category]: Cat.Displayed.Fibre.html
[non-displayed case]: Cat.Functor.Hom.html

```agda
Hom-over : ∀ {x y} → Hom x y → Functor (Fibre ℰ x ^op ×ᶜ Fibre ℰ y) (Sets ℓ′)
Hom-over u .F₀ (a , b) = el (Hom[ u ] a b) (Hom[ u ]-set a b)
Hom-over u .F₁ (f , h) g =
  hom[ eliml (h .is-id) ∙ elimr (f .is-id) ] (h .vert ∘′ g ∘′ f .vert)
Hom-over u .F-id = funext λ f →
  apr′ {q = idl _} (idr′ f) ∙ idl[]
Hom-over u .F-∘ (f , h) (f' , h') = funext λ g →
  hom[] ((h .vert ∘′ h' .vert) ∘′ g ∘′ (f' .vert ∘′ f .vert)) ≡⟨ disp! ℰ ⟩
  hom[] (h .vert ∘′ hom[] (h' .vert ∘′ g ∘′ f' .vert) ∘′ f .vert) ∎
```

We can also define partially applied versions of this functor.

```agda
Hom-over-from : ∀ {x y} → Hom x y → Ob[ x ] → Functor (Fibre ℰ y) (Sets ℓ′)
Hom-over-from u x′ .F₀ y′ = el! (Hom[ u ] x′ y′)
Hom-over-from u x′ .F₁ f g = hom[ eliml (f .is-id) ] (f .vert ∘′ g)
Hom-over-from u x′ .F-id = funext λ f → idl[]
Hom-over-from u x′ .F-∘ f g  = funext λ h → sym assoc[] ∙ sym (smashr _ _)

Hom-over-into : ∀ {x y} → Hom x y → Ob[ y ] → Functor (Fibre ℰ x ^op) (Sets ℓ′)
Hom-over-into u y′ .F₀ x′ = el! (Hom[ u ] x′ y′)
Hom-over-into u y′ .F₁ f g = hom[ elimr (f .is-id) ] (g ∘′ f .vert)
Hom-over-into u y′ .F-id = funext λ f → idr[]
Hom-over-into u y′ .F-∘ f g = funext λ h → assoc[] ∙ (sym $ smashl _ _ )
```
