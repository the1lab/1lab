<!--
```agda
open import Cat.Instances.Product
open import Cat.Displayed.Solver
open import Cat.Displayed.Fibre
open import Cat.Displayed.Total
open import Cat.Displayed.Base
open import Cat.Prelude

import Cat.Displayed.Reasoning
```
-->

```agda
module Cat.Functor.Hom.Displayed
  {o ℓ o′ ℓ′} {ℬ : Precategory o ℓ} (ℰ : Displayed ℬ o′ ℓ′)
  where
```

<!--
```agda
open Precategory ℬ
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
Hom-over u .F₁ (f , h) g = hom[ idl _ ∙ idr _ ] (h ∘′ g ∘′ f)
Hom-over u .F-id = funext λ f →
  apr′ {q = idl _} (idr′ f) ∙ idl[]
Hom-over u .F-∘ (f , h) (f' , h') = funext λ g →
  hom[] (hom[] (h ∘′ h') ∘′ g ∘′ hom[] (f' ∘′ f)) ≡⟨ disp! ℰ ⟩
  hom[] (h ∘′ hom[] (h' ∘′ g ∘′ f') ∘′ f) ∎
```

We can also define partially applied versions of this functor.

```agda
Hom-over-from : ∀ {x y} → Hom x y → Ob[ x ] → Functor (Fibre ℰ y) (Sets ℓ′)
Hom-over-from u x′ .F₀ y′ = el (Hom[ u ] x′ y′) (Hom[ u ]-set x′ y′)
Hom-over-from u x′ .F₁ f g = hom[ idl u ] (f ∘′ g)
Hom-over-from u x′ .F-id = funext λ f → idl[]
Hom-over-from u x′ .F-∘ f g  = funext λ h →
  smashl _ _ ∙ sym assoc[] ∙ sym (smashr _ _)

Hom-over-into : ∀ {x y} → Hom x y → Ob[ y ] → Functor (Fibre ℰ x ^op) (Sets ℓ′)
Hom-over-into u y′ .F₀ x′ = el (Hom[ u ] x′ y′) (Hom[ u ]-set x′ y′)
Hom-over-into u y′ .F₁ f g = hom[ idr u ] (g ∘′ f)
Hom-over-into u y′ .F-id = funext λ f → idr[]
Hom-over-into u y′ .F-∘ f g = funext λ h →
  smashr _ _ ∙ assoc[] ∙ (sym $ smashl _ _ )
```
