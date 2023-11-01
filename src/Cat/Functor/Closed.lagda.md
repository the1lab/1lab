<!--
```agda
open import Cat.Instances.Product
open import Cat.Functor.Base
open import Cat.Prelude

import Cat.Reasoning

open Precategory
open Functor
open _=>_
```
-->

```agda
module Cat.Functor.Closed where
```

<!--
```agda
private variable
  o h o₁ h₁ o₂ h₂ : Level
  B C D E : Precategory o h
  F G : Functor C D
```
-->

When taken as a [(bi)category][cat], the collection of (pre)categories
is, in a suitably weak sense, [[Cartesian closed]]: there is an
[equivalence] between the [functor categories] $[\cC \times \cD, \cE]$
and $[\cC, [\cD, \cE]]$. We do not define the full equivalence here,
leaving the natural isomorphisms aside and focusing on the inverse
functors themselves: `Curry`{.Agda} and `Uncurry`{.Agda}.

[cat]: Cat.Bi.Base.html#the-bicategory-of-categories
[equivalence]: Cat.Functor.Equivalence.html
[functor categories]: Cat.Functor.Base.html

The two conversion functions act on objects essentially in the same way
as currying and uncurrying behave on funct*ions*: the difference is that
we must properly stage the action on morphisms. Currying a functor $F :
\cC \times \cD \to \cE$ fixes a morphism $f : x \to y \in \cC$, and we
must show that $g \mapsto F(f,g)$ is natural in $g$. It follows from a
bit of calculation using the functoriality of $F$.

```agda
Curry : Functor (C ×ᶜ D) E → Functor C Cat[ D , E ]
Curry {C = C} {D = D} {E = E} F = curried where
  open import Cat.Functor.Bifunctor {C = C} {D = D} {E = E} F

  curried : Functor C Cat[ D , E ]
  curried .F₀ = Right
  curried .F₁ x→y = NT (λ f → first x→y) λ x y f →
       sym (F-∘ F _ _)
    ·· ap (F₁ F) (Σ-pathp (C .idr _ ∙ sym (C .idl _)) (D .idl _ ∙ sym (D .idr _)))
    ·· F-∘ F _ _
  curried .F-id = Nat-path λ x → F-id F
  curried .F-∘ f g = Nat-path λ x →
    ap (λ x → F₁ F (_ , x)) (sym (D .idl _)) ∙ F-∘ F _ _

Uncurry : Functor C Cat[ D , E ] → Functor (C ×ᶜ D) E
Uncurry {C = C} {D = D} {E = E} F = uncurried where
  import Cat.Reasoning C as C
  import Cat.Reasoning D as D
  import Cat.Reasoning E as E
  module F = Functor F

  uncurried : Functor (C ×ᶜ D) E
  uncurried .F₀ (c , d) = F₀ (F.₀ c) d
  uncurried .F₁ (f , g) = F.₁ f .η _ E.∘ F₁ (F.₀ _) g
```

The other direction must do slightly more calculation: Given a functor
into functor-categories, and a pair of arguments, we must apply it
twice: but at the level of morphisms, this involves composition in the
codomain category, which throws a fair bit of complication into the
functoriality constraints.

```agda
  uncurried .F-id {x = x , y} = path where abstract
    path : E ._∘_ (F.₁ (C .id) .η y) (F₁ (F.₀ x) (D .id)) ≡ E .id
    path =
      F.₁ C.id .η y E.∘ F₁ (F.₀ x) D.id ≡⟨ E.elimr (F-id (F.₀ x)) ⟩
      F.₁ C.id .η y                     ≡⟨ (λ i → F.F-id i .η y) ⟩
      E.id                              ∎

  uncurried .F-∘ (f , g) (f' , g') = path where abstract
    path : uncurried .F₁ (f C.∘ f' , g D.∘ g')
         ≡ uncurried .F₁ (f , g) E.∘ uncurried .F₁ (f' , g')
    path =
      F.₁ (f C.∘ f') .η _ E.∘ F₁ (F.₀ _) (g D.∘ g')                       ≡˘⟨ E.pulll (λ i → F.F-∘ f f' (~ i) .η _) ⟩
      F.₁ f .η _ E.∘ F.₁ f' .η _ E.∘ ⌜ F₁ (F.₀ _) (g D.∘ g') ⌝            ≡⟨ ap! (F-∘ (F.₀ _) _ _) ⟩
      F.₁ f .η _ E.∘ F.₁ f' .η _ E.∘ F₁ (F.₀ _) g E.∘ F₁ (F.₀ _) g'       ≡⟨ cat! E ⟩
      F.₁ f .η _ E.∘ ⌜ F.₁ f' .η _ E.∘ F₁ (F.₀ _) g ⌝ E.∘ F₁ (F.₀ _) g'   ≡⟨ ap! (F.₁ f' .is-natural _ _ _) ⟩
      F.₁ f .η _ E.∘ (F₁ (F.₀ _) g E.∘ F.₁ f' .η _) E.∘ F₁ (F.₀ _) g'     ≡⟨ cat! E ⟩
      ((F.₁ f .η _ E.∘ F₁ (F.₀ _) g) E.∘ (F.₁ f' .η _ E.∘ F₁ (F.₀ _) g')) ∎
```
