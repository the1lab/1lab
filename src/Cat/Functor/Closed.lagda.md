<!--
```agda
open import 1Lab.Path.Cartesian

open import Cat.Instances.Product
open import Cat.Functor.Base
open import Cat.Prelude

import Cat.Functor.Reasoning as Fr
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

  uncurried .F-id {x = x , y} = path where abstract
    path : E ._∘_ (F.₁ (C .id) .η y) (F₁ (F.₀ x) (D .id)) ≡ E .id
    path =
      F.₁ C.id .η y E.∘ F₁ (F.₀ x) D.id ≡⟨ E.elimr (F-id (F.₀ x)) ⟩
      F.₁ C.id .η y                     ≡⟨ (λ i → F.F-id i .η y) ⟩
      E.id                              ∎

  uncurried .F-∘ (f , g) (f′ , g′) = path where abstract
    path : uncurried .F₁ (f C.∘ f′ , g D.∘ g′)
         ≡ uncurried .F₁ (f , g) E.∘ uncurried .F₁ (f′ , g′)
    path =
      F.₁ (f C.∘ f′) .η _ E.∘ F₁ (F.₀ _) (g D.∘ g′)                       ≡˘⟨ E.pulll (λ i → F.F-∘ f f′ (~ i) .η _) ⟩
      F.₁ f .η _ E.∘ F.₁ f′ .η _ E.∘ ⌜ F₁ (F.₀ _) (g D.∘ g′) ⌝            ≡⟨ ap! (F-∘ (F.₀ _) _ _) ⟩
      F.₁ f .η _ E.∘ F.₁ f′ .η _ E.∘ F₁ (F.₀ _) g E.∘ F₁ (F.₀ _) g′       ≡⟨ cat! E ⟩
      F.₁ f .η _ E.∘ ⌜ F.₁ f′ .η _ E.∘ F₁ (F.₀ _) g ⌝ E.∘ F₁ (F.₀ _) g′   ≡⟨ ap! (F.₁ f′ .is-natural _ _ _) ⟩
      F.₁ f .η _ E.∘ (F₁ (F.₀ _) g E.∘ F.₁ f′ .η _) E.∘ F₁ (F.₀ _) g′     ≡⟨ cat! E ⟩
      ((F.₁ f .η _ E.∘ F₁ (F.₀ _) g) E.∘ (F.₁ f′ .η _ E.∘ F₁ (F.₀ _) g′)) ∎
```
