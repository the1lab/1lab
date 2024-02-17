<!--
```agda
open import Cat.Instances.Product
open import Cat.Prelude
```
-->

```agda
module Cat.Functor.Bifunctor
  {o₁ h₁ o₂ h₂ o₃ h₃ : _}
  {C : Precategory o₁ h₁}
  {D : Precategory o₂ h₂}
  {E : Precategory o₃ h₃}
  (F : Functor (C ×ᶜ D) E)
  where
```

# Bifunctors

<!--
```agda
private
  module C = Precategory C
  module D = Precategory D
  module E = Precategory E

open Functor F public
```
-->

The word **bifunctor** is a term of endearment for "functors out of a
product category". They're named after bilinear maps, to evoke the idea
that a functor out of $\cC \times \cD$ is functorial in each of its
arguments. Correspondingly we have the operations `first`{.Agda} and
`second`{.Agda}, altering one coordinate and leaving the other fixed.

```agda
first : ∀ {a b} {x} → C.Hom a b → E.Hom (F₀ (a , x)) (F₀ (b , x))
first f = F₁ (f , D.id)

second : ∀ {a b} {x} → D.Hom a b → E.Hom (F₀ (x , a)) (F₀ (x , b))
second f = F₁ (C.id , f)
```

These operations behave functorially by themselves, and you can "push
second past first".

```agda
first-id : ∀ {a} {x} → first C.id ≡ E.id {F₀ (x , a)}
first-id = F-id

second-id : ∀ {a} {x} → second D.id ≡ E.id {F₀ (x , a)}
second-id = F-id

first∘first : ∀ {a b c} {x} {f : C.Hom b c} {g : C.Hom a b}
            → first (f C.∘ g)
            ≡ first {x = x} f E.∘ first g
first∘first {f = f} {g} = sym (
  F₁ (f , D.id) E.∘ F₁ (g , D.id) ≡⟨ sym (F-∘ _ _) ⟩
  F₁ (f C.∘ g , D.id D.∘ D.id)    ≡⟨ ap (λ e → F₁ (f C.∘ g , e)) (D.idl _) ⟩
  F₁ (f C.∘ g , D.id)             ∎
  )

second∘second : ∀ {a b c} {x} {f : D.Hom b c} {g : D.Hom a b}
              → second (f D.∘ g)
              ≡ second {x = x} f E.∘ second g
second∘second {f = f} {g} = sym (
  F₁ (C.id , f) E.∘ F₁ (C.id , g) ≡⟨ sym (F-∘ _ _) ⟩
  F₁ (C.id C.∘ C.id , f D.∘ g)    ≡⟨ ap (λ e → F₁ (e , f D.∘ g)) (C.idl _) ⟩
  F₁ (C.id , f D.∘ g)             ∎
  )

first∘second : ∀ {a b} {x y} {f : C.Hom a b} {g : D.Hom x y}
             → first f E.∘ second g
             ≡ second g E.∘ first f
first∘second {f = f} {g} =
  F₁ (f , D.id) E.∘ F₁ (C.id , g) ≡⟨ sym (F-∘ _ _) ⟩
  F₁ (f C.∘ C.id , D.id D.∘ g)    ≡⟨ ap₂ (λ x y → F₁ (x , y)) (C.idr _ ∙ sym (C.idl _)) (D.idl _ ∙ sym (D.idr _)) ⟩
  F₁ (C.id C.∘ f , g D.∘ D.id)    ≡⟨ F-∘ _ _ ⟩
  F₁ (C.id , g) E.∘ F₁ (f , D.id) ∎
```

Fixing an object in either of the categories gives us a functor which
varies in the other category.

```agda
Left : D.Ob → Functor C E
Left y .Functor.F₀ x = F₀ (x , y)
Left y .Functor.F₁ f = first f
Left y .Functor.F-id = F-id
Left y .Functor.F-∘ f g = first∘first

Right : C.Ob → Functor D E
Right x .Functor.F₀ y = F₀ (x , y)
Right x .Functor.F₁ f = second f
Right x .Functor.F-id = F-id
Right x .Functor.F-∘ f g = second∘second

Flip : Functor (D ×ᶜ C) E
Flip .Functor.F₀ (x , y) = F₀ (y , x)
Flip .Functor.F₁ (x , y) = F₁ (y , x)
Flip .Functor.F-id    = F-id
Flip .Functor.F-∘ f g = F-∘ _ _
```
