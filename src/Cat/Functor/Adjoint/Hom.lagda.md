---
description: |
  We establish a correspondence between adjoint functors in terms of
  units and counits and in terms of satisfying a certain natural
  isomorphism of Hom-sets.
---
```agda
open import Cat.Functor.Adjoint
open import Cat.Prelude

import Cat.Functor.Reasoning as Func
import Cat.Reasoning as Cat

module Cat.Functor.Adjoint.Hom
  {o ℓ o′ ℓ′} {C : Precategory o ℓ} {D : Precategory o′ ℓ′}
  {L : Functor D C} {R : Functor C D}
  where
```

<!--
```agda
private
  module C = Cat C
  module D = Cat D
  module L = Func L
  module R = Func R
open _⊣_
open _=>_
```
-->

# Adjoints as hom-isomorphisms

Recall from the page on [adjoint functors] that an adjoint pair $L
\dashv R$ induces an isomorphism

$$
\hom_\ca{C}(L(x), y) \cong \hom_\ca{D}(x, R(y))
$$

of $\hom$-sets, sending each morphism to its left and right _adjuncts_,
respectively. What that page does not mention is that any functors $L,
R$ with such a correspondence --- as long as the isomorphism is natural
--- actually generates an adjunction $L \dashv R$, with the unit and
counit given by the adjuncts of each identity morphism.

[adjoint functors]: Cat.Functor.Adjoint.html

More precisely, the data we require is an equivalence (of sets) $f :
\hom_\ca{C}(Lx,y) \to \hom_\ca{D}(x,Ry)$ such that the equation

$$
f(g \circ x \circ Lh) = Rg \circ fx \circ h
$$

holds. While this may seem un-motivated, it's really a naturality square
for a transformation between the functors $\hom_\ca{C}(L-,-)$ and
$\hom_\ca{D}(-,R-)$ whose data has been "unfolded" into elementary
terms.

```agda
hom-iso→adjoints
  : (f : ∀ {x y} → C.Hom (L.₀ x) y → D.Hom x (R.₀ y))
  → (eqv : ∀ {x y} → is-equiv (f {x} {y}))
  → ( ∀ {a b c d} (g : C.Hom a b) (h : D.Hom c d) x
    → f (g C.∘ x C.∘ L.₁ h) ≡ R.₁ g D.∘ f x D.∘ h)
  → L ⊣ R
hom-iso→adjoints f f-equiv natural = adj′ where
  f⁻¹ : ∀ {x y} → D.Hom x (R.₀ y) → C.Hom (L.₀ x) y
  f⁻¹ = equiv→inverse f-equiv

  inv-natural : ∀ {a b c d} (g : C.Hom a b) (h : D.Hom c d) x
              → f⁻¹ (R.₁ g D.∘ x D.∘ h) ≡ g C.∘ f⁻¹ x C.∘ L.₁ h
  inv-natural g h x = ap fst $ is-contr→is-prop (f-equiv .is-eqv _)
    (f⁻¹ (R.₁ g D.∘ x D.∘ h) , refl)
    ( g C.∘ f⁻¹ x C.∘ L.₁ h
    , natural _ _ _
    ∙ sym (equiv→section f-equiv _)
    ∙ ap (f ⊙ f⁻¹)
         (D.extendl (ap (R.₁ g D.∘_) (equiv→section f-equiv _))))
```

We do not require an explicit naturality witness for the inverse of $f$,
since if a natural transformation is componentwise invertible, then its
inverse is natural as well. It remains to use our "binaturality" to
compute that $f(\id{id})$ and $f^{-1}(\id{id})$ do indeed give a system
of adjunction units and co-units.

```agda
  adj′ : L ⊣ R
  adj′ .unit .η x = f C.id
  adj′ .unit .is-natural x y h =
    f C.id D.∘ h                    ≡⟨ D.introl R.F-id ⟩
    R.₁ C.id D.∘ f C.id D.∘ h       ≡˘⟨ natural _ _ _ ⟩
    f (C.id C.∘ C.id C.∘ L.₁ h)     ≡⟨ ap f (C.cancell (C.idl _) ∙ C.intror (C.idl _ ∙ L.F-id)) ⟩
    f (L.₁ h C.∘ C.id C.∘ L.₁ D.id) ≡⟨ natural _ _ C.id ⟩
    R.₁ (L.₁ h) D.∘ f C.id D.∘ D.id ≡⟨ D.refl⟩∘⟨ D.idr _ ⟩
    R.₁ (L.₁ h) D.∘ f C.id          ∎
  adj′ .counit .η x = f⁻¹ D.id
  adj′ .counit .is-natural x y f =
    f⁻¹ D.id C.∘ L.₁ (R.₁ f) ≡⟨ C.introl refl ⟩
    C.id C.∘ f⁻¹ D.id C.∘ L.₁ (R.₁ f) ≡˘⟨ inv-natural _ _ _ ⟩
    f⁻¹ (R.₁ C.id D.∘ D.id D.∘ R.₁ f) ≡⟨ ap f⁻¹ (D.cancell (D.idr _ ∙ R.F-id) ∙ D.intror (D.idl _)) ⟩
    f⁻¹ (R.₁ f D.∘ D.id D.∘ D.id)     ≡⟨ inv-natural _ _ _ ⟩
    f C.∘ f⁻¹ D.id C.∘ L.₁ D.id       ≡⟨ C.refl⟩∘⟨ C.elimr L.F-id ⟩
    f C.∘ f⁻¹ D.id                    ∎
  adj′ .zig =
    f⁻¹ D.id C.∘ L.₁ (f C.id)          ≡⟨ C.introl refl ⟩
    C.id C.∘ f⁻¹ D.id C.∘ L.₁ (f C.id) ≡˘⟨ inv-natural _ _ _ ⟩
    f⁻¹ (R.₁ C.id D.∘ D.id D.∘ f C.id) ≡⟨ ap f⁻¹ (D.cancell (D.idr _ ∙ R.F-id)) ⟩
    f⁻¹ (f C.id)                       ≡⟨ equiv→retraction f-equiv _ ⟩
    C.id                               ∎
  adj′ .zag =
    R.₁ (f⁻¹ D.id) D.∘ f C.id          ≡⟨ D.refl⟩∘⟨ D.intror refl ⟩
    R.₁ (f⁻¹ D.id) D.∘ f C.id D.∘ D.id ≡˘⟨ natural _ _ _ ⟩
    f (f⁻¹ D.id C.∘ C.id C.∘ L.₁ D.id) ≡⟨ ap f (C.elimr (C.idl _ ∙ L.F-id)) ⟩
    f (f⁻¹ D.id)                       ≡⟨ equiv→section f-equiv _ ⟩
    D.id                               ∎
