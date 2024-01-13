<!--
```agda
open import Cat.Functor.Naturality
open import Cat.Functor.Base
open import Cat.Prelude

import Cat.Reasoning
import Cat.Univalent
```
-->

```agda
module Cat.Functor.Univalence  where
```

<!--
```agda
private variable
  o ℓ o₁ ℓ₁ : Level
  C D : Precategory o ℓ
open Precategory
open Functor
open _=>_
```
-->

Our previous results about [paths between functors][pbf], [componentwise
invertibility], and general reasoning in [[univalent categories]]
assemble into the following very straightforward proof that $[\cC,\cD]$
is univalent whenever $\cD$ is.

[pbf]: Cat.Functor.Base.html#paths-between-functors
[componentwise invertibility]: Cat.Functor.Naturality.html

```agda
Functor-is-category : is-category D → is-category Cat[ C , D ]
Functor-is-category {D = D} {C = C} d-cat .to-path {F} {G} im =
  Functor-path (λ x → d-cat .to-path (isoⁿ→iso im x)) coh
  where
    open Univalent d-cat using (Hom-pathp-iso ; pulll ; cancelr)
    abstract
      coh : ∀ {x y : C .Ob} (f : C .Hom x y)
          → PathP (λ i → D .Hom (d-cat .to-path (isoⁿ→iso im x) i) (d-cat .to-path (isoⁿ→iso im y) i))
              (F .F₁ f) (G .F₁ f)
      coh f = Hom-pathp-iso ( pulll (Isoⁿ.to im .is-natural _ _ _)
                            ∙ cancelr (Isoⁿ.invl im ηₚ _))
Functor-is-category {D = D} d-cat .to-path-over p =
  ≅ⁿ-pathp _ _ (λ x → Hom-pathp-reflr-iso (Precategory.idr D (Isoⁿ.to p .η x)))
  where open Univalent d-cat
```

<!--
```agda
module _
  {o ℓ o' ℓ' o₂ ℓ₂}
  {C : Precategory o ℓ}
  {D : Precategory o' ℓ'}
  {E : Precategory o₂ ℓ₂}
  where
  private
    de = Cat[ D , E ]
    cd = Cat[ C , D ]
  open Cat.Reasoning using (to ; from)
  open Cat.Univalent

  whisker-path-left
    : ∀ {G G' : Functor D E} {F : Functor C D}
        (ecat : is-category de)
    → (p : G ≅ⁿ G') → ∀ {x}
    → path→iso {C = E} (λ i → (Univalent.iso→path ecat p i F∘ F) .F₀ x) .to
    ≡ p .to .η (F₀ F x)
  whisker-path-left {G} {G'} {F} p =
    de.J-iso
      (λ B isom → ∀ {x} → path→iso {C = E} (λ i → F₀ (de.iso→path isom i F∘ F) x) .to ≡ isom .to .η (F₀ F x))
      λ {x} → ap (λ e → path→iso {C = E} e .to)
        (λ i j → de.iso→path-id {a = G} i j .F₀ (F₀ F x))
        ∙ transport-refl _
    where module de = Univalent p

  whisker-path-right
    : ∀ {G : Functor D E} {F F' : Functor C D}
        (cdcat : is-category cd)
    → (p : F ≅ⁿ F') → ∀ {x}
    → path→iso {C = E} (λ i → F₀ G (Univalent.iso→path cdcat p i .F₀ x)) .from
    ≡ G .F₁ (p .from .η x)
  whisker-path-right {G} {G'} {F} cdcat =
    cd.J-iso
      (λ B isom → ∀ {x} → path→iso {C = E} (λ i → F₀ G (cd.iso→path isom i .F₀ x)) .from ≡ G .F₁ (isom .from .η x))
      λ {x} → ap (λ e → path→iso {C = E} e .from)
        (λ i j → G .F₀ (cd.iso→path-id {a = G'} i j .F₀ x))
        ∙ transport-refl _ ∙ sym (G .F-id)
    where module cd = Univalent cdcat

```
-->
