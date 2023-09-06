<!--
```agda
open import Cat.Diagram.Limit.Finite
open import Cat.Diagram.Pullback
open import Cat.Diagram.Product
open import Cat.Prelude

import Cat.Diagram.Congruence
import Cat.Internal.Base
import Cat.Reasoning
```
-->

```agda
module Cat.Internal.Instances.Congruence
  {o ℓ} {C : Precategory o ℓ}
  (fc : Finitely-complete C)
  where
```

<!--
```agda
open Cat.Diagram.Congruence fc
open Cat.Internal.Base C
open Cat.Reasoning C
private module fc = Finitely-complete fc
open Pullbacks C fc.pullbacks
open Binary-products C fc.products

open Internal-cat
open Internal-cat-on
open Internal-hom
```
-->

# Internal categories from congruences

Let $\cC$ be a [[finitely complete category]], and recall that a
[congruence] in $\cC$ is an internalized notion of equivalence relation.
Intuitively, we should be able to turn this into an internal category,
where we have an internal morphism $x \to y$ if and only if $x$ and $y$
are congruent.

[congruence]: Cat.Diagram.Congruence.html

```agda
EquivRel : ∀ {A} → Congruence-on A → Internal-cat
EquivRel {A} cong = icat where
  open Congruence-on cong
  private module R×R = Pullback (fc.pullbacks rel₁ rel₂)
```

The object of objects of the internal category will simply be $A$, and
the object of morphisms is given by the subobject of $A \times A$
associated with the congruence. The source and target maps are given by
projections from the aforementioned subobject.

```agda
  icat : Internal-cat
  icat .C₀ = A
  icat .C₁ = domain
  icat .src = rel₁
  icat .tgt = rel₂
```

As aluded to earlier, the identity morphism is given by reflexivity, and
composition by transitivity.

```agda
  icat .has-internal-cat .idi x .ihom = has-refl ∘ x
  icat .has-internal-cat .idi x .has-src = cancell refl-p₁
  icat .has-internal-cat .idi x .has-tgt = cancell refl-p₂
  icat .has-internal-cat ._∘i_ f g .ihom =
    has-trans ∘ pullback.universal _ _ (f .has-src ∙ sym (g .has-tgt))
  icat .has-internal-cat ._∘i_ f g .has-src =
       pulll trans-p₁
    ·· pullr R×R.p₂∘universal
    ·· g .has-src
  icat .has-internal-cat ._∘i_ f g .has-tgt =
       pulll trans-p₂
    ·· pullr R×R.p₁∘universal
    ·· f .has-tgt
```

<details>
<summary>Proving the category equations is an exercise in shuffling
around products and pullbacks.
</summary>

```agda
  icat .has-internal-cat .idli {x = x} {y = y} f =
    Internal-hom-path $
    has-is-monic _ _ $
    inclusion ∘ has-trans ∘ R×R.universal _  ≡⟨ unpair-trans _ ⟩
    ⟨ rel₁ ∘ f .ihom , rel₂ ∘ has-refl ∘ y ⟩ ≡⟨ ap₂ ⟨_,_⟩ (f .has-src) (pulll refl-p₂ ∙ idl _) ⟩
    ⟨ x , y ⟩                                ≡˘⟨ ⟨⟩-unique _ (assoc _ _ _ ∙ f .has-src) (assoc _ _ _ ∙ f .has-tgt) ⟩
    inclusion ∘ f .ihom                      ∎
  icat .has-internal-cat .idri {x = x} {y = y} f =
    Internal-hom-path $
    has-is-monic _ _ $
    inclusion ∘ has-trans ∘ R×R.universal _  ≡⟨ unpair-trans _ ⟩
    ⟨ rel₁ ∘ has-refl ∘ x , rel₂ ∘ f .ihom ⟩ ≡⟨ ap₂ ⟨_,_⟩ (pulll refl-p₁ ∙ idl _) (f .has-tgt) ⟩
    ⟨ x , y ⟩                                ≡˘⟨ ⟨⟩-unique _ (assoc _ _ _ ∙ f .has-src) (assoc _ _ _ ∙ f .has-tgt) ⟩
    inclusion ∘ f .ihom ∎
  icat .has-internal-cat .associ {w = w} {x = x} {y = y} {z = z} f g h =
    Internal-hom-path $
    has-is-monic _ _ $
    inclusion ∘ has-trans ∘ R×R.universal _                 ≡⟨ unpair-trans _ ⟩
    ⟨ rel₁ ∘ has-trans ∘ R×R.universal _ , rel₂ ∘ f .ihom ⟩ ≡⟨ ap₂ ⟨_,_⟩ (pulll trans-p₁ ∙ pullr R×R.p₂∘universal) refl ⟩
    ⟨ rel₁ ∘ h .ihom , rel₂ ∘ f .ihom ⟩                     ≡˘⟨ ap₂ ⟨_,_⟩ refl (pulll trans-p₂ ∙ pullr R×R.p₁∘universal) ⟩
    ⟨ rel₁ ∘ h .ihom , rel₂ ∘ has-trans ∘ R×R.universal _ ⟩ ≡˘⟨ unpair-trans _ ⟩
    inclusion ∘ has-trans ∘ R×R.universal _ ∎
  icat .has-internal-cat .idi-nat σ =
    Internal-hom-path (sym (assoc _ _ _))
  icat .has-internal-cat .∘i-nat f g σ =
    Internal-hom-path $
    sym (assoc _ _ _)
    ∙ ap (has-trans ∘_) (R×R.unique (pulll R×R.p₁∘universal) (pulll R×R.p₂∘universal))
```
</details>
