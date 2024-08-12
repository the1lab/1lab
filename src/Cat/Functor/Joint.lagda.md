---
description: |
  We generalize properties of functors to families of functors.
---
<!--
```agda
open import Cat.Functor.Conservative
open import Cat.Functor.Naturality
open import Cat.Functor.Properties
open import Cat.Functor.Base
open import Cat.Prelude

import Cat.Reasoning
```
-->
```agda
module Cat.Functor.Joint where
```

<!--
```agda
private variable
  o h o₁ h₁ iℓ : Level
  C D K : Precategory o h
  Idx : Type iℓ
open Functor
open _=>_
```
-->

# Families of functors

This module generalizes properties of functors (fullness, faithfulness,
conservativity, etc.) to families of functors $F_i : \cC \to \cD$.
For the rest of this section we will fix a family of functors
$F_i : \cC \to \cD$.

```agda
Swap : Functor K Cat[ C , D ] → Functor C Cat[ K , D ]
Swap F .F₀ c .F₀ k = F .F₀ k .F₀ c
Swap F .F₀ c .F₁ f = F .F₁ f .η c
Swap F .F₀ c .F-id = F .F-id ηₚ c
Swap F .F₀ c .F-∘ f g = F .F-∘ f g ηₚ c
Swap F .F₁ f .η k = F .F₀ k .F₁ f
Swap F .F₁ f .is-natural x y g = sym (F .F₁ g .is-natural _ _ f)
Swap F .F-id = ext λ k → F .F₀ k .F-id
Swap F .F-∘ f g = ext λ k → F .F₀ k .F-∘ f g

module _
  {oc ℓc od ℓd}
  {C : Precategory oc ℓc}
  {D : Precategory od ℓd}
  where
  private
    module C = Cat.Reasoning C
    module D = Cat.Reasoning D
```

:::{.definition #jointly-faithful-functors alias="jointly-faithful"}
A family of functors $F_i : \cC \to \cD$ is **jointly faithful** when:
- For any $f, g : \cC(x,y)$, if $F_i(f) = F_i(g)$ for every $I$, then
$f = g$
:::

```agda
  is-jointly-faithful : (Idx → Functor C D) → Type _
  is-jointly-faithful Fᵢ =
    ∀ {x y} {f g : C.Hom x y} → (∀ i → Fᵢ i .F₁ f ≡ Fᵢ i .F₁ g) → f ≡ g
```

The canonical example of a family of jointly faithful functors are the
family of hom-functors $\hat{C}(\yo(A), -)$, indexed by objects of $A$:
this is a restatment of the [[coyoneda lemma]].

Note that every functor $F : \cI \to [\cC, \cD]$ induces a family of
functors via the mapping on objects: this family is jointly faithful
precisely when $\hat{F} : \cC \to [\cI, \cD]$ is faithful.

```agda
  swap-faithful→jointly-faithful
    : (F : Functor K Cat[ C , D ])
    → is-faithful (Swap F)
    → is-jointly-faithful (F .F₀)
  swap-faithful→jointly-faithful F faithful p = faithful (ext p)

  jointly-faithful→swap-faithful
    : (F : Functor K Cat[ C , D ])
    → is-jointly-faithful (F .F₀)
    → is-faithful (Swap F)
  jointly-faithful→swap-faithful F joint p = joint (λ i → p ηₚ i)
```

## Jointly conservative functors

:::{.definition #jointly-conservative-functors alias="jointly-conservative"}
A family of functors $F_i : \cC \to \cD$ is **jointly conservative** when:
- For $f : \cC(x,y)$, if $F_i(f)$ is an iso for every $i$, then $f$ is an iso.
:::

```agda
  is-jointly-conservative : (Idx → Functor C D) → Type _
  is-jointly-conservative Fᵢ =
    ∀ {x y} {f : C.Hom x y} → (∀ i → D.is-invertible (Fᵢ i .F₁ f)) → C.is-invertible f
```

We can also rephrase joint-conservativity as a property of a diagram
$F : \cI \to [ \cC, \cD ]$.

```agda
  swap-conservative→jointly-conservative
    : (F : Functor K Cat[ C , D ])
    → is-conservative (Swap F)
    → is-jointly-conservative (F .F₀)
  swap-conservative→jointly-conservative F reflect-iso isos =
    reflect-iso (invertible→invertibleⁿ (Swap F .F₁ _) isos)

  jointly-conservative→swap-conservative
    : (F : Functor K Cat[ C , D ])
    → is-jointly-conservative (F .F₀)
    → is-conservative (Swap F)
  jointly-conservative→swap-conservative F reflect-iso isos =
    reflect-iso (λ i → is-invertibleⁿ→is-invertible isos i)
```


## Jointly full functors

:::{.definition #jointly-full-functors alias="jointy full"}
A diagram of functors $F : \cI \to [\cC, \cD]$ is **jointly full** when
the functor $\hat{F} : \cC \to [\cI, \cD]$ is full. Explicitly, $F$ is
jointly full if a family of morphisms $g_i : \cD(F(i)(x), F(i)(y))$ that is
natural in $i$ implies the mere existence of a $f : \cC(x,y)$ with
$F_i(f) = g_i$.
:::

Note that joint fullness *must* be a property of a diagram of functors,
due to the naturality constraint. This

<!--
```agda
module _
  {oc ℓc od ℓd ok ℓk}
  {C : Precategory oc ℓc}
  {D : Precategory od ℓd}
  {K : Precategory ok ℓk}
  where
  private
    module C = Cat.Reasoning C
    module D = Cat.Reasoning D
    module K = Cat.Reasoning K
```
-->

```agda
  is-jointly-full : Functor K Cat[ C , D ] → Type _
  is-jointly-full F = is-full (Swap F)

  jointly-full-fibre
    : ∀ {x y}
    → (F : Functor K Cat[ C , D ])
    → is-jointly-full F
    → (gᵢ : ∀ i → D.Hom (F .F₀ i .F₀ x) (F .F₀ i .F₀ y))
    → (∀ {i j} (f : K.Hom i j) → gᵢ j D.∘ F .F₁ f .η x ≡ F .F₁ f .η y D.∘ gᵢ i)
    → ∃[ f ∈ C.Hom x y ] (∀ i → F .F₀ i .F₁ f ≡ gᵢ i)
  jointly-full-fibre F joint-full gᵢ gᵢ-nat =
    ∥-∥-map (Σ-map₂ λ p i → p ηₚ i) (joint-full (NT gᵢ λ i j f → gᵢ-nat f))
```


## Jointly fully faithful functors

:::{.definition #jointly-fully-faithful-functors alias="jointly-fully-faithful"}
A diagram of functors $F : \cI \to [\cC, \cD]$ is **jointly fully faithful** when
the functor $\hat{F} : \cC \to [\cI, \cD]$ is fully faithful. Explicitly, $F$ is
jointly faully faithful if there is an equivalence of natural transformations
$\hat{F}(x) \to \hat{F}(y)$ and morphisms $\cC(x,y)$.
:::

```agda
  is-jointly-fully-faithful : Functor K Cat[ C , D ] → Type _
  is-jointly-fully-faithful F = is-fully-faithful (Swap F)
```

If a diagram of functors is jointly fully and jointly faithful, then it is jointly
fully faithful.

```agda
  jointly-full+jointly-faithful→jointly-ff
    : (F : Functor K Cat[ C , D ])
    → is-jointly-full F
    → is-jointly-faithful (F .F₀)
    → is-jointly-fully-faithful F
  jointly-full+jointly-faithful→jointly-ff F full faithful {x} {y} .is-eqv α =
    is-prop∙→is-contr img-is-prop $
    ∥-∥-elim (λ _ → img-is-prop) (Σ-map₂ (λ p → ext p)) $
    jointly-full-fibre F full (λ i → α .η i) (λ f → α .is-natural _ _ f)
    where
      img-is-prop : is-prop (Σ[ f ∈ C.Hom x y ] (Swap F .F₁ f ≡ α))
      img-is-prop (f , p) (g , q) =
        Σ-prop-path (λ f → Nat-is-set (Swap F .F₁ f) α)
          (faithful (λ i → p ηₚ i ∙ sym (q ηₚ i)))
```
