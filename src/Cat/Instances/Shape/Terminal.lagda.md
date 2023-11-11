<!--
```agda
open import 1Lab.Prelude

open import Cat.Functor.Naturality
open import Cat.Functor.Base
open import Cat.Base

import Cat.Reasoning
```
-->

```agda
module Cat.Instances.Shape.Terminal where
```

<!--
```agda
open Precategory
```
-->

:::{.definition #terminal-category}
The **terminal category** is the category with a single object, and only
trivial morphisms.
:::

```agda
⊤Cat : Precategory lzero lzero
⊤Cat .Ob = ⊤
⊤Cat .Hom _ _ = ⊤
⊤Cat .Hom-set _ _ _ _ _ _ _ _ = tt
⊤Cat .Precategory.id = tt
⊤Cat .Precategory._∘_ _ _ = tt
⊤Cat .idr _ _ = tt
⊤Cat .idl _ _ = tt
⊤Cat .assoc _ _ _ _ = tt

module _ {o h} {A : Precategory o h} where
  private module A = Precategory A
  open Functor

  const! : Ob A → Functor ⊤Cat A
  const! = Const

  !F : Functor A ⊤Cat
  !F .F₀ _ = tt
  !F .F₁ _ = tt
  !F .F-id = refl
  !F .F-∘ _ _ = refl

  const-η : ∀ (F G : Functor ⊤Cat A) → F .F₀ tt ≡ G .F₀ tt → F ≡ G
  const-η F G p =
    Functor-path
      (λ _ → p)
      (λ _ i → hcomp (∂ i) λ where
        j (i = i0) → F .F-id (~ j)
        j (i = i1) → G .F-id (~ j)
        j (j = i0) → A.id)
```


Natural isomorphisms between functors $\top \to \cC$
correspond to isomorphisms in $\cC$.

```agda
module _ {o ℓ} {𝒞 : Precategory o ℓ} {F G : Functor ⊤Cat 𝒞} where
  private
    module 𝒞 = Cat.Reasoning 𝒞
    open Functor
    open _=>_

  hom→⊤-natural-trans : 𝒞.Hom (F .F₀ tt) (G .F₀ tt) → F => G
  hom→⊤-natural-trans f .η _ = f
  hom→⊤-natural-trans f .is-natural _ _ _ = 𝒞.elimr (F .F-id) ∙ 𝒞.introl (G .F-id)

  iso→⊤-natural-iso : F .F₀ tt 𝒞.≅ G .F₀ tt → F ≅ⁿ G
  iso→⊤-natural-iso i = iso→isoⁿ (λ _ → i) λ _ → 𝒞.eliml (G .F-id) ∙ 𝒞.intror (F .F-id)
```

<!--
```agda
module _ {o ℓ o' ℓ'} {𝒞 : Precategory o ℓ} {𝒟 : Precategory o' ℓ'} where
  private
    module 𝒟 = Precategory 𝒟
    open Functor
    open _=>_

  idnat-constr
    : ∀ {M : Functor ⊤Cat 𝒟}
    → M F∘ !F => Const {C = 𝒞} (M .F₀ tt)
  idnat-constr .η _ = 𝒟.id
  idnat-constr {M = M} .is-natural _ _ _ = ap (𝒟.id 𝒟.∘_) (M .F-id)
```
-->
