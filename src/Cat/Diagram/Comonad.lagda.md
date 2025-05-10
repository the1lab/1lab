<!--
```agda
open import Cat.Functor.Adjoint
open import Cat.Functor.Base
open import Cat.Prelude

import Cat.Reasoning
```
-->

```agda
module Cat.Diagram.Comonad where
```

<!--
```agda
open Functor
open _=>_

module _ {o ℓ} {C : Precategory o ℓ} where
  open Precategory C
```
-->

# Comonads {defines="comonad"}

A **comonad on a category** $\cC$ is dual to a [[monad]] on $\cC$; instead
of a unit $\Id \To M$ and multiplication $(M \circ M) \To M$, we have a
counit $W \To \Id$ and comultiplication $W \To (W \circ W)$. More
generally, we can define what it means to equip a *fixed* functor $W$
with the structure of a comonad.

```agda
  record Comonad-on (W : Functor C C) : Type (o ⊔ ℓ) where
    field
      counit : W => Id
      comult : W => (W F∘ W)
```

<!--
```agda
    module counit = _=>_ counit renaming (η to ε)
    module comult = _=>_ comult renaming (η to δ)

    open Functor W renaming (F₀ to W₀ ; F₁ to W₁ ; F-id to W-id ; F-∘ to W-∘) public
    open counit using (ε) public
    open comult using (δ) public
```
-->

We also have equations governing the counit and comultiplication.
Unsurprisingly, these are dual to the equations of a monad.

```agda
    field
      δ-unitl : ∀ {x} → W₁ (ε x) ∘ δ x ≡ id
      δ-unitr : ∀ {x} → ε (W₀ x) ∘ δ x ≡ id
      δ-assoc : ∀ {x} → W₁ (δ x) ∘ δ x ≡ δ (W₀ x) ∘ δ x
```

<!--
```agda
module _ {o h : _} {C : Precategory o h} {F G : Functor C C} {M : Comonad-on F} {N : Comonad-on G} where
  private
    module C = Cat.Reasoning C
    module M = Comonad-on M
    module N = Comonad-on N

  Comonad-on-path
    : (p0 : F ≡ G)
    → (∀ x → PathP (λ i → C.Hom (p0 i · x) x) (M.ε x) (N.ε x))
    → (∀ x → PathP (λ i → C.Hom (p0 i · x) (p0 i · (p0 i · x))) (M.δ x) (N.δ x))
    → PathP (λ i → Comonad-on (p0 i)) M N
  Comonad-on-path M=N pcounit pcomult = path where
    p0 : ∀ x → F · x ≡ G · x
    p0 x i = M=N i · x

    p1 : ∀ {x y} (f : C.Hom x y) → PathP (λ i → C.Hom (p0 x i) (p0 y i)) (M.W₁ f) (N.W₁ f)
    p1 f i = M=N i .Functor.F₁ f

    path : PathP (λ i → Comonad-on (M=N i)) M N
    path i .Comonad-on.counit =
      Nat-pathp M=N refl {a = M.counit} {b = N.counit} pcounit i
    path i .Comonad-on.comult =
      Nat-pathp M=N (ap₂ _F∘_ M=N M=N) {a = M.comult} {b = N.comult} pcomult i
    path i .Comonad-on.δ-unitl {x = x} =
      is-prop→pathp (λ i → C.Hom-set (p0 x i) (p0 x i) (p1 (pcounit x i) i C.∘ pcomult x i) C.id)
        M.δ-unitl N.δ-unitl i
    path i .Comonad-on.δ-unitr {x = x} =
      is-prop→pathp (λ i → C.Hom-set (p0 x i) (p0 x i) (pcounit (p0 x i) i C.∘ pcomult x i) C.id)
        M.δ-unitr N.δ-unitr i
    path i .Comonad-on.δ-assoc {x} =
      is-prop→pathp (λ i → C.Hom-set (p0 x i) (p0 (p0 (p0 x i) i) i) (p1 (pcomult x i) i C.∘ pcomult x i) (pcomult (p0 x i) i C.∘ pcomult x i))
        M.δ-assoc N.δ-assoc i
```
-->
