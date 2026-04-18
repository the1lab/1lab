<!--
```agda
open import Cat.Functor.Properties
open import Cat.Displayed.Functor
open import Cat.Displayed.Base
open import Cat.Prelude

import Cat.Displayed.Morphism.Reasoning as Dr
import Cat.Reasoning as Cr
```
-->

```agda
module Cat.Displayed.Functor.Properties
  {oa ℓa ob ℓb oe ℓe of ℓf}
  {A : Precategory oa ℓa} {B : Precategory ob ℓb}
  {ℰ : Displayed A oe ℓe} {ℱ : Displayed B of ℓf}
  where
```

<!--
```agda
private
  module A = Cr A
  module ℰ = Dr ℰ
  module ℱ = Dr ℱ
  variable
    F : Functor A B

open Functor
open Displayed-functor
```
-->

# Properties of displayed functors

This module mirrors the corresponding one for [ordinary functors]
by defining the corresponding classes of [[displayed functors]]. Suppose
$F : \cA \to \cB$ is a functor and $F' : \cE \to_F \cF$ is a displayed
functor over $F$.

```agda
module _ {F} (F' : Displayed-functor F ℰ ℱ) where
```

[ordinary functors]: Cat.Functor.Properties.html

:::{.definition #fully-displayed-functor}
$F'$ is **fully displayed** when its action on hom-sets _over_ any
morphism is surjective:

```agda
  is-full[] : Type _
  is-full[] =
    ∀ {x y f} {x' : ℰ.Ob[ x ]} {y' : ℰ.Ob[ y ]}
    → is-surjective {A = ℰ.Hom[ f ] x' y'} (₁' F')
```
:::

:::{.definition #faithfully-displayed-functor}
$F : \cE$ functor is **faithfully displayed** when its action on hom-sets
_over_ any morphism is injective. The obvious way to write this up is

```agda
  is-fibrewise-injective : Type _
  is-fibrewise-injective =
    ∀ {x y f} {x' : ℰ.Ob[ x ]} {y' : ℰ.Ob[ y ]}
    → injective {A = ℰ.Hom[ f ] x' y'} (₁' F')
```

this form is inconvenient to use, since two displayed morphisms being
compared need definitionally equal base morphisms. Hence we reserve
`is-faithful[]`{.Agda} for a more useful, but logically equivalent form:

```agda
  is-faithful[] : Type _
  is-faithful[] =
    ∀ {x y f g} {f=g : f ≡ g}
      {x' : ℰ.Ob[ x ]} {y' : ℰ.Ob[ y ]}
      {f' : ℰ.Hom[ f ] x' y'} {g' : ℰ.Hom[ g ] x' y'}
    → ₁' F' f' ℱ.≡[ ap (₁ F) f=g ] ₁' F' g'
    → f' ℰ.≡[ f=g ] g'

  fibrewise-injective→faithful[] : is-fibrewise-injective → is-faithful[]
  fibrewise-injective→faithful[] inj' {x} {y} {f} {g} {f=g} =
    J (λ h f=h →
        ∀ {x' : ℰ.Ob[ x ]} {y' : ℰ.Ob[ y ]}
          {f' : ℰ.Hom[ f ] x' y'} {h' : ℰ.Hom[ h ] x' y'}
        → ₁' F' f' ℱ.≡[ ap (₁ F) f=h ] ₁' F' h'
        → f' ℰ.≡[ f=h ] h')
      inj' f=g

  faithful[]→fibrewise-injective[] : is-faithful[] → is-fibrewise-injective
  faithful[]→fibrewise-injective[] faith' = faith'
```
:::

## Fully faithfully displayed functors {defines="fully-faithfully-displayed-functor fully-faithfully-displayed"}

A displayed functor is **fully faithfully displayed** when its action on
hom-sets _over_ any morphism is an equivalence.

```agda
  is-ff[] : Type _
  is-ff[] = ∀ {x y f} {x' : ℰ.Ob[ x ]} {y' : ℰ.Ob[ y ]}
    →  is-equiv {A = ℰ.Hom[ f ] x' y'} (₁' F')

  ff[]→faithful[] : is-ff[] → is-faithful[]
  ff[]→faithful[] ff' =
    fibrewise-injective→faithful[] (Equiv.injective (₁' F' , ff'))

  ff[]→full[] : is-ff[] → is-full[]
  ff[]→full[] ff' f' = inc (equiv→inverse ff' f' , equiv→counit ff' f')

  full[]+faithful[]→ff[] : is-full[] → is-faithful[] → is-ff[]
  full[]+faithful[]→ff[] full' faith' .is-eqv = p where
    img-is-prop : ∀ {x y f} {x' : ℰ.Ob[ x ]} {y' : ℰ.Ob[ y ]} f'
      → is-prop (fibre {A = ℰ.Hom[ f ] x' y'} (₁' F') f')
    img-is-prop f' (g' , p) (h' , q) = Σ-prop-path
      (λ x → ℱ.Hom[ ₁ F _ ]-set (₀' F' _) (₀' F' _) (₁' F' x) f')
      (faith' (p ∙ sym q))

    p : ∀ {x y f} {x' : ℰ.Ob[ x ]} {y' : ℰ.Ob[ y ]} f'
      → is-contr (fibre {A = ℰ.Hom[ f ] x' y'} (₁' F') f')
    p f' .centre = ∥-∥-elim (λ _ → img-is-prop f') (λ x → x) (full' f')
    p f' .paths = img-is-prop f' _
```

### Inverse action

```agda
module ff[ff]
  {F} (F' : Displayed-functor F ℰ ℱ)
  (ff : is-fully-faithful F) (ff' : is-ff[] F')
  where
```

Suppose $F'$ is fully faithfully displayed and $F$ is [[fully
faithful]]. We can then construct an inverse action of $F'$ on displayed
morphisms in $\cF$, that is we can pull back any displayed morphism $f'$
over $f$ in $\cF$ to a unique displayed morphism in $F'^{-1} f'$ in
$\cE$ such  that $F F'^{-1} f'$. However, we must take care to transport
so that the base of $F'^{-1} f'$ agrees with $F^{-1} f$

<!--
```agda
  private
    module F = Functor F
    module F' = Displayed-functor F'
    module F₁ {x} {y} = Equiv (F.₁ , ff {x} {y})
    module F₁' {x} {y} {f} {x'} {y'} = Equiv (F'.₁' , ff' {x} {y} {f} {x'} {y'})
```
-->

```agda
  ff'⁻¹
    : ∀ {x y f} {x' : ℰ.Ob[ x ]} {y' : ℰ.Ob[ y ]}
    → ℱ.Hom[ f ] (F'.₀' x') (F'.₀' y')
    → ℰ.Hom[ F₁.from f ] x' y'
  ff'⁻¹ {f = f} f' = F₁'.from $ ℱ.hom[ sym (F₁.ε f) ] f'
```

On account of this transport, we need displayed variants of the usual
`η` and `ε` equalities for the equivalence given by `ff'`{.Agda}.

```agda
  ε[]
    : ∀ {x y f} {x' : ℰ.Ob[ x ]} {y' : ℰ.Ob[ y ]}
      (f' : ℱ.Hom[ f ] (F'.₀' x') (F'.₀' y'))
    → F'.₁' (ff'⁻¹ f') ℱ.≡[ F₁.ε f ] f'
  ε[] {f = f} f' = ℱ.to-pathp[]⁻ $ F₁'.ε (ℱ.hom[ F₁.ε f ]⁻ f')

  η[]
    : ∀ {x y f} {x' : ℰ.Ob[ x ]} {y' : ℰ.Ob[ y ]} (f' : ℰ.Hom[ f ] x' y')
    → ff'⁻¹ (F'.₁' f') ℰ.≡[ F₁.η f ] f'
  η[] {f = f} f' = ℰ.to-pathp[]⁻ $
    F₁'.from (ℱ.hom[ ⌜ F₁.ε (F.₁ f) ⌝ ]⁻ (F'.₁' f'))  ≡˘⟨ ap¡ (F₁.zig f) ⟩
    F₁'.from (ℱ.hom[ ap F.₁ (F₁.η f) ]⁻ (F'.₁' f'))   ≡˘⟨ ℰ.hom[]-is-subst _ _ ∙∙ (subst-fibrewise (λ g → F₁'.from {f = g}) (sym (F₁.η f)) (F'.₁' f')) ∙∙ sym (ap F₁'.from (ℱ.hom[]-is-subst _ _)) ⟩
    ℰ.hom[ F₁.η f ]⁻ ⌜ F₁'.from (F'.₁' f') ⌝          ≡⟨ ap! (F₁'.η f') ⟩
    ℰ.hom[ F₁.η f ]⁻ f'                               ∎
```

## Essential fibres {defines="essentially-split-surjective-over"}

One way to generalize [[essential fibres]] is as follows:

```agda
Essential-fibre[_]
  : ∀ {b} ((a , f) : Essential-fibre F b) → Displayed-functor F ℰ ℱ
  → ℱ.Ob[ b ] → Type _
Essential-fibre[_] {b = b} (a , f) F' b' = Σ ℰ.Ob[ a ] λ a' → ₀' F' a' ℱ.≅[ f ] b'

is-split-eso[_] : is-split-eso F → Displayed-functor F ℰ ℱ → Type _
is-split-eso[ eso ] F' = ∀ {b} b' → Essential-fibre[ eso b ] F' b'
```