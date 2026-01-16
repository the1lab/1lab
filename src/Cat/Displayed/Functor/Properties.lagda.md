<!--
```agda
open import Cat.Functor.Properties
open import Cat.Displayed.Functor
open import Cat.Displayed.Base
open import Cat.Prelude
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
  module ℰ = Displayed ℰ
  module ℱ = Displayed ℱ
  variable
    F : Functor A B

open Functor
open Displayed-functor
```
-->

# Properties of displayed functors

This module mirrors the corresponding one for [ordinary functors]
by defining the corresponding classes of [[displayed functors]]. Note
that many applications of these properties require the conjunction with
the corresponding property of ordinaty functors.

[ordinary functors]: Cat.Functor.Properties.html

:::{.definition #fully-displayed-functor}
A displayed functor is **fully displayed** when its action on hom-sets
_over_ any morphism is surjective:

```agda
is-full' : Displayed-functor F ℰ ℱ → Type _
is-full' F' = ∀ {a b f a' b'} → is-surjective (₁' F' {a} {b} {f} {a'} {b'})
```
:::

:::{.definition #faithfully-displayed-functor}
A displayed functor is **faithfully displayed** when its action on
hom-sets _over_ any morphism is injective:

```agda
is-faithful' : Displayed-functor F ℰ ℱ → Type _
is-faithful' F' = ∀ {a b f a' b'} → injective (₁' F' {a} {b} {f} {a'} {b'})
```
:::

## Fully faithfully displayed functors {defines="fully-faithfully-displayed-functor fully-faithfully-functor"}
A displayed functor is **fully faithfully displayed** when its action on
hom-sets _over_ any morphism is an equivalence.

```agda
is-ff' : Displayed-functor F ℰ ℱ → Type _
is-ff' F' = ∀ {a b f a' b'} →  is-equiv (₁' F' {a} {b} {f} {a'} {b'})

ff'→faithful' : {F' : Displayed-functor F ℰ ℱ} → is-ff' F' → is-faithful' F'
ff'→faithful' has-is-ff = Equiv.injective (_ , has-is-ff)

ff'→full' : {F' : Displayed-functor F ℰ ℱ} → is-ff' F' → is-full' F'
ff'→full' has-is-ff f' = inc (equiv→inverse has-is-ff f' , equiv→counit has-is-ff f')

full'+faithful'→ff' : {F' : Displayed-functor F ℰ ℱ}
  → is-full' F' → is-faithful' F' → is-ff' F'
full'+faithful'→ff' {F = F} {F' = F'} has-is-full has-is-faithful .is-eqv = p where
  img-is-prop : ∀ {a} {b} {f} {a'} {b'} f'
    → is-prop (fibre (₁' F' {a} {b} {f} {a'} {b'}) f')
  img-is-prop f' (g' , p) (h' , q) = Σ-prop-path
    (λ x → ℱ.Hom[ ₁ F _ ]-set (₀' F' _) (₀' F' _) (₁' F' x) f')
    (has-is-faithful (p ∙ sym q))

  p : ∀ {a} {b} {f} {a'} {b'} f'
    → is-contr (fibre (₁' F' {a} {b} {f} {a'} {b'}) f')
  p f' .centre = ∥-∥-elim (λ _ → img-is-prop f') (λ x → x) (has-is-full f')
  p f' .paths = img-is-prop f' _
```
