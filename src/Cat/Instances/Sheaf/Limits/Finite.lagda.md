<!--
```agda
open import Cat.Instances.Presheaf.Limits
open import Cat.Instances.Sheaf.Limits
open import Cat.Diagram.Limit.Pullback
open import Cat.Instances.Shape.Cospan
open import Cat.Diagram.Limit.Product
open import Cat.Instances.Shape.Two
open import Cat.Diagram.Limit.Base
open import Cat.Instances.Functor
open import Cat.Diagram.Pullback
open import Cat.Diagram.Terminal
open import Cat.Diagram.Product
open import Cat.Site.Base
open import Cat.Prelude
```
-->

```agda
module Cat.Instances.Sheaf.Limits.Finite
  {o ℓ ℓj} {C : Precategory o ℓ} (J : Coverage C ℓj) where
```

<!--
```agda
open is-pullback
open is-product
open Pullback
open Terminal
open Product
```
-->

## Finite limits of sheaves

Since the category $\Sh(\cC, J)$ of [[sheaves]] on a [[site]] is a
reflective subcategory of $\psh(\cC)$, we know automatically that it is
closed --- but using this theorem computes every limit, even the finite
limits with known shape such as [[products]] and the [[terminal
object]], as an [[equaliser]] between maps to and from a very big
product. To make working with finite limits of sheaves smoother, we
specialise the proof that [[sheaves are closed under limits|limits of
sheaves]] to these finite cases:

```agda
Sh[]-products : has-products (Sheaves J ℓ)
Sh[]-products (A , ashf) (B , bshf) = prod where
  prod' = PSh-products _ C A B

  prod : Product (Sheaves J _) _ _
  prod .apex .fst = prod' .apex
  prod .π₁ = prod' .π₁
  prod .π₂ = prod' .π₂
  prod .has-is-product .⟨_,_⟩  = prod' .⟨_,_⟩
  prod .has-is-product .π₁∘⟨⟩  = prod' .π₁∘⟨⟩
  prod .has-is-product .π₂∘⟨⟩  = prod' .π₂∘⟨⟩
  prod .has-is-product .unique = prod' .unique

  prod .apex .snd = is-sheaf-limit
    {F = 2-object-diagram _ _} {ψ = 2-object-nat-trans _ _}
    (is-product→is-limit (PSh ℓ C) (prod' .has-is-product))
    (λ { true → ashf ; false → bshf })
```

<!--
```agda
Sh[]-pullbacks : has-pullbacks (Sheaves J ℓ)
Sh[]-pullbacks {A = A} {B} {X} f g = pb where
  pb' = PSh-pullbacks _ C f g

  open is-pullback
  open Pullback

  pb : Pullback (Sheaves J _) _ _
  pb .apex .fst = pb' .apex
  pb .apex .snd = is-sheaf-limit {o' = lzero} {ℓ' = lzero} (Limit.has-limit (Pullback→Limit (PSh ℓ C) pb')) λ where
    cs-a → A .snd
    cs-b → B .snd
    cs-c → X .snd
  pb .p₁ = pb' .p₁
  pb .p₂ = pb' .p₂
  pb .has-is-pb = record { Pullback pb' }
```
-->

The terminal object in sheaves is even easier to define:

```agda
Sh[]-terminal : Terminal (Sheaves J ℓ)
Sh[]-terminal .top .fst = PSh-terminal _ C .top
Sh[]-terminal .has⊤ (S , _) = PSh-terminal _ C .has⊤ S

Sh[]-terminal .top .snd .whole _ _     = lift tt
Sh[]-terminal .top .snd .glues _ _ _ _ = refl
Sh[]-terminal .top .snd .separate _ _  = refl
```
