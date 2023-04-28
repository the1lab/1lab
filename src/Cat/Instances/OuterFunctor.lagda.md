<!--
```agda
open import Cat.Internal.Functor.Outer

open import Cat.Prelude

import Cat.Internal.Base
import Cat.Internal.Reasoning
import Cat.Reasoning
```
-->

```agda
module Cat.Instances.OuterFunctor
  {o ℓ} {C : Precategory o ℓ}
  where
```

<!--
```agda
open Cat.Reasoning C
open Cat.Internal.Base C
open Outer-functor
open _=>o_

```
-->

# The category of outer functors

Unsurprisingly, [outer functors] and outer natural transformations form
a category. To show this, we must first prove that outer natural
transformations are have composites and identities. Luckily, this
is a rote calculation.

[outer functors]: Cat.Internal.Functor.Outer.html

<!--
```agda
module _ {ℂ : Internal-cat} where
  open Internal-cat ℂ
```
-->

```agda
  idnto : ∀ {F : Outer-functor ℂ} → F =>o F
  idnto {F = F} .ηo px = px
  idnto {F = F} .ηo-fib _ = refl
  idnto {F = F} .is-naturalo px y f =
    ap (F .P₁ px) (Internal-hom-path refl)
  idnto {F = F} .ηo-nat _ _ = refl

  _∘nto_ : ∀ {F G H : Outer-functor ℂ} → G =>o H → F =>o G → F =>o H
  _∘nto_ α β .ηo x = α .ηo (β .ηo x)
  _∘nto_ α β .ηo-fib px = α .ηo-fib (β .ηo px) ∙ β .ηo-fib px
  _∘nto_ {H = H} α β .is-naturalo px y f =
    ap (α .ηo) (β .is-naturalo px y f)
    ∙ α .is-naturalo (β .ηo px) y (adjusti (sym (β .ηo-fib px)) refl f)
    ∙ ap (H .P₁ _) (Internal-hom-path refl)
  (α ∘nto β) .ηo-nat px σ =
    α .ηo-nat (β .ηo px) σ ∙ ap (α .ηo) (β .ηo-nat px σ)
```

Assembling these into a category is also quite simple.

<!--
```agda
module _ (ℂ : Internal-cat) where
  open Internal-cat ℂ
```
-->

```agda
  Outer-functors : Precategory (o ⊔ ℓ) (o ⊔ ℓ) 
  Outer-functors .Precategory.Ob = Outer-functor ℂ
  Outer-functors .Precategory.Hom = _=>o_
  Outer-functors .Precategory.Hom-set _ _ = Outer-nat-is-set
  Outer-functors .Precategory.id = idnto
  Outer-functors .Precategory._∘_ = _∘nto_
  Outer-functors .Precategory.idr α = Outer-nat-path (λ _ → refl)
  Outer-functors .Precategory.idl α = Outer-nat-path (λ _ → refl)
  Outer-functors .Precategory.assoc α β γ = Outer-nat-path (λ _ → refl)
```

