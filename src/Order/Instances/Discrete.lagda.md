```agda
open import Cat.Displayed.Univalence.Thin
open import Cat.Prelude

open import Order.Base

module Order.Instances.Discrete where
```

```agda
Discrete-po : ∀ {ℓ} (T : Type ℓ) → is-set T → Poset-on ℓ T
Discrete-po T t-set = make-poset.to-poset-on mk where
  open make-poset
  mk : make-poset _ T
  mk .rel x y = x ≡ y
  mk .id = refl
  mk .thin = t-set _ _
  mk .trans = _∙_
  mk .antisym a b = a
```
