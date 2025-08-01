<!--
```agda
open import 1Lab.Prelude

open import Cat.Instances.Shape.Terminal
open import Cat.Diagram.Product.Indexed
open import Cat.Instances.Slice
open import Cat.Univalent
open import Cat.Prelude
```
-->

```agda
module Cat.Diagram.Pullback.Indexed {o ℓ} (C : Precategory o ℓ) where
```

<!--
```agda
import Cat.Reasoning C as C
private
  variable
    o' ℓ' : Level
    Idx : Type ℓ'
    A B P : C.Ob
```
-->

# Wide pullabacks {defines="wide-pullback indexed-pullback"}

```agda
is-ｐｕｌｌｂａｃｋ : {c : C.Ob} (F : Idx → /-Obj c) (π : ∀ i → /-Hom (cut C.id) (F i)) → Type (o ⊔ ℓ ⊔ level-of Idx)
is-ｐｕｌｌｂａｃｋ {c = c} = is-indexed-product (Slice C c)

Ｐｕｌｌｂａｃｋ : {c : C.Ob} (F : Idx → /-Obj c) → Type (o ⊔ ℓ ⊔ level-of Idx)
Ｐｕｌｌｂａｃｋ {c = c} = Indexed-product (Slice C c)
```
