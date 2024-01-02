<!--
```agda
open import Algebra.Semigroup
open import Algebra.Magma

open import Cat.Prelude

open import Data.Bool

open import Order.Diagram.Meet
open import Order.Diagram.Glb
open import Order.Base

import Order.Diagram.Meet.Reasoning as Meets
import Order.Diagram.Top
import Order.Reasoning
```
-->

```agda
module Order.Diagram.Glb.Reasoning {o ℓ} (P : Poset o ℓ) where
```

<!--
```agda
open Order.Diagram.Top P
open Order.Reasoning P
```
-->

# Reasoning about greatest lower bounds

```agda
module Glbs (glbs : ∀ {I : Type o} → (f : I → Ob) → Glb P f) where
  module glbs {I} {f : I → Ob} = Glb (glbs f)
  open glbs using () renaming (glb≤fam to ⋂-proj; greatest to ⋂-universal) public

  ⋂ : ∀ {I : Type o} → (I → Ob) → Ob
  ⋂ f = glbs.glb {f = f}
```

```agda
  ⋂-twice
    : ∀ {I : Type o} {J : I → Type o} (f : (i : I) → J i → Ob)
    → ⋂ (λ i → ⋂ λ j → f i j)
    ≡ ⋂ {I = Σ I J} (λ p → f (p .fst) (p .snd))
  ⋂-twice f =
    ≤-antisym
      (⋂-universal _ (λ (i , j) → ≤-trans (⋂-proj i) (⋂-proj {f = f i} j)))
      (⋂-universal _ λ i → ⋂-universal _ λ j → ⋂-proj (i , j))
```

```agda
  ⋂≤⋂
    : {I : Type o} {f g : I → Ob}
    → (∀ i → f i ≤ g i)
    → ⋂ f ≤ ⋂ g
  ⋂≤⋂ p = ⋂-universal _ λ i → ≤-trans (⋂-proj i) (p i)

  ⋂-singleton
    : ∀ {I : Type o} {f : I → Ob}
    → (p : is-contr I)
    → ⋂ f ≡ f (p .centre)
  ⋂-singleton {f = f} p = ≤-antisym
    (⋂-proj (p .centre))
    (⋂-universal _ λ i → ≤-refl' (ap f (p .paths i)))
```

```agda
  module _ (x y : Ob) where opaque
    private
      it : Meet P x y
      it = Glb→Meet (lower-glb (glbs _))

    infixr 25 _∩_
    _∩_ : Ob
    _∩_ = it .Meet.glb

    ∩-meets : is-meet P x y _∩_
    ∩-meets = it .Meet.has-meet

  opaque
    has-top : Top
    has-top = Glb→Top (lower-glb (glbs (λ ())))

  open Meets ∩-meets public
  open Top has-top using (top; !) public
```

```agda
  ∩-distrib-⋂-≤l
    : ∀ {I : Type o} {x : Ob} {f : I → Ob}
    → x ∩ ⋂ f ≤ ⋂ λ i → x ∩ f i
  ∩-distrib-⋂-≤l =
    (⋂-universal _ λ i → ∩-universal _ ∩≤l (≤-trans ∩≤r (⋂-proj i)))
```

```agda
  ∩-distrib-nonempty-⋂-l
    : ∀ {I : Type o} {x : Ob} {f : I → Ob}
    → ∥ I ∥
    → x ∩ ⋂ f ≡ ⋂ λ i → x ∩ f i
  ∩-distrib-nonempty-⋂-l i =
    ≤-antisym
     ∩-distrib-⋂-≤l
     (∥-∥-rec! (λ i → ∩-universal _ (≤-trans (⋂-proj i) ∩≤l) (⋂≤⋂ λ _ → ∩≤r)) i)
```

```agda
  ⋂-ap
    : ∀ {I I' : Type o} {f : I → Ob} {g : I' → Ob}
    → (e : I ≃ I')
    → (∀ i → f i ≡ g (e .fst i))
    → ⋂ f ≡ ⋂ g
  ⋂-ap e p = ap₂ (λ I f → ⋂ {I = I} f) (ua e) (ua→ p)

  -- raised i for "index", raised f for "family"
  ⋂-apⁱ : ∀ {I I' : Type o} {f : I' → Ob} (e : I ≃ I') → ⋂ (λ i → f (e .fst i)) ≡ ⋂ f
  ⋂-apᶠ : ∀ {I : Type o} {f g : I → Ob} → (∀ i → f i ≡ g i) → ⋂ f ≡ ⋂ g

  ⋂-apⁱ e = ⋂-ap e (λ i → refl)
  ⋂-apᶠ p = ⋂-ap (_ , id-equiv) p
```
