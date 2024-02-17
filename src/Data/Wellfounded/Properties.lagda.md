<!--
```agda
open import 1Lab.Prelude

open import Data.Wellfounded.Base
open import Data.Nat.Order
open import Data.Nat.Base
```
-->

```agda
module Data.Wellfounded.Properties where
```

It was mentioned in the definition of `Acc`{.Agda} that being accessible
is a proposition, but this has not yet been established. We can do so
using, as usual, induction:

<!--
```agda
private variable
  ℓ : Level
  A B : Type ℓ
  R : A → A → Type ℓ
```
-->

```agda
Acc-is-prop : ∀ x → is-prop (Acc R x)
Acc-is-prop x (acc s) (acc t) =
  ap acc (ext λ y y<x → Acc-is-prop y (s y y<x) (t y y<x))

Wf-is-prop : is-prop (Wf R)
Wf-is-prop = Π-is-hlevel 1 Acc-is-prop
```

## Instances

The usual induction principle for the natural numbers is equivalent to
saying that the relation $R(x,y) := y = 1+x$ is well-founded.
Additionally, the relation $<$ on the natural numbers is well-founded.

```agda
suc-wf : Wf (λ x y → y ≡ suc x)
suc-wf = Induction-wf (λ x y → y ≡ suc x) λ P m →
  Nat-elim P
    (m 0 λ y 0=suc → absurd (zero≠suc 0=suc))
    λ {n} Pn → m (suc n) (λ y s → subst P (suc-inj s) Pn)

<-wf : Wf _<_
<-wf x = go x x ≤-refl where
  go : (x y : Nat) → .(y ≤ x) → Acc _<_ y
  go x zero w = acc λ _ ()
  go (suc x) (suc y) w = acc k' where
    k' : ∀ x → x < suc y → Acc _<_ x
    k' x' w' = go x x' (≤-trans (≤-peel w') (≤-peel w))
```
