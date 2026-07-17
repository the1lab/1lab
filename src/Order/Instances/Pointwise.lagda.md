<!--
```agda
open import 1Lab.Reflection.Marker

open import Cat.Diagram.Product.Indexed
open import Cat.Morphism
open import Cat.Prelude

open import Data.Power
open import Data.Bool

open import Order.Instances.Product
open import Order.Semilattice.Join
open import Order.Semilattice.Meet
open import Order.Instances.Props
open import Order.Diagram.Bottom
open import Order.Diagram.Join
open import Order.Diagram.Meet
open import Order.Diagram.Glb
open import Order.Diagram.Lub
open import Order.Diagram.Top
open import Order.Univalent
open import Order.Base

import Order.Reasoning as Pr

open is-indexed-product
open Indexed-product
open Inverses
```
-->

```agda
module Order.Instances.Pointwise where
```

# The pointwise ordering {defines="pointwise-ordering"}

The product of a family of [[partially ordered sets]] $\prod_{i : I} P_i$ is a
poset, for any index type $I$ which we might choose! There might be other ways
of making $\prod_{i : I} P_i$ into a poset, of course, but the canonical way
we're talking about here is the **pointwise ordering** on $\prod_{i : I} P_i$,
where $f \le g$ iff $f(x) \le g(x)$ for all $x$.

```agda
Pointwise : ∀ {ℓ ℓₐ ℓᵣ} (I : Type ℓ) (P : I → Poset ℓₐ ℓᵣ)
  → Poset (ℓ ⊔ ℓₐ) (ℓ ⊔ ℓᵣ)
Pointwise I P = po where
  open module PrP {i : I} = Pr (P i)

  po : Poset _ _
  po .Poset.Ob = (i : I) → ⌞ P i ⌟
  po .Poset._≤_ f g = ∀ x → f x ≤ g x
  po .Poset.≤-thin = hlevel 1
  po .Poset.≤-refl x = ≤-refl
  po .Poset.≤-trans f≤g g≤h x = ≤-trans (f≤g x) (g≤h x)
  po .Poset.≤-antisym f≤g g≤f = funext λ x → ≤-antisym (f≤g x) (g≤f x)

tupleᵖ
  : ∀ {ℓ ℓₐ ℓₐ' ℓᵣ ℓᵣ'} {I : Type ℓ} {P : I → Poset ℓₐ ℓᵣ} {R : Poset ℓₐ' ℓᵣ'}
  → (∀ i → Monotone R (P i))
  → Monotone R (Pointwise I P)
tupleᵖ f .hom x i = f i · x
tupleᵖ f .pres-≤ x≤y i = f i .pres-≤ x≤y

prjᵖ
  : ∀ {ℓ ℓₐ ℓᵣ} {I : Type ℓ} {P : I → Poset ℓₐ ℓᵣ} (i : I)
  → Monotone (Pointwise I P) (P i)
prjᵖ i .hom f      = f i
prjᵖ i .pres-≤ f≤g = f≤g i
```

A very important particular case of the pointwise ordering is the poset
of subsets of a fixed type, which has underlying set $A \to \Omega$.

```agda
Subsets : ∀ {ℓ} → Type ℓ → Poset ℓ ℓ
Subsets A = Pointwise A (λ _ → Props)
```

Another important case: when your domain is not an arbitrary type but
another poset, you might want to consider the full subposet of $P \to Q$
consisting of the monotone maps:

```agda
Poset[_,_]
  : ∀ {ℓₒ ℓᵣ ℓₒ' ℓᵣ'}
  → (P : Poset ℓₒ ℓᵣ) (Q : Poset ℓₒ' ℓᵣ')
  → Poset (ℓₒ ⊔ ℓᵣ ⊔ ℓₒ' ⊔ ℓᵣ') (ℓₒ ⊔ ℓᵣ')
Poset[_,_] P Q = po module Poset[_,_] where
  open Pr Q

  po : Poset _ _
  po .Poset.Ob      = Monotone P Q
  po .Poset._≤_ f g = ∀ x → f · x ≤ g · x

  po .Poset.≤-thin   = hlevel 1
  po .Poset.≤-refl _ = ≤-refl

  po .Poset.≤-trans   f≤g g≤h x = ≤-trans (f≤g x) (g≤h x)
  po .Poset.≤-antisym f≤g g≤f   = ext λ x → ≤-antisym (f≤g x) (g≤f x)
```

Using `Pointwise`{.Agda} we can show that $\Pos$ has all indexed products:

```agda
Posets-has-indexed-products
  : ∀ {o ℓ ℓ'}
  → has-indexed-products (Posets (o ⊔ ℓ') (ℓ ⊔ ℓ')) ℓ'
Posets-has-indexed-products F = mk where
  mk : Indexed-product (Posets _ _) _
  mk .ΠF = Pointwise _ F
  mk .π  = prjᵖ
  mk .has-is-ip .tuple   = tupleᵖ
  mk .has-is-ip .commute = ext λ _ → refl
  mk .has-is-ip .unique f g = ext λ y i → sym (g i) ·ₚ y
```

## Binary products are a special case of indexed products

```agda
×≡Pointwise-bool : ∀ {o ℓ} (P Q : Poset o ℓ) → P ×ᵖ Q ≡ Pointwise Bool (if_then P else Q)
×≡Pointwise-bool P Q = Poset-path λ where
  .to   → tupleᵖ (Bool-elim _ fstᵖ sndᵖ)
  .from → pairᵖ (prjᵖ true) (prjᵖ false)
  .inverses .invl → ext λ where
    x true → refl
    x false → refl
  .inverses .invr → ext λ x y → refl ,ₚ refl
```
