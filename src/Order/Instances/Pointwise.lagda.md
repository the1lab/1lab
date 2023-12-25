<!--
```agda
open import Cat.Prelude

open import Order.Instances.Props
open import Order.Displayed
open import Order.Base
open import Cat.Diagram.Product.Indexed
open import 1Lab.Reflection.Marker

open Indexed-product
open is-indexed-product

import Order.Reasoning as Pr
```
-->

```agda
module Order.Instances.Pointwise where
```

# The pointwise ordering

The product of a family of [[partially ordered sets]] $\prod_{i : I} P_i$ is a
poset, for any index type $I$ which we might choose! There might be other ways
of making $\prod_{i : I} P_i$ into a poset, of course, but the canonical way
we're talking about here is the **pointwise ordering** on $\prod_{i : I} P_i$,
where $f \le g$ iff $f(x) \le g(x)$ for all $x$.

[partially ordered sets]: Order.Base.html

```agda
Pointwise : ∀ {ℓ ℓₐ ℓᵣ} (I : Type ℓ) (P : I → Poset ℓₐ ℓᵣ)
  → Poset (ℓ ⊔ ℓₐ) (ℓ ⊔ ℓᵣ)
Pointwise I P = po where
  open module PrP {i : I} = Pr (P i)

  po : Poset _ _
  po .Poset.Ob = (i : I) → ⌞ P i ⌟
  po .Poset._≤_ f g = ∀ x → f x ≤ g x
  po .Poset.≤-thin = hlevel!
  po .Poset.≤-refl x = ≤-refl
  po .Poset.≤-trans f≤g g≤h x = ≤-trans (f≤g x) (g≤h x)
  po .Poset.≤-antisym f≤g g≤f = funext λ x → ≤-antisym (f≤g x) (g≤f x)

Tupleᵖ : ∀ {ℓ ℓₐ ℓₐ' ℓᵣ ℓᵣ'} {I : Type ℓ} {P : I → Poset ℓₐ ℓᵣ} {R : Poset ℓₐ' ℓᵣ'} → (∀ i → Monotone R (P i)) → Monotone R (Pointwise I P)
Tupleᵖ f .hom x i = f i # x
Tupleᵖ f .pres-≤ x≤y i = f i .pres-≤ x≤y

Prjᵖ : ∀ {ℓ ℓₐ ℓᵣ} {I : Type ℓ} {P : I → Poset ℓₐ ℓᵣ} (i : I) → Monotone (Pointwise I P) (P i)
Prjᵖ i .hom = λ f → f i
Prjᵖ i .pres-≤ f≤g = f≤g i
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
Poset[_,_] : ∀ {ℓₒ ℓᵣ ℓₒ' ℓᵣ'}
         → Poset ℓₒ ℓᵣ
         → Poset ℓₒ' ℓᵣ'
         → Poset (ℓₒ ⊔ ℓᵣ ⊔ ℓₒ' ⊔ ℓᵣ') (ℓₒ ⊔ ℓᵣ')
Poset[_,_] P Q = po where
  open Pr Q

  po : Poset _ _
  po .Poset.Ob = Monotone P Q
  po .Poset._≤_ f g = ∀ (x : ⌞ P ⌟) → f # x ≤ g # x
  po .Poset.≤-thin = hlevel!
  po .Poset.≤-refl _ = ≤-refl
  po .Poset.≤-trans f≤g g≤h x = ≤-trans (f≤g x) (g≤h x)
  po .Poset.≤-antisym f≤g g≤f = ext (λ x → ≤-antisym (f≤g x) (g≤f x))
```

Using `Pointwise`{.Agda} we can show that $\Pos$ has all indexed products:
  
```agda
Posets-has-indexed-products : ∀ {o ℓ ℓ'} → has-indexed-products (Posets (o ⊔ ℓ') (ℓ ⊔ ℓ')) ℓ'
Posets-has-indexed-products F .ΠF = Pointwise _ F
Posets-has-indexed-products F .π = Prjᵖ
Posets-has-indexed-products F .has-is-ip .tuple = Tupleᵖ
Posets-has-indexed-products F .has-is-ip .commute = trivial!
Posets-has-indexed-products F .has-is-ip .unique {h = h} f g = ext λ y i → happly (ap hom (g i)) y
```

## Binary products are a special case of indexed products

```agda
open import Data.Bool
open import Order.Instances.Product
open import Order.Univalent

open import Cat.Morphism
open Inverses

×≡Pointwise-bool : ∀ {o ℓ} (P Q : Poset o ℓ) → P ×ᵖ Q ≡ Pointwise Bool (if_then P else Q)
×≡Pointwise-bool P Q = Poset-path λ where
  .to → Tupleᵖ (Bool-elim _ Fstᵖ Sndᵖ)
  .from → Pairᵖ (Prjᵖ true) (Prjᵖ false)
  .inverses .invl → ext λ where
    x true → refl
    x false → refl
  .inverses .invr → ext λ _ → refl , refl

```