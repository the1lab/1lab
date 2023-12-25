<!--
```agda
open import Cat.Diagram.Coproduct.Indexed
open import Cat.Morphism
open import Cat.Prelude

open import Data.Id.Base
open import Data.Bool
open import Data.Sum

open import Order.Instances.Coproduct renaming (Matchᵖ to Match⊎ᵖ)
open import Order.Instances.Discrete
open import Order.Displayed
open import Order.Univalent
open import Order.Base

import Order.Reasoning as Pr

open is-indexed-coproduct
open Indexed-coproduct
open Inverses
```
-->

```agda
module Order.Instances.Disjoint where
```

# Indexed coproducts of posets

The coproduct of a family $F$ of [[partially ordered sets]] $\sum_{i : I} F_i$ is a
poset, for any set $I$. Specifically it is the disjoint union of all the
posets in the family.

[partially ordered sets]: Order.Base.html

<!--
```agda
module _ {ℓ ℓₐ ℓᵣ} (I : Set ℓ) (F : ⌞ I ⌟ → Poset ℓₐ ℓᵣ) where
```
-->

```agda
  private
    open module F {i : ⌞ I ⌟} = Pr (F i)
    ⌞F⌟ : ⌞ I ⌟ → Type ℓₐ
    ⌞F⌟ e = ⌞ F e ⌟

  _≤[_]'_ : {i j : ⌞ I ⌟} → ⌞F⌟ i → (i ≡ᵢ j) → ⌞F⌟ j → Type ℓᵣ
  (x ≤[ p ]' y) = substᵢ ⌞F⌟ p x ≤ y
  
  Substᵖ : ∀ {i j} → i ≡ᵢ j → Monotone (F i) (F j)
  Substᵖ reflᵢ .hom = λ x → x
  Substᵖ reflᵢ .pres-≤ = λ x≤y → x≤y


  Disjoint-disp : Displayed _ _ (Discᵢ I)
  Disjoint-disp .Displayed.Ob[_] = ⌞F⌟
  Disjoint-disp .Displayed.Rel[_] p x y = x ≤[ p ]' y
  Disjoint-disp .Displayed.≤-refl' = F.≤-refl
  Disjoint-disp .Displayed.≤-thin' p = hlevel!
  Disjoint-disp .Displayed.≤-trans' {f = reflᵢ} {g = reflᵢ} = F.≤-trans
  Disjoint-disp .Displayed.≤-antisym' = F.≤-antisym

  Disjoint : Poset _ _
  Disjoint = ∫ Disjoint-disp

_≤[_]_ : ∀ {ℓ ℓₐ ℓᵣ} {I : Set ℓ} {F : ⌞ I ⌟ → Poset ℓₐ ℓᵣ} {i j : ⌞ I ⌟} → ⌞ F i ⌟ → (i ≡ᵢ j) → ⌞ F j ⌟ → Type ℓᵣ
_≤[_]_ {I = I} {F = F} x p y = _≤[_]'_ I F x p y
{-# DISPLAY _≤[_]'_ I F x p y = x ≤[ p ] y #-}
```

<!--
```agda
module _ {ℓ ℓₐ ℓᵣ} {I : Set ℓ} {F : ⌞ I ⌟ → Poset ℓₐ ℓᵣ} where
  private 
    
    open module F {i : ⌞ I ⌟} = Pr (F i)
    
    ⌞F⌟ : ⌞ I ⌟ → Type ℓₐ
    ⌞F⌟ e = ⌞ F e ⌟
```
-->

```agda
  Injᵖ : (i : ⌞ I ⌟) → Monotone (F i) (Disjoint I F)
  Injᵖ i .hom x = (i , x)
  Injᵖ i .pres-≤ x≤y = reflᵢ , x≤y

  Matchᵖ : ∀ {o ℓ} {R : Poset o ℓ} → (∀ i → Monotone (F i) R) → Monotone (Disjoint I F) R
  Matchᵖ cases .hom (i , x) = cases i # x
  Matchᵖ cases .pres-≤ {i , x} {.i , y} (reflᵢ , x≤y) = cases i .pres-≤ x≤y
```

Using this, we can show that $\Pos$ has all $\Set$-indexed coproducts.

```agda

Posets-has-set-indexed-coproducts : ∀ {o ℓ κ} (I : Set κ) → has-coproducts-indexed-by (Posets (o ⊔ κ) (ℓ ⊔ κ)) ⌞ I ⌟
Posets-has-set-indexed-coproducts I F .ΣF = Disjoint I F
Posets-has-set-indexed-coproducts I F .ι = Injᵖ
Posets-has-set-indexed-coproducts I F .has-is-ic .match = Matchᵖ
Posets-has-set-indexed-coproducts I F .has-is-ic .commute = trivial!
Posets-has-set-indexed-coproducts I F .has-is-ic .unique f p = ext λ where
  (i , x) → happly (ap hom (p i)) x
  
```
## Binary coproducts are a special case of indexed coproducts

```agda
⊎≡Disjoint-bool : ∀ {o ℓ} (P Q : Poset o ℓ) → P ⊎ᵖ Q ≡ Disjoint (el! Bool) (if_then P else Q)
⊎≡Disjoint-bool P Q = Poset-path λ where 
  .to → Match⊎ᵖ (Injᵖ true) (Injᵖ false)
  .from → Matchᵖ (Bool-elim _ Inlᵖ Inrᵖ)
  .inverses .invl → ext λ where 
    (true , x) → refl
    (false , x) → refl
  .inverses .invr → ext λ where 
    (inl x) → refl
    (inr x) → refl
```
