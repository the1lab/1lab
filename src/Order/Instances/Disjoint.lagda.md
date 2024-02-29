<!--
```agda
open import Cat.Diagram.Coproduct.Indexed
open import Cat.Morphism
open import Cat.Prelude

open import Data.Id.Base
open import Data.Bool
open import Data.Sum

open import Order.Instances.Coproduct renaming (matchᵖ to match⊎ᵖ)
open import Order.Instances.Discrete
open import Order.Displayed
open import Order.Univalent
open import Order.Morphism
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

If $F_i$ is a family of [[partial orders]] indexed by a [[set]] $I$,
then we can equip the $\Sigma$-type $\Sigma_{(i : I)} F_i$ with a
"fibrewise" partial order: this is the [[coproduct]] of these orders in
the category of posets.

[partially ordered sets]: Order.Base.html

<!--
```agda
private module D = Displayed

module _ {ℓ ℓₐ ℓᵣ} (I : Set ℓ) (F : ⌞ I ⌟ → Poset ℓₐ ℓᵣ) where
  private
    open module F {i : ⌞ I ⌟} = Pr (F i)

    ⌞F⌟ : ⌞ I ⌟ → Type ℓₐ
    ⌞F⌟ e = ⌞ F e ⌟
```
-->

Since the indices $i, j : I$ are drawn from completely arbitrary sets,
we can't exactly define the order by pattern matching, as in the
[[binary coproduct of posets]]. Instead, we must define what it means to
compare two totally arbitrary pairs $(i, x) \le (j, y)$^[where $x : F_x$
and $y : F_j$].

Considering that we only know how to compare elements in the same fibre,
the natural solution is to require, as part of proving $(i, x) \le (j,
y)$, some evidence $p : i = j$. We can then transport $x$ across $p$ to
obtain a value in $F_j$, which can be compared against $y : F_j$.

The concerns of defining the ordering in each fibre, and then defining
the ordering on the entire total space, are mostly orthogonal. Indeed,
these can be handled in a modular way: the construction we're interested
in naturally arises as the [[total (thin) category|total category]] of a
particular [[displayed order]] --- over the [[discrete partial order]]
on the index set $I$.

```agda
  _≤[_]'_ : {i j : ⌞ I ⌟} → ⌞F⌟ i → i ≡ᵢ j → ⌞F⌟ j → Type ℓᵣ
  x ≤[ p ]' y = substᵢ ⌞F⌟ p x ≤ y

  substᵖ : ∀ {i j} → i ≡ᵢ j → Monotone (F i) (F j)
  substᵖ reflᵢ .hom    x   = x
  substᵖ reflᵢ .pres-≤ x≤y = x≤y

  Disjoint-over : Displayed _ _ (Discᵢ I)
  Disjoint-over .D.Ob[_]        = ⌞F⌟
  Disjoint-over .D.Rel[_] p x y = x ≤[ p ]' y
  Disjoint-over .D.≤-thin'    = hlevel!
  Disjoint-over .D.≤-refl'    = F.≤-refl
  Disjoint-over .D.≤-antisym' = F.≤-antisym
  Disjoint-over .D.≤-trans' {f = reflᵢ} {g = reflᵢ} =
    F.≤-trans
```

To differentiate from the binary coproducts, we refer to the indexed
coproduct of a family as **disjoint** coproducts, or `Disjoint`{.Agda}
for short.

```agda
  Disjoint : Poset _ _
  Disjoint = ∫ Disjoint-over
```

<!--
```agda
_≤[_]_
  : ∀ {ℓ ℓₐ ℓᵣ} {I : Set ℓ} {F : ⌞ I ⌟ → Poset ℓₐ ℓᵣ} {i j : ⌞ I ⌟}
  → ⌞ F i ⌟ → i ≡ᵢ j → ⌞ F j ⌟
  → Type ℓᵣ
_≤[_]_ {I = I} {F = F} x p y = _≤[_]'_ I F x p y
{-# DISPLAY _≤[_]'_ I F x p y = x ≤[ p ] y #-}

module _ {ℓ ℓₐ ℓᵣ} {I : Set ℓ} {F : ⌞ I ⌟ → Poset ℓₐ ℓᵣ} where
  private
    open module F {i : ⌞ I ⌟} = Pr (F i)

    ⌞F⌟ : ⌞ I ⌟ → Type ℓₐ
    ⌞F⌟ e = ⌞ F e ⌟
```
-->

```agda
  injᵖ : (i : ⌞ I ⌟) → Monotone (F i) (Disjoint I F)
  injᵖ i .hom    x   = i , x
  injᵖ i .pres-≤ x≤y = reflᵢ , x≤y
```

The name `Disjoint`{.Agda} is justified by the observation that each of
the coprojections `injᴾ`{.Agda} is actually an [[order embedding]]. This
identifies each factor $F_i$ with its image in $\Sigma F$.

```agda
  injᵖ-is-order-embedding
    : ∀ i → is-order-embedding (F i) (Disjoint I F) (apply (injᵖ i))
  injᵖ-is-order-embedding i .fst = injᵖ i .pres-≤
  injᵖ-is-order-embedding i .snd = biimp-is-equiv!
    (injᵖ i .pres-≤)
    λ { (p , q) → ≤-trans (≤-refl' (substᵢ-filler-set _ hlevel! p _)) q }
```

To complete the construction of the coproduct, we have the following
function for mapping _out_, by cases:

```agda
  matchᵖ
    : ∀ {o ℓ} {R : Poset o ℓ}
    → (∀ i → Monotone (F i) R)
    → Monotone (Disjoint I F) R
  matchᵖ cases .hom    (i , x)       = cases i # x
  matchᵖ cases .pres-≤ (reflᵢ , x≤y) =
    cases _ .pres-≤ x≤y
```

Straightforward calculations finish the proof that $\Pos$ has all
set-indexed coproducts.

```agda
Posets-has-set-indexed-coproducts
  : ∀ {o ℓ κ} (I : Set κ)
  → has-coproducts-indexed-by (Posets (o ⊔ κ) (ℓ ⊔ κ)) ⌞ I ⌟
Posets-has-set-indexed-coproducts I F = mk where
  mk : Indexed-coproduct (Posets _ _) F
  mk .ΣF = Disjoint I F
  mk .ι  = injᵖ
  mk .has-is-ic .match      = matchᵖ
  mk .has-is-ic .commute    = trivial!
  mk .has-is-ic .unique f p = ext λ i x → p i #ₚ x
```

## Binary coproducts are a special case of indexed coproducts

```agda
⊎≡Disjoint-bool : ∀ {o ℓ} (P Q : Poset o ℓ) → P ⊎ᵖ Q ≡ Disjoint (el! Bool) (if_then P else Q)
⊎≡Disjoint-bool P Q = Poset-path λ where
  .to   → match⊎ᵖ (injᵖ true) (injᵖ false)
  .from → matchᵖ (Bool-elim _ inlᵖ inrᵖ)
  .inverses .invl → ext λ where
    true  x → refl
    false x → refl
  .inverses .invr → ext λ where
    (inl x) → refl
    (inr x) → refl
```
