<!--
```agda
open import Cat.Diagram.Coproduct.Indexed
open import Cat.Morphism
open import Cat.Prelude

open import Data.Bool
open import Data.Sum

open import Order.Instances.LexicalSum
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

The indexed coproduct is a special case of the [[lexicographic
sum|lexicographic sum of posets]] where the base poset is [[discrete|
discrete-partial-order]]. It means that there is no non-trivial
relationship across fibres.

```agda
  Disjoint : Poset _ _
  Disjoint = Lexical-sum (Discᵢ I) F
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
  injᵖ : (i : ⌞ I ⌟) → Monotone (F i) (Disjoint I F)
  injᵖ = lexical-sum-injᵖ {I = Discᵢ I} {F = F}
```

The name `Disjoint`{.Agda} is justified by the observation that each of
the coprojections `injᴾ`{.Agda} is actually an [[order embedding]]. This
identifies each factor $F_i$ with its image in $\Sigma F$.

```agda
  injᵖ-is-order-embedding
    : ∀ i → is-order-embedding (F i) (Disjoint I F) (apply (injᵖ i))
  injᵖ-is-order-embedding =
    lexical-sum-injᵖ-is-order-embedding {I = Discᵢ I} {F = F}
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
    cases _ .pres-≤ (x≤y reflᵢ)
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
