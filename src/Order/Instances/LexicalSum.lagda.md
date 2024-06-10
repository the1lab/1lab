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
module Order.Instances.LexicalSum where
```

# Lexicographic sum of posets {defines="lexicographic-sum-of-posets lexical-sum-of-posets"}

<!--
```agda
private module D = Displayed

module _ {ℓₐ ℓᵣ ℓₐ' ℓᵣ'} (I : Poset ℓₐ ℓᵣ) (F : ⌞ I ⌟ → Poset ℓₐ' ℓᵣ') where
  private
    module I = Pr I
    module F {i : ⌞ I ⌟} = Pr (F i)

    ⌞F⌟ : ⌞ I ⌟ → Type ℓₐ'
    ⌞F⌟ e = ⌞ F e ⌟
```
-->

Let $I$ be a [[partial order]] and $F_i$ be a family of [[partial
orders]] indexed by the underlying set of $I$.We can equip the
$\Sigma$-type $\Sigma_{(i : I)} F_i$ with a lexicographic partial
order:

$$
  (i, x) \leq (j, y) \iff i \leq j \wedge (i = j \implies x \leq y)
$$

::: note
The above formulation intentionally avoids the conventional strict
order:

$$
  (i, x) < (j, y) \iff i < j \vee i = j \wedge x < y
$$

The reason is that $i < j$ naturally involves $i \neq j$ as we take
the non-strict order $i \leq j$ as the primitive notion. Negated types
carry little information and do not work well in constructive settings.
:::

Given the dependency of $F$ on $I$, the comparison between $x : F_i$
and $y : F_j$ only make sense when they lie in the same fibre, that is,
when there is evidence $p : i = j$. We can then transport $x$ across
$p$ to obtain a value in $F_j$, which can then be compared against
$y : F_j$.

The concerns of defining the ordering in each fibre, and then defining
the ordering on the entire total space, are mostly orthogonal. Indeed,
these can be handled in a modular way: the construction we're interested
in naturally arises as the [[total (thin) category|total category]] of a
particular [[displayed order]] over the base poset $I$.

```agda
  Lexical-sum-over : Displayed _ _ I
  Lexical-sum-over .D.Ob[_]      = ⌞F⌟
  Lexical-sum-over .D.Rel[_] {i} {j} _ x y =
    (p : i ≡ᵢ j) → substᵢ ⌞F⌟ p x F.≤ y
```
<!--
```agda
  Lexical-sum-over .D.≤-thin' _  = hlevel 1
  Lexical-sum-over .D.≤-refl' p  = F.≤-refl' $ sym $ substᵢ-filler-set ⌞F⌟ (hlevel 2) p _
  Lexical-sum-over .D.≤-antisym' x≤'y y≤'x = F.≤-antisym (x≤'y reflᵢ) (y≤'x reflᵢ)
  Lexical-sum-over .D.≤-trans' {f = i≤j} {g = j≤i} x≤'y y≤'z reflᵢ =
    let i=ᵢj = Id≃path.from $ I.≤-antisym i≤j j≤i in
    lemma i=ᵢj (x≤'y i=ᵢj) (y≤'z (symᵢ i=ᵢj))
    where
      lemma : ∀ {i j} (p : i ≡ᵢ j) {x y z} → substᵢ ⌞F⌟ p x F.≤ y → substᵢ ⌞F⌟ (symᵢ p) y F.≤ z → x F.≤ z
      lemma reflᵢ = F.≤-trans
```
-->

```agda
  Lexical-sum : Poset _ _
  Lexical-sum = ∫ Lexical-sum-over
```

<!--
```agda
module _ {ℓₐ ℓᵣ ℓₐ' ℓᵣ'} {I : Poset ℓₐ ℓᵣ} {F : ⌞ I ⌟ → Poset ℓₐ' ℓᵣ'} where
  private
    module I = Pr I
    module F {i : ⌞ I ⌟} = Pr (F i)

    ⌞F⌟ : ⌞ I ⌟ → Type ℓₐ'
    ⌞F⌟ e = ⌞ F e ⌟
```
-->

The name `Lexical-sum`{.Agda} is justified by its mapping-in universal
property: given another poset $G$ displayed over $I$ and a collection
of fibrewise maps $\sigma_{i\in I} : G_i \to F_i$, there exists a
(unique!) index-preserving map from the total space of $G$ into the
lexical sum such that it commutes with all $\sigma_i$.

```agda
  splitᵖ
    : ∀ {o ℓ} (G : Displayed o ℓ I)
    → (∀ i → Monotone (Fibre G i) (F i))
    → Monotone (∫ G) (Lexical-sum I F)
  splitᵖ G cases .hom    (i , x)     = i , cases i # x
  splitᵖ G cases .pres-≤ (i≤j , x≤y) =
    i≤j , λ p → lemma p i≤j x≤y
    where
      module G = D G

      lemma
        : ∀ {i j} (p : i ≡ᵢ j) (i≤j : i I.≤ j) {x y}
        → G.Rel[ i≤j ] x y
        → substᵢ ⌞F⌟ p (cases i .hom x) F.≤ (cases j .hom y)
      lemma {i = i} reflᵢ i≤j x≤y =
        cases i .pres-≤ $ subst (λ q → G.Rel[ q ] _ _) (I.≤-thin i≤j I.≤-refl) x≤y
```
