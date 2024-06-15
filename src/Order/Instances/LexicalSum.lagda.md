<!--
```agda
open import Cat.Prelude

open import Data.Id.Base

open import Order.Displayed
open import Order.Morphism
open import Order.Base

import Order.Reasoning as Pr
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
orders]] indexed by the underlying set of $I$. We can equip the
$\Sigma$-type $\Sigma_{(i : I)} F_i$ with a lexicographic partial
order:

$$
  (i, x) \leq (j, y) \iff i \leq j \wedge (i = j \implies x \leq y)
$$

::: note
We avoid the more traditional formulation that uses the strict order:

$$
  (i, x) < (j, y) \iff i < j \vee (i = j \wedge x < y)
$$

The reason is that $i < j$ naturally involves $i \neq j$ when we take
the non-strict order $i \leq j$ as the primitive notion. Negated types
carry less information and usually work less well in constructive
settings.
:::

Given the dependency of $F$ on $I$, the comparison between $x : F_i$
and $y : F_j$ only makes sense when they lie in the same fibre, that is,
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

The fibre in a lexical sum over $i : I$ is essentially $F_i$. In fact,
their underlying types are judgementally equal in the current
construction. We do not express the sameness using isomorphisms in the
category of posets (`Posets`{.Agda}) due to technical reasons: their
universe levels do not match and we would need ugly lifting to
compensate for the differences.

```agda
  lexical-sum-fibre-equiv
    : (i : ⌞ I ⌟) → ⌞ Fibre (Lexical-sum-over I F) i ⌟ ≃ ⌞ F i ⌟
  lexical-sum-fibre-equiv i = _ , id-equiv

  lexical-sum-fibre-equiv-is-order-embedding
    : ∀ i → is-order-embedding (Fibre (Lexical-sum-over I F) i) (F i) (λ x → x)
  lexical-sum-fibre-equiv-is-order-embedding i =
    prop-ext!
      (λ x≤y → x≤y reflᵢ)
      (λ x≤y p → subst (F._≤ _) (substᵢ-filler-set ⌞F⌟ (hlevel 2) p _) x≤y)
```

We can also define injections from $F_i$, which are essentially
`Order.Displayed.fibre-injᵖ`{.Agda} precomposed with the inverse of
`lexical-sum-fibre-equiv`{.Agda}.

```agda
  lexical-sum-injᵖ : (i : ⌞ I ⌟) → Monotone (F i) (Lexical-sum I F)
  lexical-sum-injᵖ i .hom    x   = i , x
  lexical-sum-injᵖ i .pres-≤ x≤y = I.≤-refl , λ p →
    subst (F._≤ _) (substᵢ-filler-set ⌞F⌟ (hlevel 2) p _) x≤y

  lexical-sum-injᵖ-is-order-embedding
    : ∀ i → is-order-embedding (F i) (Lexical-sum I F) (apply (lexical-sum-injᵖ i))
  lexical-sum-injᵖ-is-order-embedding i =
    prop-ext! (lexical-sum-injᵖ i .pres-≤) λ (_ , q) → q reflᵢ
```

The name `Lexical-sum`{.Agda} is justified by its mapping-in universal
property: given another poset $G$ displayed over $I$ and a collection
a fibrewise map $\sigma_{i\in I} : G_i \to F_i$, there exists a
(unique!) index-preserving map from the total space of $G$ into the
lexical sum such that it commutes with $\sigma$.

```agda
  splitᵖ
    : ∀ {o ℓ} (G : Displayed o ℓ I)
    → (∀ i → Monotone (Fibre G i) (F i))
    → Monotone (∫ G) (Lexical-sum I F)
  splitᵖ G cases .hom    (i , x)     = i , cases i # x
  splitᵖ G cases .pres-≤ (i≤j , x≤y) = i≤j , λ i=ᵢj → lemma-pres-≤ i=ᵢj i≤j x≤y
```
<!--
```agda
    where
      module G = D G

      lemma-pres-≤
        : ∀ {i j} (p : i ≡ᵢ j) (i≤j : i I.≤ j) {x y}
        → G.Rel[ i≤j ] x y
        → substᵢ ⌞F⌟ p (cases i .hom x) F.≤ (cases j .hom y)
      lemma-pres-≤ {i = i} reflᵢ i≤j x≤y =
        cases i .pres-≤ $ subst (λ q → G.Rel[ q ] _ _) (I.≤-thin i≤j I.≤-refl) x≤y
```
-->

::: source
The categorical definition of lexicographic sums is given by Reinhard
Börger, Walter Tholen and Anna Tozzi in their paper [Lexicographic sums
and fibre-faithful maps](https://doi.org/10.1007/BF00872986).
:::
