<!--
```agda
open import Algebra.Group.Cat.FinitelyComplete
open import Algebra.Group.Cat.Base
open import Algebra.Group.Subgroup
open import Algebra.Group.Ab.Sum
open import Algebra.Group.Ab

open import Cat.Diagram.Equaliser
open import Cat.Diagram.Product
open import Cat.Abelian.Base
open import Cat.Prelude
```
-->

```agda
module Cat.Abelian.Instances.Ab {ℓ} where
```

<!--
```agda
open is-additive.Coequaliser
open is-additive.Terminal
open is-pre-abelian
open is-additive
```
-->

# The category of abelian groups

The prototypal --- representative, even --- example of an
[$\Ab$-enriched], and an [abelian] category at that, is the category of
[[abelian groups]], $\Ab$. For abstractly-nonsensical reasons, we could
say $\Ab$ is $\Ab$-enriched by virtue of being monoidal closed, but we
have a concrete construction at hand: `Ab-ab-category`{.Agda}

[$\Ab$-enriched]: Cat.Abelian.Base.html#ab-enriched-categories
[abelian]: Cat.Abelian.Base.html#pre-abelian-abelian-categories

Let us show it is additive. The terminal group is given by the terminal
set, equipped with its unique group structure, and we have already
computed [[products|direct sum abelian groups]] --- they are given by
direct sums.

```agda
Ab-is-additive : is-additive (Ab ℓ)
Ab-is-additive .has-ab = Ab-ab-category
Ab-is-additive .has-terminal .top = from-commutative-group (Zero-group {ℓ}) (λ x y → refl)
Ab-is-additive .has-terminal .has⊤ x =
  contr (total-hom (λ _ → lift tt) (record { pres-⋆ = λ x y i → lift tt }))
    λ x → trivial!

Ab-is-additive .has-prods A B .Product.apex = A ⊕ B
Ab-is-additive .has-prods A B .Product.π₁ = _
Ab-is-additive .has-prods A B .Product.π₂ = _
Ab-is-additive .has-prods A B .Product.has-is-product = Direct-sum-is-product
```
