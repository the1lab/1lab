```agda
open import Algebra.Group.Cat.FinitelyComplete
open import Algebra.Group.Cat.Base
open import Algebra.Group.Subgroup
open import Algebra.Group.Ab.Free
open import Algebra.Group.Ab.Sum
open import Algebra.Group.Ab
open import Algebra.Group

open import Cat.Functor.Adjoint.Continuous
open import Cat.Diagram.Equaliser.Kernel
open import Cat.Functor.FullSubcategory
open import Cat.Diagram.Coequaliser
open import Cat.Diagram.Equaliser
open import Cat.Diagram.Terminal
open import Cat.Diagram.Product
open import Cat.Functor.Adjoint
open import Cat.Abelian.Base
open import Cat.Prelude

module Cat.Abelian.Instances.Ab {ℓ} where
```

<!--
```agda
open is-additive.Coequaliser
open is-additive.Terminal
open is-pre-abelian
open Ab-category
open is-additive
open make-group
```
-->

# The category of abelian groups

The prototypal --- representative, even --- example of an
[$\Ab$-enriched], and an [abelian] category at that, is the category of
abelian groups, $\Ab$. For abstractly-nonsensical reasons, we could say
$\Ab$ is $\Ab$-enriched by virtue of being monoidal closed, but we have
a concrete construction at hand to apply. Let's see it:

[$\Ab$-enriched]: Cat.Abelian.Base.html#ab-enriched-categories
[abelian]: Cat.Abelian.Base.html#pre-abelian-abelian-categories

```agda
Ab-ab : Ab-category (Ab ℓ)
Ab-ab .Group-on-hom A B = Hom-group A B .Restrict-ob.object .snd
Ab-ab .Hom-grp-ab A B = Hom-group A B .Restrict-ob.witness
Ab-ab .∘-linear-l f g h = Forget-is-faithful refl
Ab-ab .∘-linear-r f g h = Forget-is-faithful $ funext λ x →
  sym $ f .preserves .Group-hom.pres-⋆ _ _
```

Let us show it is additive. The terminal group is given by the terminal
set, equipped with its unique group structure, and we have already
computed [products](Algebra.Group.Ab.Sum.html) --- they are given by
direct sums.

```agda
Ab-is-additive : is-additive (Ab ℓ)
Ab-is-additive .has-ab = Ab-ab
Ab-is-additive .has-terminal .top =
  restrict (to-group p) λ _ _ → refl where
    p : make-group (Lift _ ⊤)
    p .group-is-set a b p q i j = lift tt
    p .unit = lift tt
    p .mul _ _ = lift tt
    p .inv _ = lift tt
    p .assoc x y z i = lift tt
    p .invl x i = lift tt
    p .invr x i = lift tt
    p .idl x i = lift tt
Ab-is-additive .has-terminal .has⊤ x =
  contr (total-hom (λ _ → lift tt) record { pres-⋆ = λ _ _ → refl }) λ h →
    Forget-is-faithful refl

Ab-is-additive .has-prods A B .Product.apex = A ⊕ B
Ab-is-additive .has-prods A B .Product.π₁ = _
Ab-is-additive .has-prods A B .Product.π₂ = _
Ab-is-additive .has-prods A B .Product.has-is-product = Direct-sum-is-product
```
