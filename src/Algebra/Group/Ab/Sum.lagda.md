```agda
open import Algebra.Group.Cat.FinitelyComplete
open import Algebra.Group.Cat.Base
open import Algebra.Group.Ab
open import Algebra.Prelude
open import Algebra.Group

module Algebra.Group.Ab.Sum where
```

<!--
```agda
module _ {ℓ} (G H : AbGroup ℓ) where
  private
    module G = AbGrp G
    module H = AbGrp H
```
-->

# Direct sum of abelian groups

Let $G, H : \Ab$ be two [abelian groups]; We construct their [coproduct]
in the category of abelian groups by equipping the set $G_0 \times H_0$
with the "pointwise" group structure. While this might seem like an odd
way of constructing a coproduct --- after all, $G_0 \times H_0$ is
literally a product --- remember that in [$\Ab$-categories] (like $\Ab$
itself, in this case), finite [products and coproducts coincide][additive].

So, despite the name "direct sum", _and_ despite the preceding
paragraph, the structure we build is actually the [_product_] in $\Ab$ of
$G$ and $H$. However, we do not refer to this limit as a product ---
opting to use "direct sum" instead --- because the more important notion
of product in $\Ab$ is the [tensor product of abelian groups][tensor].

[coproduct]: Cat.Diagram.Coproduct.html
[abelian groups]: Algebra.Group.Ab.html#abelian-groups
[$\Ab$-categories]: Cat.Abelian.Base.html#ab-enriched-categories
[additive]: Cat.Abelian.Base.html#additive-categories
[_product_]: Cat.Diagram.Product.html
[tensor]: Algebra.Group.Ab.html#the-tensor-product

```agda
  _⊕_ : AbGroup ℓ
  _⊕_ = restrict (Direct-product (G .object) (H .object)) ab where
    ab : is-abelian-group (Direct-product (G .object) (H .object) .snd)
    ab x y = Σ-pathp G.commutative H.commutative
```

<!--
```agda
module _ {ℓ} {G H : AbGroup ℓ} where
  private
    module G = AbGrp G
    module H = AbGrp H
  open Group-hom
```
-->

The construction of the projection homomorphisms and the "limiting"
homomorphism is as in $\Sets$: The existence of a [left adjoint] free
abelian group functor $\Sets \to \Ab$ implies that limits in $\Ab$ are
computed as in $\Sets$ (namely, because the _forgetful_ functor $U : \Ab
\to \Sets$ is a _right_ adjoint, and [right adjoints preserve
limits][rapl]).

[left adjoint]: Cat.Functor.Adjoint.html
[rapl]: Cat.Functor.Adjoint.Continuous.html

```agda
  ⊕-proj₁ : Ab.Hom (G ⊕ H) G
  ⊕-proj₁ .hom = fst
  ⊕-proj₁ .preserves .pres-⋆ x y = refl

  ⊕-proj₂ : Ab.Hom (G ⊕ H) H
  ⊕-proj₂ .hom = snd
  ⊕-proj₂ .preserves .pres-⋆ x y = refl

  open Ab.is-product
  Direct-sum-is-product : Ab.is-product {A = G} {H} {G ⊕ H} ⊕-proj₁ ⊕-proj₂
  Direct-sum-is-product .⟨_,_⟩ f g .hom x = f # x , g # x
  Direct-sum-is-product .⟨_,_⟩ f g .preserves .pres-⋆ x y =
    Σ-pathp (f .preserves .pres-⋆ x y) (g .preserves .pres-⋆ x y)

  Direct-sum-is-product .π₁∘factor = Forget-is-faithful refl
  Direct-sum-is-product .π₂∘factor = Forget-is-faithful refl
  Direct-sum-is-product .unique other p q = Forget-is-faithful $ funext λ x →
    Σ-pathp (p #ₚ x) (q #ₚ x)
```
