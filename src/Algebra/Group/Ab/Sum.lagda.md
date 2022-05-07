```agda
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
  _⊕_ = ((G.₀ × H.₀) , grp) , ab where
    grp : Group-on (G.₀ × H.₀)
    grp = make-group (hlevel 2) (G.unit , H.unit)
      (λ { (a , x) (b , y) → a G.⋆ b , x H.⋆ y })
      (λ { (a , x) → a G.⁻¹ , x H.⁻¹ })
      (λ { _ _ _ → Σ-pathp (sym G.associative) (sym H.associative) })
      (λ _ → Σ-pathp G.inversel H.inversel)
      (λ _ → Σ-pathp G.inverser H.inverser)
      λ _ → Σ-pathp G.idl H.idl

    ab : is-abelian-group ((G.₀ × H.₀) , grp)
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
homomorphism is as in $\sets$: The existence of a [left adjoint] free
abelian group functor $\sets \to \Ab$ implies that limits in $\Ab$ are
computed as in $\sets$ (namely, because the _forgetful_ functor $U : \Ab
\to \sets$ is a _right_ adjoint, and [right adjoints preserve
limits][rapl]).

[left adjoint]: Cat.Functor.Adjoint.html
[rapl]: Cat.Functor.Adjoint.Continuous.html

```agda
  ⊕-proj₁ : Ab.Hom (G ⊕ H) G
  ⊕-proj₁ .fst = fst
  ⊕-proj₁ .snd .pres-⋆ x y = refl

  ⊕-proj₂ : Ab.Hom (G ⊕ H) H
  ⊕-proj₂ .fst = snd
  ⊕-proj₂ .snd .pres-⋆ x y = refl

  open Ab.is-product
  Direct-sum-is-product : Ab.is-product {A = G} {H} {G ⊕ H} ⊕-proj₁ ⊕-proj₂
  Direct-sum-is-product .⟨_,_⟩ f g .fst x = f .fst x , g .fst x
  Direct-sum-is-product .⟨_,_⟩ f g .snd .pres-⋆ x y =
    Σ-pathp (f .snd .pres-⋆ x y) (g .snd .pres-⋆ x y)
  Direct-sum-is-product .π₁∘factor = Forget-is-faithful refl
  Direct-sum-is-product .π₂∘factor = Forget-is-faithful refl
  Direct-sum-is-product .unique other p q = Forget-is-faithful $ funext λ x →
    Σ-pathp (happly (ap fst p) x) (happly (ap fst q) x)
```
