<!--
```agda
open import Cat.Functor.Adjoint.Reflective
open import Cat.Instances.Presheaf.Limits
open import Cat.Diagram.Limit.Finite
open import Cat.Functor.Properties
open import Cat.Instances.Functor
open import Cat.Diagram.Pullback
open import Cat.Diagram.Terminal
open import Cat.Diagram.Product
open import Cat.Functor.Adjoint
open import Cat.Prelude

open import Topoi.Base

import Cat.Functor.Reasoning as Func
import Cat.Reasoning as Cat
```
-->

```agda
module Topoi.Reasoning where
```

# Reasoning in topoi

As mentioned in the [overture on topos theory], categories of sheaves
are incredibly nice categories to work in _logically_, mirroring many of
the same properties of the category of Sets. This follows from the fact
that they are [[reflective subcategories]] of presheaf categories, and
_those_ categories enjoy many of the exactness properties of $\Sets$ by
virtue of being functor categories.

[overture on topos theory]: Topoi.Base.html

This module provides a companion to the overture which makes it more
convenient to reason about a _particular_ sheaf topos by computing
explicit descriptions of [[finite limits]] and [[colimits]], and
establishing the key exactness properties of a topos: Coproducts are
disjoint, equivalence relations are effective, and colimits are stable
under pullback.

```agda
module Sheaf-topos {o ℓ} {𝒯 : Precategory o ℓ} (T : Topos ℓ 𝒯) where
  open Cat 𝒯 public
  open _⊣_ (T .Topos.L⊣ι) public

  module L = Func (T .Topos.L)
  module L-lex = is-lex (T .Topos.L-lex)
  module ι = Func (T .Topos.ι)

  open Topos T using (site) public

  module Presh = Cat (PSh ℓ site)

  Lι-iso : ∀ x → is-invertible (counit.ε x)
  Lι-iso x = iso→invertible
    (is-reflective→counit-is-iso (T .Topos.L⊣ι) (T .Topos.has-ff))

  ε⁻¹ : Id => T .Topos.L F∘ T .Topos.ι
  ε⁻¹ = Cat._≅_.from (is-reflective→counit-iso (T .Topos.L⊣ι) (T .Topos.has-ff))
  module ε⁻¹ = _=>_ ε⁻¹

  psh-equal : ∀ {X Y} {f g : Hom X Y} → ι.₁ f ≡ ι.₁ g → f ≡ g
  psh-equal = ff→faithful {F = T .Topos.ι} (T .Topos.has-ff)
```

::: terminology
We will refer to the objects of $\mathcal{C}$, the topos, as
**sheaves**, and the objects of $[S\op,\Sets]$ as **presheaves**.
Correspondingly, the [[left adjoint]] functor $[S\op, \Sets] \to
\mathcal{C}$ is called **sheafification**.
:::

## Limits

Since the sheafification functor is left exact and the inclusion functor
is [[fully faithful]] (thus the adjunction counit is an isomorphism, c.f.
`Lι-iso`{.Agda}), we can compute limits directly in the presheaf
category and sheafify. Unfolding the result of this procedure, rather
than appealing to the equivalence $\mathcal{C} \cong
[S\op,\Sets]^{L\iota}$, yields much better computational properties. We
do it by hand for the [[terminal object]], binary [[products]], and binary
[[pullbacks]].

```agda
  open Terminal
  terminal-sheaf : Terminal 𝒯
  terminal-sheaf .top = L.₀ (PSh-terminal _ site .top)
  terminal-sheaf .has-is-term = L-lex.pres-⊤ (PSh-terminal _ site .has-is-term)

  product-sheaf : ∀ A B → Product 𝒯 A B
  product-sheaf A B = product' where
    product-presheaf : Product (PSh ℓ site) (ι.₀ A) (ι.₀ B)
    product-presheaf = PSh-products _ site _ _

    open Product
    product' : Product 𝒯 A B
    product' .apex = L.₀ (product-presheaf .apex)
    product' .π₁ = counit.ε _ ∘ L.₁ (product-presheaf .π₁)
    product' .π₂ = counit.ε _ ∘ L.₁ (product-presheaf .π₂)
    product' .has-is-product =
      let
        prod =
          L-lex.pres-product
            (PSh-terminal _ site .has-is-term)
            (product-presheaf .has-is-product)
      in is-product-iso (Lι-iso _) (Lι-iso _) prod

  open Binary-products 𝒯 product-sheaf public
```

The computation for finite connected limits (pullbacks, equalisers) is a
bit more involved, but not by much:

```agda
  pullback-sheaf
    : ∀ {X Y Z} (f : Hom X Z) (g : Hom Y Z)
    → Pullback 𝒯 f g
  pullback-sheaf f g = pullback' where
    pullback-presheaf : Pullback (PSh ℓ site) (ι.₁ f) (ι.₁ g)
    pullback-presheaf = PSh-pullbacks _ site _ _

    open Pullback
    open is-pullback
    module Pb = Pullback pullback-presheaf
    module lpb = is-pullback (L-lex.pres-pullback (pullback-presheaf .has-is-pb))

    pullback' : Pullback 𝒯 f g
    pullback' .apex = L.₀ Pb.apex
    pullback' .p₁ = counit.ε _ ∘ L.₁ Pb.p₁
    pullback' .p₂ = counit.ε _ ∘ L.₁ Pb.p₂
    pullback' .has-is-pb = pb' where
      pb' : is-pullback 𝒯 _ f _ g
      pb' .square = square' where abstract
        square' : f ∘ counit.ε _ ∘ L.₁ Pb.p₁ ≡ g ∘ counit.ε _ ∘ L.₁ Pb.p₂
        square' =
          f ∘ counit.ε _ ∘ L.₁ Pb.p₁           ≡⟨ extendl (sym (counit.is-natural _ _ _)) ⟩
          counit.ε _ ∘ L.₁ (ι.₁ f) ∘ L.₁ Pb.p₁ ≡⟨ refl⟩∘⟨ lpb.square ⟩
          counit.ε _ ∘ L.₁ (ι.₁ g) ∘ L.₁ Pb.p₂ ≡⟨ extendl (counit.is-natural _ _ _) ⟩
          g ∘ counit.ε _ ∘ L.₁ Pb.p₂           ∎

      pb' .universal {p₁' = p₁'} {p₂'} p =
        lpb.universal {p₁' = ε⁻¹.η _ ∘ p₁'} {p₂' = ε⁻¹.η _ ∘ p₂'} path
        where abstract
          path : L.₁ (ι.₁ f) ∘ ε⁻¹.η _ ∘ p₁' ≡ L.₁ (ι.₁ g) ∘ ε⁻¹.η _ ∘ p₂'
          path =
            L.₁ (ι.₁ f) ∘ ε⁻¹.η _ ∘ p₁' ≡⟨ extendl (sym (ε⁻¹.is-natural _ _ _)) ⟩
            ε⁻¹.η _ ∘ f ∘ p₁'           ≡⟨ refl⟩∘⟨ p ⟩
            ε⁻¹.η _ ∘ g ∘ p₂'           ≡⟨ extendl (ε⁻¹.is-natural _ _ _) ⟩
            L.₁ (ι.₁ g) ∘ ε⁻¹.η _ ∘ p₂' ∎

      pb' .p₁∘universal =
        pullr lpb.p₁∘universal ∙ cancell (Lι-iso _ .is-invertible.invl)
      pb' .p₂∘universal =
        pullr lpb.p₂∘universal ∙ cancell (Lι-iso _ .is-invertible.invl)
      pb' .unique p q = lpb.unique
        (sym ( ap₂ _∘_ refl (sym p ∙ sym (assoc _ _ _))
             ∙ cancell (Lι-iso _ .is-invertible.invr)))
        (sym ( ap₂ _∘_ refl (sym q ∙ sym (assoc _ _ _))
             ∙ cancell (Lι-iso _ .is-invertible.invr)))

  finitely-complete : Finitely-complete 𝒯
  finitely-complete .Finitely-complete.terminal = terminal-sheaf
  finitely-complete .Finitely-complete.products = product-sheaf
  finitely-complete .Finitely-complete.equalisers =
    with-pullbacks 𝒯 terminal-sheaf pullback-sheaf
      .Finitely-complete.equalisers
  finitely-complete .Finitely-complete.pullbacks = pullback-sheaf
```
