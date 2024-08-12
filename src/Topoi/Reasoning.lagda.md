<!--
```agda
open import Cat.CartesianClosed.Instances.PSh
open import Cat.Functor.Adjoint.Reflective
open import Cat.Diagram.Everything
open import Cat.Functor.Properties
open import Cat.Instances.Functor
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
  terminal-sheaf .top = L.₀ (PSh-terminal {C = site} .top)
  terminal-sheaf .has⊤ = L-lex.pres-⊤ (PSh-terminal {C = site} .has⊤)

  products-sheaf : Binary-products 𝒯
  products-sheaf =
    has-products→binary-products λ A B →
    is-product-iso (Lι-iso A) (Lι-iso B) $
    L-lex.pres-product
      (PSh-terminal {C = site} .has⊤)
      (PSh-products {C = site} .Binary-products.has-is-product)

  open Binary-products products-sheaf public
```

The computation for finite connected limits (pullbacks, equalisers) is a
bit more involved, but not by much:

```agda
  pullbacks-sheaf : Pullbacks 𝒯
  pullbacks-sheaf =
    has-pullbacks→pullbacks λ {X} {Y} {Z} f g →
    is-pullback-inner (Lι-iso X) (Lι-iso Y) (Lι-iso Z)
      (sym (counit.is-natural _ _ f))
      (sym (counit.is-natural _ _ g))
      (L-lex.pres-pullback (PSh-pullbacks {C = site} .Pullbacks.has-is-pb))

  finitely-complete : Finitely-complete 𝒯
  finitely-complete .Finitely-complete.terminal = terminal-sheaf
  finitely-complete .Finitely-complete.products = products-sheaf
  finitely-complete .Finitely-complete.equalisers =
    with-pullbacks 𝒯 terminal-sheaf pullbacks-sheaf
      .Finitely-complete.equalisers
  finitely-complete .Finitely-complete.pullbacks = pullbacks-sheaf
```
