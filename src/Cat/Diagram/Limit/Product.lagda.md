---
description: |
  A correspondence is established between concretely-defined product
  diagrams and general limits of discrete diagrams.
---

<!--
```agda
open import Cat.Instances.Shape.Terminal
open import Cat.Diagram.Product.Indexed
open import Cat.Instances.Discrete.Pre
open import Cat.Instances.Shape.Two
open import Cat.Diagram.Limit.Base
open import Cat.Functor.Kan.Unique
open import Cat.Functor.Naturality
open import Cat.Instances.Discrete
open import Cat.Functor.Constant
open import Cat.Functor.Kan.Base
open import Cat.Diagram.Product
open import Cat.Prelude

open import Data.Bool

import Cat.Functor.Reasoning
import Cat.Reasoning
```
-->

```agda
module Cat.Diagram.Limit.Product where
```

<!--
```agda
module _ {o h} (C : Precategory o h)  where
  open Cat.Reasoning C

  open is-product
  open Product
  open Functor
  open _=>_

```
-->

# Products are limits {defines="products-as-limits"}

We establish the correspondence between binary products $A \times B$ and
limits over the functor out of the [[two-object category]] which maps $0$
to $A$ and $1$ to $B$.

The two-way correspondence between products and terminal cones is
simple enough to establish by appropriately shuffling the data.

```agda
  is-product→is-limit
    : ∀ {x} {F : Functor 2-object-category C} {eps : Const x => F}
    → is-product C (eps .η true) (eps .η false)
    → is-limit {C = C} F x eps
  is-product→is-limit {x = x} {F} {eps} is-prod =
    to-is-limitp ml λ where
      {true} → refl
      {false} → refl
    where
      module is-prod = is-product is-prod
      open make-is-limit

      ml : make-is-limit F x
      ml .ψ j = eps .η j
      ml .commutes f = sym (eps .is-natural _ _ _) ∙ idr _
      ml .universal eps _ = is-prod.⟨ eps true , eps false ⟩
      ml .factors {true} eps _ = is-prod.π₁∘⟨⟩
      ml .factors {false} eps _ = is-prod.π₂∘⟨⟩
      ml .unique eps p other q = is-prod.unique (q true) (q false)

  is-limit→is-product
    : ∀ {a b} {K : Functor ⊤Cat C}
    → {eps : K F∘ !F => 2-object-diagram a b}
    → is-ran !F (2-object-diagram a b) K eps
    → is-product C (eps .η true) (eps .η false)
  is-limit→is-product {a} {b} {K} {eps} lim = prod where
    module lim = is-limit lim

    D : Functor 2-object-category C
    D = 2-object-diagram a b

    pair
      : ∀ {y} → Hom y a → Hom y b
      → ∀ (j : Bool) → Hom y (D .F₀ j)
    pair p1 p2 true = p1
    pair p1 p2 false = p2

    pair-commutes
      : ∀ {y} {p1 : Hom y a} {p2 : Hom y b}
      → {i j : Bool}
      → (p : i ≡ j)
      → D .F₁ p ∘ pair p1 p2 i ≡ pair p1 p2 j
    pair-commutes {p1 = p1} {p2 = p2} =
        J (λ _ p → D .F₁ p ∘ pair p1 p2 _ ≡ pair p1 p2 _)
          (eliml (D .F-id))

    prod : is-product C (eps .η true) (eps .η false)
    prod .⟨_,_⟩ f g = lim.universal (pair f g) pair-commutes
    prod .π₁∘⟨⟩ {_} {p1'} {p2'} = lim.factors (pair p1' p2') pair-commutes
    prod .π₂∘⟨⟩ {_} {p1'} {p2'} = lim.factors (pair p1' p2') pair-commutes
    prod .unique {other = other} p q = lim.unique _ _ other λ where
      true → p
      false → q

  Product→Limit : ∀ {F : Functor 2-object-category C} → Product C (F · true) (F · false) → Limit F
  Product→Limit prod = to-limit (is-product→is-limit {eps = 2-object-nat-trans _ _} (has-is-product prod))

  Limit→Product : ∀ {a b} → Limit (2-object-diagram a b) → Product C a b
  Limit→Product lim .apex = Limit.apex lim
  Limit→Product lim .π₁ = Limit.cone lim .η true
  Limit→Product lim .π₂ = Limit.cone lim .η false
  Limit→Product lim .has-is-product =
    is-limit→is-product (Limit.has-limit lim)
```

## Indexed products as limits

We can also compute the *indexed* product of a *family* $F : I \to \cC$
of objects as a limit, replacing the function $F$ with a diagram indexed
by the [[fundamental pregroupoid]] of $I$.

```agda
  module _ {ℓ} {I : Type ℓ} (F : I → Ob) where
    open _=>_

    Proj→Cone : ∀ {x} → (∀ i → Hom x (F i)) → Const x => Π₁-adjunct C F
    Proj→Cone π .η i = π i
    Proj→Cone π .is-natural i j = elim! $
      J (λ j p →  π j ∘ id ≡ subst (Hom (F i) ⊙ F) p id ∘ π i)
        (idr _ ∙ introl (transport-refl id))

    is-indexed-product→is-limit
      : ∀ {x} {π : ∀ i → Hom x (F i)}
      → is-indexed-product C F π
      → is-limit (Π₁-adjunct C F) x (Proj→Cone π)
    is-indexed-product→is-limit {x = x} {π} ip = to-is-limitp ml refl where
      module ip = is-indexed-product ip
      open make-is-limit

      ml : make-is-limit (Π₁-adjunct C F) x
      ml .ψ j = π j
      ml .commutes {i} {j} = elim! $
        J (λ j p → subst (Hom (F i) ⊙ F) p id ∘ π i ≡ π j)
          (eliml (transport-refl _))
      ml .universal eps p = ip.tuple eps
      ml .factors eps p = ip.commute
      ml .unique eps p other q = ip.unique eps q

    is-limit→is-indexed-product
      : ∀ {K : Functor ⊤Cat C}
      → {eps : K F∘ !F => Π₁-adjunct C F}
      → is-ran !F (Π₁-adjunct C F) K eps
      → is-indexed-product C F (eps .η)
    is-limit→is-indexed-product {K = K} {eps} lim = ip where
      module lim = is-limit lim
      open is-indexed-product

      ip : is-indexed-product C F (eps .η)
      ip .tuple k = lim.universal k comm where abstract
        comm : {x y : I} (h : ∥ x ≡ y ∥₀) → Π₁-adjunct₁ C F h ∘ k x ≡ k y
        comm {x} = elim! $ J
          (λ y p → path→iso (ap F p) .to ∘ k x ≡ k y) (eliml (transport-refl _))
      ip .commute       = lim.factors _ _
      ip .unique k comm = lim.unique _ _ _ comm

    IP→Limit : Indexed-product C F → Limit (Π₁-adjunct C F)
    IP→Limit ip = to-limit (is-indexed-product→is-limit has-is-ip)
      where open Indexed-product ip

    Limit→IP : Limit (Π₁-adjunct C F) → Indexed-product C F
    Limit→IP lim .Indexed-product.ΠF = _
    Limit→IP lim .Indexed-product.π  = _
    Limit→IP lim .Indexed-product.has-is-ip = is-limit→is-indexed-product $
      Limit.has-limit lim

module _ {o h ℓ o' h'} {C : Precategory o h} {D : Precategory o' h'} {F : Functor C D} {idx : Type ℓ} ⦃ i-is-grpd : H-Level idx 3 ⦄ (d : idx → C .Precategory.Ob) (F-cont : is-continuous ℓ ℓ F) where
  private
    module F = Cat.Functor.Reasoning F
    module C = Cat.Reasoning C
    module D = Cat.Reasoning D

  is-continuous→pres-indexed-product : ∀ {x} {π : ∀ i → C.Hom x (d i)} → is-indexed-product C d π → is-indexed-product D (λ i → F.₀ (d i)) (λ i → F.₁ (π i))
  is-continuous→pres-indexed-product {x} {π} prod = record where
    lim = F-cont $ is-indexed-product→is-limit _ _ prod
    module lim = make-is-limit (unmake-limit lim)

    tuple {Y} k = lim.universal k λ {y'} → elim! $ J
      (λ y p → F.₁ (subst (λ y → C.Hom (d y') (d y)) p C.id) D.∘ k y' ≡ k y)
      (F.eliml (transport-refl _))
    commute = lim.factors _ _
    unique k comm = lim.unique _ _ _ comm
```
