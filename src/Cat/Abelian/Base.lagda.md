<!--
```agda
open import Algebra.Group.Ab.Tensor
open import Algebra.Group.Ab
open import Algebra.Monoid
open import Algebra.Group

open import Cat.Diagram.Equaliser.Kernel
open import Cat.Diagram.Coequaliser
open import Cat.Diagram.Biproduct
open import Cat.Diagram.Coproduct
open import Cat.Diagram.Terminal
open import Cat.Diagram.Product
open import Cat.Displayed.Total
open import Cat.Instances.Slice
open import Cat.Diagram.Zero
open import Cat.Prelude hiding (_+_ ; _*_ ; _-_)

import Algebra.Group.Cat.Base as Grp
import Algebra.Group.Ab.Hom as Ab

import Cat.Reasoning as Cat

open ∫Hom
```
-->

```agda
module Cat.Abelian.Base where
```

# Abelian categories

This module defines the sequence of properties which "work up to"
abelian categories: Ab-enriched categories, pre-additive categories,
pre-abelian categories, and abelian categories. Each concept builds on
the last by adding a new categorical property on top of a precategory.

## Ab-enriched categories {defines="ab-enriched-category"}

An $\Ab$-enriched category is one where each $\hom$ set carries the
structure of an [[Abelian group]], such that the composition map is
_bilinear_, hence extending to an Abelian group homomorphism

$$
\hom(b, c) \otimes \hom(a, b) \to \hom(a, c)
$$,

where the term on the left is the [[tensor product|tensor product of
abelian groups]] of the corresponding $\hom$-groups. As the name
implies, every such category has a canonical $\Ab$-enrichment (made
monoidal using $- \otimes -$), but we do not use the language of
enriched category theory in our development of Abelian categories.

[zero object]: Cat.Diagram.Zero.html

```agda
record Ab-category {o ℓ} (C : Precategory o ℓ) : Type (o ⊔ lsuc ℓ) where
  open Cat C public
  field
    Abelian-group-on-hom : ∀ A B → Abelian-group-on (Hom A B)

  module Hom {A B} = Abelian-group-on (Abelian-group-on-hom A B) renaming (_⁻¹ to inverse)
  open Hom
    using (zero-diff)
    renaming (_—_ to _-_ ; _*_ to _+_ ; 1g to 0m)
    public

  Hom-grp : ∀ A B → Abelian-group ℓ
  Hom-grp A B = (el (Hom A B) (Hom-set A B)) , Abelian-group-on-hom A B

  field
    -- Composition is multilinear:
    ∘-linear-l
      : ∀ {A B C} (f g : Hom B C) (h : Hom A B)
      → (f ∘ h) + (g ∘ h) ≡ (f + g) ∘ h
    ∘-linear-r
      : ∀ {A B C} (f : Hom B C) (g h : Hom A B)
      → (f ∘ g) + (f ∘ h) ≡ f ∘ (g + h)

  ∘map : ∀ {A B C} → Ab.Hom (Hom-grp B C ⊗ Hom-grp A B) (Hom-grp A C)
  ∘map {A} {B} {C} = from-bilinear-map record where
    map           = _∘_
    pres-*l x y z = sym (∘-linear-l x y z)
    pres-*r x y z = sym (∘-linear-r x y z)
```

<details>
<summary> Note that from multilinearity of composition, it follows that
the addition of $\hom$-groups and composition^["multiplication"]
operations satisfy familiar algebraic identities, e.g. $0f = f0 = 0$,
$-ab = (-a)b = a(-b)$, etc.</summary>

```agda
  ∘-zero-r : ∀ {A B C} {f : Hom B C} → f ∘ 0m {A} {B} ≡ 0m
  ∘-zero-r {f = f} =
    f ∘ 0m                     ≡⟨ Hom.intror Hom.inverser ⟩
    f ∘ 0m + (f ∘ 0m - f ∘ 0m) ≡⟨ Hom.associative ⟩
    (f ∘ 0m + f ∘ 0m) - f ∘ 0m ≡⟨ ap (_- f ∘ 0m) (∘-linear-r _ _ _) ⟩
    (f ∘ (0m + 0m)) - f ∘ 0m   ≡⟨ ap ((_- f ∘ 0m) ⊙ (f ∘_)) Hom.idl ⟩
    (f ∘ 0m) - f ∘ 0m          ≡⟨ Hom.inverser ⟩
    0m                         ∎

  ∘-zero-l : ∀ {A B C} {f : Hom A B} → 0m ∘ f ≡ 0m {A} {C}
  ∘-zero-l {f = f} =
    0m ∘ f                                   ≡⟨ Hom.introl Hom.inversel ⟩
    (Hom.inverse (0m ∘ f) + 0m ∘ f) + 0m ∘ f ≡⟨ sym Hom.associative ⟩
    Hom.inverse (0m ∘ f) + (0m ∘ f + 0m ∘ f) ≡⟨ ap (Hom.inverse (0m ∘ f) +_) (∘-linear-l _ _ _) ⟩
    Hom.inverse (0m ∘ f) + ((0m + 0m) ∘ f)   ≡⟨ ap ((Hom.inverse (0m ∘ f) +_) ⊙ (_∘ f)) Hom.idl ⟩
    Hom.inverse (0m ∘ f) + (0m ∘ f)          ≡⟨ Hom.inversel ⟩
    0m                                       ∎

  ∘-negatel
    : ∀ {A B C} {g : Hom B C} {h : Hom A B}
    → Hom.inverse (g ∘ h) ≡ Hom.inverse g ∘ h
  ∘-negatel {g = g} {h} = monoid-inverse-unique Hom.has-is-monoid (g ∘ h) _ _
    Hom.inversel
    (∘-linear-l _ _ _ ∙ ap (_∘ h) Hom.inverser ∙ ∘-zero-l)

  ∘-negater
    : ∀ {A B C} {g : Hom B C} {h : Hom A B}
    → Hom.inverse (g ∘ h) ≡ g ∘ Hom.inverse h
  ∘-negater {g = g} {h} = monoid-inverse-unique Hom.has-is-monoid (g ∘ h) _ _
    Hom.inversel
    (∘-linear-r _ _ _ ∙ ap (g ∘_) Hom.inverser ∙ ∘-zero-r)

  ∘-minus-l
    : ∀ {A B C} (f g : Hom B C) (h : Hom A B)
    → (f ∘ h) - (g ∘ h) ≡ (f - g) ∘ h
  ∘-minus-l f g h =
    f ∘ h - g ∘ h               ≡⟨ ap (f ∘ h +_) ∘-negatel ⟩
    f ∘ h + (Hom.inverse g ∘ h) ≡⟨ ∘-linear-l _ _ _ ⟩
    (f - g) ∘ h                 ∎

  ∘-minus-r
    : ∀ {A B C} (f : Hom B C) (g h : Hom A B)
    → (f ∘ g) - (f ∘ h) ≡ f ∘ (g - h)
  ∘-minus-r f g h =
    f ∘ g - f ∘ h               ≡⟨ ap (f ∘ g +_) ∘-negater ⟩
    f ∘ g + (f ∘ Hom.inverse h) ≡⟨ ∘-linear-r _ _ _ ⟩
    f ∘ (g - h)                 ∎
```

</details>

Before moving on, we note the following property of $\Ab$-categories: If
$A$ is an object s.t. $\id_A = 0$, then $A$ is a zero object.

```agda
module _ {o ℓ} {C : Precategory o ℓ} (A : Ab-category C) where
  private module A = Ab-category A

  id-zero→zero : ∀ {X} → A.id {X} ≡ A.0m → is-zero C X
  id-zero→zero idm .is-zero.has-is-initial B = contr A.0m λ h → sym $
    h                                ≡⟨ A.intror refl ⟩
    h A.∘ A.id                       ≡⟨ A.refl⟩∘⟨ idm ⟩
    h A.∘ A.0m                       ≡⟨ A.∘-zero-r ⟩
    A.0m                             ∎
  id-zero→zero idm .is-zero.has-is-terminal x = contr A.0m λ h → sym $
    h                              ≡⟨ A.introl refl ⟩
    A.id A.∘ h                     ≡⟨ idm A.⟩∘⟨refl ⟩
    A.0m A.∘ h                     ≡⟨ A.∘-zero-l ⟩
    A.0m                           ∎
```

Perhaps the simplest example of an $\Ab$-category is.. any ring! In the
same way that a monoid is a category with one object, and a group is a
groupoid with one object, a ring is a _ringoid_ with one object; Ringoid
being another word for $\Ab$-category, rather than a horizontal
categorification of the drummer for the Beatles. The next simplest
example is $\Ab$ itself:

```agda
module _ where
  open Ab-category
  Ab-ab-category : ∀ {ℓ} → Ab-category (Ab ℓ)
  Ab-ab-category .Abelian-group-on-hom A B = Ab.Abelian-group-on-hom A B
  Ab-ab-category .∘-linear-l f g h = ext λ _ → refl
  Ab-ab-category .∘-linear-r f g h = ext λ _ →
    sym (f .snd .is-group-hom.pres-⋆ _ _)
```

## Additive categories {defines="additive-category"}

An $\Ab$-category is **additive** when its underlying category has a
[[terminal object]] and finite [[products]]; By the yoga above, this
implies that the terminal object is also a zero object, and the finite
products coincide with finite coproducts.

```agda
record is-additive {o ℓ} (C : Precategory o ℓ) : Type (o ⊔ lsuc ℓ) where
  field has-ab : Ab-category C
  open Ab-category has-ab public

  field
    has-terminal : Terminal C
    has-prods    : ∀ A B → Product C A B

  ∅ : Zero C
  ∅ .Zero.∅ = has-terminal .Terminal.top
  ∅ .Zero.has-is-zero = id-zero→zero has-ab $
    is-contr→is-prop (has-terminal .Terminal.has⊤ _) _ _
  module ∅ = Zero ∅

  0m-unique : ∀ {A B} → ∅.zero→ {A} {B} ≡ 0m
  0m-unique = ap₂ _∘_ (∅.has⊥ _ .paths _) refl ∙ ∘-zero-l
```

Coincidence of finite products and finite coproducts leads to an object
commonly called a (finite) **[[biproduct]]**. The coproduct coprojections
are given by the pair of maps

$$
\begin{align*}
&\langle \id , 0 \rangle : A \to A \times B \\
&\langle 0 , \id \rangle : B \to A \times B\text{,}
\end{align*}
$$

respectively, and the comultiplication of $f$ and $g$ is given by
$f\pi_1 + g\pi_2$. We can calculate, for the first coprojection followed
by comultiplication,

$$
\begin{align*}
& (f\pi_1+g\pi_2) \langle \id , 0 \rangle \\
=& f\pi_1\langle \id , 0 \rangle + g\pi_2\langle \id , 0 \rangle \\
=& f\id + g0 \\
=& f\text{,}
\end{align*}
$$

and analogously for the second coprojection followed by
comultiplication.

```agda
  private module Prod = Binary-products C has-prods
  open Prod

  has-coprods : ∀ A B → Coproduct C A B
  has-coprods A B = coprod where
    open Coproduct
    open is-coproduct
    coprod : Coproduct C A B
    coprod .coapex = A ⊗₀ B
    coprod .ι₁ = ⟨ id , 0m ⟩
    coprod .ι₂ = ⟨ 0m , id ⟩
    coprod .has-is-coproduct .[_,_] f g = f ∘ π₁ + g ∘ π₂
    coprod .has-is-coproduct .[]∘ι₁ {inj0 = f} {g} =
      (f ∘ π₁ + g ∘ π₂) ∘ ⟨ id , 0m ⟩ ≡⟨ sym (∘-linear-l _ _ _) ⟩
      (f ∘ π₁) ∘ ⟨ id , 0m ⟩ + _      ≡⟨ Hom.elimr (pullr π₂∘⟨⟩ ∙ ∘-zero-r) ⟩
      (f ∘ π₁) ∘ ⟨ id , 0m ⟩          ≡⟨ cancelr π₁∘⟨⟩ ⟩
      f                               ∎
    coprod .has-is-coproduct .[]∘ι₂ {inj0 = f} {g} =
      (f ∘ π₁ + g ∘ π₂) ∘ ⟨ 0m , id ⟩ ≡⟨ sym (∘-linear-l _ _ _) ⟩
      _ + (g ∘ π₂) ∘ ⟨ 0m , id ⟩      ≡⟨ Hom.eliml (pullr π₁∘⟨⟩ ∙ ∘-zero-r) ⟩
      (g ∘ π₂) ∘ ⟨ 0m , id ⟩          ≡⟨ cancelr π₂∘⟨⟩ ⟩
      g                               ∎
```

For uniqueness, we use distributivity of composition over addition of
morphisms and the universal property of the product to establish the
desired equation. Check it out:

```agda
    coprod .has-is-coproduct .unique {inj0 = f} {g} {other} p q = sym $
      f ∘ π₁ + g ∘ π₂                                         ≡⟨ ap₂ _+_ (pushl (sym p)) (pushl (sym q)) ⟩
      (other ∘ ⟨ id , 0m ⟩ ∘ π₁) + (other ∘ ⟨ 0m , id ⟩ ∘ π₂) ≡⟨ ∘-linear-r _ _ _ ⟩
      other ∘ (⟨ id , 0m ⟩ ∘ π₁ + ⟨ 0m , id ⟩ ∘ π₂)           ≡⟨ elimr lemma ⟩
      other                                                   ∎
      where
        lemma : ⟨ id , 0m ⟩ ∘ π₁ + ⟨ 0m , id ⟩ ∘ π₂
              ≡ id
        lemma = ⟨⟩-unique₂ {pr1 = π₁} {pr2 = π₂}
          (sym (∘-linear-r _ _ _) ∙ ap₂ _+_ (cancell π₁∘⟨⟩) (pulll π₁∘⟨⟩ ∙ ∘-zero-l) ∙ Hom.elimr refl)
          (sym (∘-linear-r _ _ _) ∙ ap₂ _+_ (pulll π₂∘⟨⟩ ∙ ∘-zero-l) (cancell π₂∘⟨⟩) ∙ Hom.eliml refl)
          (elimr refl)
          (elimr refl)

  module Coprod = Binary-coproducts C has-coprods
  open Coprod
```

Thus every additive category is [[semiadditive|semiadditive category]].

```agda
  additive→semiadditive : is-semiadditive C
  additive→semiadditive .is-semiadditive.has-zero = ∅
  additive→semiadditive .is-semiadditive.has-biproducts {A} {B} = bp where
    open is-biproduct
    bp : Biproduct C A B
    bp .Biproduct.biapex = A ⊗₀ B
    bp .Biproduct.π₁ = π₁
    bp .Biproduct.π₂ = π₂
    bp .Biproduct.ι₁ = ι₁
    bp .Biproduct.ι₂ = ι₂
    bp .Biproduct.has-is-biproduct .has-is-product = Prod.has-is-product
    bp .Biproduct.has-is-biproduct .has-is-coproduct = Coprod.has-is-coproduct
    bp .Biproduct.has-is-biproduct .πι₁ = π₁∘⟨⟩
    bp .Biproduct.has-is-biproduct .πι₂ = π₂∘⟨⟩
    bp .Biproduct.has-is-biproduct .ιπ-comm =
      ι₁ ∘ π₁ ∘ ι₂ ∘ π₂ ≡⟨ refl⟩∘⟨ pulll π₁∘⟨⟩ ⟩
      ι₁ ∘ 0m ∘ π₂      ≡⟨ pulll ∘-zero-r ∙ ∘-zero-l ⟩
      0m                ≡˘⟨ pulll ∘-zero-r ∙ ∘-zero-l ⟩
      ι₂ ∘ 0m ∘ π₁      ≡˘⟨ refl⟩∘⟨ pulll π₂∘⟨⟩ ⟩
      ι₂ ∘ π₂ ∘ ι₁ ∘ π₁ ∎

  open is-semiadditive additive→semiadditive hiding (∘-linear-l; ∘-linear-r)
```

As described there, every [[semiadditive category]] has its own enrichment
in commutative monoids. Since we already know that the zero morphisms
agree (`0m-unique`{.Agda}), it would be natural to expect that the
additions also agree; this is straightforward to check by linearity.

```agda
  enrichments-agree : ∀ {A B} {f g : Hom A B} → f +→ g ≡ f + g
  enrichments-agree {f = f} {g} =
    (id ∘ π₁ + id ∘ π₂) ∘ (f ⊗₁ g) ∘ δ      ≡⟨ ap₂ _+_ (idl _) (idl _) ⟩∘⟨refl ⟩
    (π₁ + π₂) ∘ (f ⊗₁ g) ∘ δ                ≡˘⟨ ∘-linear-l _ _ _ ⟩
    (π₁ ∘ (f ⊗₁ g) ∘ δ + π₂ ∘ (f ⊗₁ g) ∘ δ) ≡⟨ ap₂ _+_ (pulll π₁∘⟨⟩ ∙ cancelr π₁∘⟨⟩) (pulll π₂∘⟨⟩ ∙ cancelr π₂∘⟨⟩) ⟩
    f + g                                   ∎
```

Therefore, in order to get an additive category from a semiadditive
category, it suffices to ask for inverses for every morphism, so that
each $\hom$-monoid becomes a $\hom$-*group*.

<!--
```agda
module _ {o ℓ} (C : Precategory o ℓ) (semiadditive : is-semiadditive C) where
  open Cat C
  open is-semiadditive semiadditive
```
-->

```agda
  semiadditive+group→additive
    : (inv : ∀ {A B} → Hom A B → Hom A B)
    → (invl : ∀ {A B} {f : Hom A B} → inv f +→ f ≡ zero→)
    → is-additive C
  semiadditive+group→additive inv invl .is-additive.has-ab = ab where
    mk : ∀ {A B} → make-abelian-group (Hom A B)
    mk .make-abelian-group.ab-is-set = hlevel 2
    mk .make-abelian-group.mul = _+→_
    mk .make-abelian-group.inv = inv
    mk .make-abelian-group.1g = zero→
    mk .make-abelian-group.idl _ = +-idl
    mk .make-abelian-group.assoc _ _ _ = +-assoc
    mk .make-abelian-group.invl _ = invl
    mk .make-abelian-group.comm _ _ = +-comm

    ab : Ab-category C
    ab .Ab-category.Abelian-group-on-hom _ _  = to-abelian-group-on mk
    ab .Ab-category.∘-linear-l _ _ _ = ∘-linear-l
    ab .Ab-category.∘-linear-r _ _ _ = ∘-linear-r

  semiadditive+group→additive inv invl .is-additive.has-terminal = terminal
  semiadditive+group→additive inv invl .is-additive.has-prods _ _ = Biprod.product
```

## Pre-abelian & abelian categories {defines="pre-abelian-category abelian-category"}

An additive category is **pre-abelian** when it additionally has
[kernels] and cokernels, hence binary [[equalisers]] and [coequalisers]
where one of the maps is zero.

[kernels]: Cat.Diagram.Equaliser.Kernel.html
[coequalisers]: Cat.Diagram.Coequaliser.html

```agda
record is-pre-abelian {o ℓ} (C : Precategory o ℓ) : Type (o ⊔ lsuc ℓ) where
  field has-additive : is-additive C
  open is-additive has-additive public
  field
    kernel   : ∀ {A B} (f : Hom A B) → Kernel C ∅ f
    cokernel : ∀ {A B} (f : Hom A B) → Coequaliser C 0m f

  module Ker {A B} (f : Hom A B) = Kernel (kernel f)
  module Coker {A B} (f : Hom A B) = Coequaliser (cokernel f)
```

Every morphism $A \xto{f} B$ in a preabelian category admits a canonical
decomposition as

$$
A \xepi{p} \coker (\ker f) \xto{f'} \ker (\coker f) \xmono{i} B
$$,

where, as indicated, the map $p$ is an epimorphism (indeed a [regular
epimorphism], since it is a cokernel) and the map $i$ is a [regular
monomorphism].

[regular epimorphism]: Cat.Diagram.Coequaliser.RegularEpi.html
[regular monomorphism]: Cat.Diagram.Equaliser.RegularMono.html

```agda
  decompose
    : ∀ {A B} (f : Hom A B)
    → Σ[ f' ∈ Hom (Coker.coapex (Ker.kernel f)) (Ker.ker (Coker.coeq f)) ]
       (f ≡ Ker.kernel (Coker.coeq f) ∘ f' ∘ Coker.coeq (Ker.kernel f))
  decompose {A} {B} f = map , sym path
    where
      proj' : Hom (Coker.coapex (Ker.kernel f)) B
      proj' = Coker.universal (Ker.kernel f) {e' = f} $ sym path
```

<!--
```agda
        where abstract
          path : f ∘ kernel f .Kernel.kernel ≡ f ∘ 0m
          path = Ker.equal f
            ∙∙ ∅.zero-∘r _
            ∙∙ ap₂ _∘_ (∅.has⊥ _ .paths 0m) refl
            ∙∙ ∘-zero-l ∙∙ sym ∘-zero-r
```
-->

```agda
      map : Hom (Coker.coapex (Ker.kernel f)) (Ker.ker (Coker.coeq f))
      map = Ker.universal (Coker.coeq f) {e' = proj'} $ sym path
```

The existence of the map $f'$, and indeed of the maps $p$ and $i$,
follow from the universal properties of kernels and cokernels. The map
$p$ is the canonical quotient map $A \to \coker(f)$, and the map $i$ is
the canonical subobject inclusion $\ker(f) \to B$.

<!--
```agda
        where abstract
          path : ∅.zero→ ∘ proj' ≡ Coker.coeq f ∘ proj'
          path = Coker.unique₂ (Ker.kernel f)
            {e' = 0m} (∘-zero-r ∙ sym ∘-zero-l)
            (pushl (∅.zero-∘r _) ∙ pulll ( ap₂ _∘_ refl (∅.has⊤ _ .paths 0m)
                                               ∙ ∘-zero-r)
                 ∙ ∘-zero-l)
            (pullr (Coker.factors (Ker.kernel f)) ∙ sym (Coker.coequal _)
                 ∙ ∘-zero-r)

      path =
        Ker.kernel (Coker.coeq f) ∘ map ∘ Coker.coeq (Ker.kernel f) ≡⟨ pulll (Ker.factors _) ⟩
        proj' ∘ Coker.coeq (Ker.kernel f)                           ≡⟨ Coker.factors _ ⟩
        f                                                           ∎
```
-->

A pre-abelian category is **abelian** when the map $f'$ in the above
decomposition is an isomorphism.

```agda
record is-abelian {o ℓ} (C : Precategory o ℓ) : Type (o ⊔ lsuc ℓ) where
  field has-is-preab : is-pre-abelian C
  open is-pre-abelian has-is-preab public
  field
    coker-ker≃ker-coker
      : ∀ {A B} (f : Hom A B) → is-invertible (decompose f .fst)
```

This implies in particular that any monomorphism is a kernel, and every
epimorphism is a cokernel. Let's investigate the case for "every mono is
a kernel" first: Suppose that $f : A \mono B$ is some monomorphism;
We'll show that it's isomorphic to $\ker (\coker f)$ in the slice
category $\cA/B$.

```agda
  module _ {A B} (f : Hom A B) (monic : is-monic f) where
    private
      module m = Cat (Slice C B)
```

The map $A \to \ker (\coker f)$ is obtained as the composite

$$
A \xepi{p} \coker (\ker f) \cong \ker (\coker f)
$$,

where the isomorphism is our canonical map from before.

```agda
      f→kercoker : m.Hom (cut f) (cut (Ker.kernel (Coker.coeq f)))
      f→kercoker ./-Hom.map = decompose f .fst ∘ Coker.coeq (Ker.kernel f)
      f→kercoker ./-Hom.com = sym (decompose f .snd)
```

Conversely, map $\ker (\coker f) \to A$ is the composite

$$
\ker (\coker f) \cong \coker (\ker f) \to A
$$,

where the second map arises from the universal property of the cokernel:
We can map out of it with the map $\ker f \mono A$, since (using that
$f$ is mono), we have $0 = \ker f$ from $f0 = f\ker f$.

```agda
      kercoker→f : m.Hom (cut (Ker.kernel (Coker.coeq f))) (cut f)
      kercoker→f ./-Hom.map =
        Coker.universal (Ker.kernel f) {e' = id} (monic _ _ path) ∘
          coker-ker≃ker-coker f .is-invertible.inv
        where abstract
          path : f ∘ id ∘ 0m ≡ f ∘ id ∘ Ker.kernel f
          path =
            f ∘ id ∘ 0m              ≡⟨ ap (f ∘_) (eliml refl) ∙ ∘-zero-r ⟩
            0m                       ≡˘⟨ ∅.zero-∘r _ ∙ 0m-unique ⟩
            (∅.zero→ ∘ Ker.kernel f) ≡˘⟨ Ker.equal f ⟩
            f ∘ Ker.kernel f         ≡⟨ ap (f ∘_) (introl refl) ⟩
            f ∘ id ∘ Ker.kernel f    ∎
```

This is indeed a map in the slice using that both isomorphisms and
coequalisers are epic to make progress.

```agda
      kercoker→f ./-Hom.com = path where
        lemma =
          is-coequaliser→is-epic (Coker.coeq _) (Coker.has-is-coeq _) _ _ $
               pullr (Coker.factors _)
            ∙∙ elimr refl
            ∙∙ (decompose f .snd ∙ assoc _ _ _)

        path =
          invertible→epic (coker-ker≃ker-coker _) _ _ $
            (f ∘ Coker.universal _ _ ∘ _) ∘ decompose f .fst   ≡⟨ ap₂ _∘_ (assoc _ _ _) refl ⟩
            ((f ∘ Coker.universal _ _) ∘ _) ∘ decompose f .fst ≡⟨ cancelr (coker-ker≃ker-coker _ .is-invertible.invr) ⟩
            f ∘ Coker.universal _ _                            ≡⟨ lemma ⟩
            Ker.kernel _ ∘ decompose f .fst                     ∎
```

Using the universal property of the cokernel (both uniqueness and
universality), we establish that the maps defined above are inverses in
$\cA$, thus assemble into an isomorphism in the slice.

```agda
    mono→kernel : cut f m.≅ cut (Ker.kernel (Coker.coeq f))
    mono→kernel = m.make-iso f→kercoker kercoker→f f→kc→f kc→f→kc where
      f→kc→f : f→kercoker m.∘ kercoker→f ≡ m.id
      f→kc→f = ext $
        (decompose f .fst ∘ Coker.coeq _) ∘ Coker.universal _ _ ∘ _  ≡⟨ cancel-inner lemma ⟩
        decompose f .fst ∘ _                                         ≡⟨ coker-ker≃ker-coker f .is-invertible.invl ⟩
        id                                                           ∎
        where
          lemma = Coker.unique₂ _
            {e' = Coker.coeq (Ker.kernel f)}
            (∘-zero-r ∙ sym (sym (Coker.coequal _) ∙ ∘-zero-r))
            (pullr (Coker.factors (Ker.kernel f)) ∙ elimr refl)
            (eliml refl)

      kc→f→kc : kercoker→f m.∘ f→kercoker ≡ m.id
      kc→f→kc = ext $
        (Coker.universal _ _ ∘ _) ∘ decompose f .fst ∘ Coker.coeq _ ≡⟨ cancel-inner (coker-ker≃ker-coker f .is-invertible.invr) ⟩
        Coker.universal _ _ ∘ Coker.coeq _                          ≡⟨ Coker.factors _ ⟩
        id                                                          ∎
```
