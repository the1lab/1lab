<!--
```agda
open import Algebra.Group.Ab.Tensor
open import Algebra.Group.Ab
open import Algebra.Prelude
open import Algebra.Monoid
open import Algebra.Group

open import Cat.Diagram.Equaliser.Kernel

import Algebra.Group.Cat.Base as Grp
import Algebra.Group.Ab.Hom as Ab
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

## Ab-enriched categories

An $\Ab$-enriched category is one where each $\hom$ set carries the
structure of an [[Abelian group]], such that the composition map is
_bilinear_, hence extending to an Abelian group homomorphism

$$
\hom(b, c) \otimes \hom(a, b) \to \hom(a, c)\text{,}
$$

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

  _+_ : ∀ {A B} (f g : Hom A B) → Hom A B
  f + g = Abelian-group-on-hom _ _ .Abelian-group-on._*_ f g

  0m : ∀ {A B} → Hom A B
  0m = Abelian-group-on-hom _ _ .Abelian-group-on.1g

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
  ∘map {A} {B} {C} =
    from-bilinear-map (Hom-grp B C) (Hom-grp A B) (Hom-grp A C)
      (record { map     = _∘_
              ; pres-*l = λ x y z → sym (∘-linear-l x y z)
              ; pres-*r = λ x y z → sym (∘-linear-r x y z)
              })

  module Hom {A B} = Abelian-group-on (Abelian-group-on-hom A B) renaming (_⁻¹ to inverse)
  open Hom
    using (zero-diff)
    renaming (_—_ to _-_)
    public
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

  neg-∘-l
    : ∀ {A B C} {g : Hom B C} {h : Hom A B}
    → Hom.inverse (g ∘ h) ≡ Hom.inverse g ∘ h
  neg-∘-l {g = g} {h} = monoid-inverse-unique Hom.has-is-monoid (g ∘ h) _ _
    Hom.inversel
    (∘-linear-l _ _ _ ∙ ap (_∘ h) Hom.inverser ∙ ∘-zero-l)

  neg-∘-r
    : ∀ {A B C} {g : Hom B C} {h : Hom A B}
    → Hom.inverse (g ∘ h) ≡ g ∘ Hom.inverse h
  neg-∘-r {g = g} {h} = monoid-inverse-unique Hom.has-is-monoid (g ∘ h) _ _
    Hom.inversel
    (∘-linear-r _ _ _ ∙ ap (g ∘_) Hom.inverser ∙ ∘-zero-r)

  ∘-minus-l
    : ∀ {A B C} (f g : Hom B C) (h : Hom A B)
    → (f ∘ h) - (g ∘ h) ≡ (f - g) ∘ h
  ∘-minus-l f g h =
    f ∘ h - g ∘ h               ≡⟨ ap (f ∘ h +_) neg-∘-l ⟩
    f ∘ h + (Hom.inverse g ∘ h) ≡⟨ ∘-linear-l _ _ _ ⟩
    (f - g) ∘ h                 ∎

  ∘-minus-r
    : ∀ {A B C} (f : Hom B C) (g h : Hom A B)
    → (f ∘ g) - (f ∘ h) ≡ f ∘ (g - h)
  ∘-minus-r f g h =
    f ∘ g - f ∘ h               ≡⟨ ap (f ∘ g +_) neg-∘-r ⟩
    f ∘ g + (f ∘ Hom.inverse h) ≡⟨ ∘-linear-r _ _ _ ⟩
    f ∘ (g - h)                 ∎
```

</details>

Before moving on, we note the following property of $\Ab$-categories: If
$A$ is an object s.t. $\id[A] = 0$, then $A$ is a zero object.

```agda
module _ {o ℓ} {C : Precategory o ℓ} (A : Ab-category C) where
  private module A = Ab-category A

  id-zero→zero : ∀ {A} → A.id {A} ≡ A.0m → A.is-zero A
  id-zero→zero idm .A.is-zero.has-is-initial B = contr A.0m λ h → sym $
    h                                ≡⟨ A.intror refl ⟩
    h A.∘ A.id                       ≡⟨ A.refl⟩∘⟨ idm ⟩
    h A.∘ A.0m                       ≡⟨ A.∘-zero-r ⟩
    A.0m                             ∎
  id-zero→zero idm .A.is-zero.has-is-terminal x = contr A.0m λ h → sym $
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
  Ab-ab-category .∘-linear-l f g h = trivial!
  Ab-ab-category .∘-linear-r f g h =
    Homomorphism-path (λ _ → sym (f .preserves .is-group-hom.pres-⋆ _ _))
```

# Additive categories

An $\Ab$-category is **additive** when its underlying category has a
[[terminal object]] and finite [[products]]; By the yoga above, this
implies that the terminal object is also a zero object, and the finite
products coincide with finite coproducts.

```agda
record is-additive {o ℓ} (C : Precategory o ℓ) : Type (o ⊔ lsuc ℓ) where
  field has-ab : Ab-category C
  open Ab-category has-ab public

  field
    has-terminal : Terminal
    has-prods    : ∀ A B → Product A B

  ∅ : Zero
  ∅ .Zero.∅ = has-terminal .Terminal.top
  ∅ .Zero.has-is-zero = id-zero→zero has-ab $
    is-contr→is-prop (has-terminal .Terminal.has⊤ _) _ _
  module ∅ = Zero ∅

  0m-unique : ∀ {A B} → ∅.zero→ {A} {B} ≡ 0m
  0m-unique = ap₂ _∘_ (∅.has⊥ _ .paths _) refl ∙ ∘-zero-l
```

Coincidence of finite products and finite coproducts leads to an object
commonly called a (finite) **biproduct**. The coproduct coprojections
are given by the pair of maps

$$
\begin{align*}
&(\id \times 0) : A \to A \times B \\
&(0 \times \id) : B \to A \times B\text{,}
\end{align*}
$$

respectively, and the comultiplication of $f$ and $g$ is given by
$f\pi_1 + g\pi_2$. We can calculate, for the first coprojection followed
by comultiplication,

$$
\begin{align*}
& (f\pi_1+g\pi_2)(\id\times 0) \\
=& f\pi_1(\id\times 0) + g\pi_2(\id\times 0) \\
=& f\id + g0 \\
=& f\text{,}
\end{align*}
$$

and analogously for the second coprojection followed by
comultiplication.

```agda
  has-coprods : ∀ A B → Coproduct A B
  has-coprods A B = coprod where
    open Coproduct
    open is-coproduct
    module Prod = Product (has-prods A B)
    coprod : Coproduct A B
    coprod .coapex = Prod.apex
    coprod .in₀ = Prod.⟨ id , 0m ⟩
    coprod .in₁ = Prod.⟨ 0m , id ⟩
    coprod .has-is-coproduct .[_,_] f g = f ∘ Prod.π₁ + g ∘ Prod.π₂
    coprod .has-is-coproduct .in₀∘factor {inj0 = inj0} {inj1} =
      (inj0 ∘ Prod.π₁ + inj1 ∘ Prod.π₂) ∘ Prod.⟨ id , 0m ⟩ ≡⟨ sym (∘-linear-l _ _ _) ⟩
      ((inj0 ∘ Prod.π₁) ∘ Prod.⟨ id , 0m ⟩ + _)            ≡⟨ Hom.elimr (pullr Prod.π₂∘factor ∙ ∘-zero-r) ⟩
      (inj0 ∘ Prod.π₁) ∘ Prod.⟨ id , 0m ⟩                  ≡⟨ cancelr Prod.π₁∘factor ⟩
      inj0                                                ∎
    coprod .has-is-coproduct .in₁∘factor {inj0 = inj0} {inj1} =
      (inj0 ∘ Prod.π₁ + inj1 ∘ Prod.π₂) ∘ Prod.⟨ 0m , id ⟩ ≡⟨ sym (∘-linear-l _ _ _) ⟩
      (_ + (inj1 ∘ Prod.π₂) ∘ Prod.⟨ 0m , id ⟩)            ≡⟨ Hom.eliml (pullr Prod.π₁∘factor ∙ ∘-zero-r) ⟩
      (inj1 ∘ Prod.π₂) ∘ Prod.⟨ 0m , id ⟩                  ≡⟨ cancelr Prod.π₂∘factor ⟩
      inj1                                                 ∎
```

For uniqueness, we use distributivity of composition over addition of
morphisms and the universal property of the product to establish the
desired equation. Check it out:

```agda
    coprod .has-is-coproduct .unique {inj0 = inj0} {inj1} other p q = sym $
      inj0 ∘ Prod.π₁ + inj1 ∘ Prod.π₂                                             ≡⟨ ap₂ _+_ (pushl (sym p)) (pushl (sym q)) ⟩
      (other ∘ Prod.⟨ id , 0m ⟩ ∘ Prod.π₁) + (other ∘ Prod.⟨ 0m , id ⟩ ∘ Prod.π₂) ≡⟨ ∘-linear-r _ _ _ ⟩
      other ∘ (Prod.⟨ id , 0m ⟩ ∘ Prod.π₁ + Prod.⟨ 0m , id ⟩ ∘ Prod.π₂)           ≡⟨ elimr lemma ⟩
      other                                                                       ∎
      where
        lemma : Prod.⟨ id , 0m ⟩ ∘ Prod.π₁ + Prod.⟨ 0m , id ⟩ ∘ Prod.π₂
              ≡ id
        lemma = Prod.unique₂ {pr1 = Prod.π₁} {pr2 = Prod.π₂}
          (sym (∘-linear-r _ _ _) ∙ ap₂ _+_ (cancell Prod.π₁∘factor) (pulll Prod.π₁∘factor ∙ ∘-zero-l) ∙ Hom.elimr refl)
          (sym (∘-linear-r _ _ _) ∙ ap₂ _+_ (pulll Prod.π₂∘factor ∙ ∘-zero-l) (cancell Prod.π₂∘factor) ∙ Hom.eliml refl)
          (elimr refl)
          (elimr refl)
```

# Pre-abelian & abelian categories

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
    cokernel : ∀ {A B} (f : Hom A B) → Coequaliser 0m f

  module Ker {A B} (f : Hom A B) = Kernel (kernel f)
  module Coker {A B} (f : Hom A B) = Coequaliser (cokernel f)
```

Every morphism $A \xto{f} B$ in a preabelian category admits a canonical
decomposition as

$$
A \xepi{p} \coker (\ker f) \xto{f'} \ker (\coker f) \xmono{i} B\text{,}
$$

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
            ·· ∅.zero-∘r _
            ·· ap₂ _∘_ (∅.has⊥ _ .paths 0m) refl
            ·· ∘-zero-l ·· sym ∘-zero-r
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
A \xepi{p} \coker (\ker f) \cong \ker (\coker f)\text{,}
$$

where the isomorphism is our canonical map from before.

```agda
      f→kercoker : m.Hom (cut f) (cut (Ker.kernel (Coker.coeq f)))
      f→kercoker ./-Hom.map = decompose f .fst ∘ Coker.coeq (Ker.kernel f)
      f→kercoker ./-Hom.commutes = sym (decompose f .snd)
```

Conversely, map $\ker (\coker f) \to A$ is the composite

$$
\ker (\coker f) \cong \coker (\ker f) \to A\text{,}
$$

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
      kercoker→f ./-Hom.commutes = path where
        lemma =
          is-coequaliser→is-epic (Coker.coeq _) (Coker.has-is-coeq _) _ _ $
               pullr (Coker.factors _)
            ·· elimr refl
            ·· (decompose f .snd ∙ assoc _ _ _)

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
