<!--
```agda
open import Cat.Displayed.Fibre
open import Cat.Displayed.Total
open import Cat.Displayed.Base
open import Cat.Prelude

import Cat.Displayed.Reasoning
import Cat.Displayed.Morphism
import Cat.Reasoning
```
-->

```agda
module Cat.Displayed.Univalence
  {o ℓ o' ℓ'}
  {B : Precategory o ℓ}
  (E : Displayed B o' ℓ')
  where
```

<!--
```agda
private
  module B = Cat.Reasoning B
  module ∫E = Cat.Reasoning (∫ E)
open Cat.Displayed.Morphism E
open Displayed E
open Total-hom
```
-->

# Univalence for displayed categories {defines="univalence-of-displayed-categories displayed-univalent-category"}

We provide equivalent characterisations of univalence for categories
$\cE$ which are displayed over a [[univalent category]] $\cB$.

We say a [[displayed category]] $\cE$ is **univalent** when, for any
$f : x \cong y$ in $\cB$ and object $A$ over $x$, the space of "objects
over $y$ isomorphic to $A$ over $f$" is a proposition.

```agda
is-category-displayed : Type _
is-category-displayed =
  ∀ {x y} (f : x B.≅ y) (A : Ob[ x ]) → is-prop (Σ[ B ∈ Ob[ y ] ] (A ≅[ f ] B))
```

This condition is sufficient for the [[total category]] $\int E$ to be
univalent, if $\cB$ is, too. The proof of this is a bit nasty, so we'll
break it down into parts. Initially, observe that the type of
isomorphisms $(x, A) \cong (y, B)$ in $\int E$ is equivalent to the type

$$
\sum_{p : x \cong y} (A \cong_p B),
$$

consisting of an isomorphism $p$ in the base category and an isomorphism
$f$ over it.

```agda
module _ (base-c : is-category B) (disp-c : is-category-displayed) where
  private
    piece-together
      : ∀ {x y} (p : x B.≅ y) {A : Ob[ x ]} {B : Ob[ y ]} (f : A ≅[ p ] B)
      → (x , A) ∫E.≅ (y , B)
    piece-together p f =
      ∫E.make-iso (total-hom (p .B.to) (f .to')) (total-hom (p .B.from) (f .from'))
        (total-hom-path E (p .B.invl) (f .invl'))
        (total-hom-path E (p .B.invr) (f .invr'))
```

We first tackle the case where $f : A \cong B$ is vertical, i.e. $A$ and
$B$ are in the same [[fibre category]]. But then, observe that our
displayed univalence condition, when applied to the identity morphism,
gives us exactly an identification $p : A \equiv B$ s.t. over $p$, $f$
looks like the identity (vertical) isomorphism.

```agda
    contract-vertical-iso
      : ∀ {x} {A : Ob[ x ]} (B : Ob[ x ]) (f : A ≅↓ B)
      → Path (Σ _ ((x , A) ∫E.≅_)) ((x , A) , ∫E.id-iso)
          ((x , B) , piece-together B.id-iso f)
    contract-vertical-iso {x} {A} B f =
      Σ-pathp (λ i → x , pair i .fst)
        (∫E.≅-pathp refl _ (total-hom-pathp E _ _ refl λ i → pair i .snd .to'))
      where
        pair = disp-c B.id-iso A
          (A , id-iso↓)
          (B , f)
```

:::{.definition #univalence-of-total-categories}
We can now use _isomorphism induction_ in the base category to reduce
the general case to `contract-vertical-iso`{.Agda} above. To wit: If $p
: x \cong y$ is an arbitrary isomorphism (in $\cB$), it suffices to
consider the case where $y = x$ and $p$ is the identity. Here, $p$ is
the isomorphism of first components coming from the isomorphism in $\int E$.
:::

```agda
  is-category-total : is-category (∫ E)
  is-category-total = total-cat where
    wrapper
      : ∀ {x y} (p : x B.≅ y) (A : Ob[ x ]) (B : Ob[ y ]) (f : A ≅[ p ] B)
      → Path (Σ _ ((x , A) ∫E.≅_))
        ((x , A) , ∫E.id-iso)
        ((y , B) , piece-together p f)
    wrapper p A =
      Univalent.J-iso base-c
        (λ y p → (B : Ob[ y ]) (f : A ≅[ p ] B)
               → ((_ , A) , ∫E.id-iso) ≡ (((y , B) , piece-together p f)))
        contract-vertical-iso
        p

    total-cat : is-category (∫ E)
    total-cat .to-path p = ap fst $
        wrapper (total-iso→iso E p) _ _ (total-iso→iso[] E p)
    total-cat .to-path-over p = ap snd $
        wrapper (total-iso→iso E p) _ _ (total-iso→iso[] E p)
```

## Fibrewise univalent categories

Using the same trick as above, we can show that a displayed category is
univalent everywhere if, and only if, it is univalent when restricted to
vertical isomorphisms:

```agda
is-category-fibrewise
  : is-category B
  → (∀ {x} (A : Ob[ x ]) → is-prop (Σ[ B ∈ Ob[ x ] ] (A ≅↓ B)))
  → is-category-displayed
is-category-fibrewise base-c wit f A =
  Univalent.J-iso base-c (λ y p → is-prop (Σ[ B ∈ Ob[ y ] ] (A ≅[ p ] B))) (wit A) f
```

Consequently, it suffices for each fibre _category_ to be univalent,
since a vertical isomorphism is no more than an isomorphism in a
particular fibre category.

```agda
is-category-fibrewise'
  : is-category B
  → (∀ x → is-category (Fibre E x))
  → is-category-displayed
is-category-fibrewise' b wit = is-category-fibrewise b wit' where
  wit' : ∀ {x} (A : Ob[ x ]) → is-prop (Σ[ B ∈ Ob[ x ] ] (A ≅↓ B))
  wit' {x} A =
    is-contr→is-prop $ retract→is-contr
      (λ (x , i) → x , make-iso[ B.id-iso ]
        (i .F.to)
        (i .F.from)
        (to-pathp (i .F.invl))
        (to-pathp (i .F.invr)))
      (λ (x , i) → x , F.make-iso (i .to') (i .from')
        (from-pathp (i .invl')) (from-pathp (i .invr')))
      (λ (x , i) → Σ-pathp refl (≅[]-path refl))
      (is-contr-ΣR (wit x))
    where module F = Cat.Reasoning (Fibre E x)
```
