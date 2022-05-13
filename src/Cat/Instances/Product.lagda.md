```agda
open import Cat.Functor.Base
open import Cat.Univalent
open import Cat.Prelude

import Cat.Reasoning

module Cat.Instances.Product where
```

<!--
```agda
open Precategory
open Functor
private variable
  o₁ h₁ o₂ h₂ : Level
  C D E : Precategory o₁ h₁
```
-->

# Product categories

Let $\ca{C}$ and $\ca{D}$ be two precategories; we put no restrictions
on their relative sizes. Their _product category_ $\ca{C} \times^c
\ca{D}$ is the category having as object _pairs_ $(x, y)$ of an object
$x : \ca{C}$ and $y : \ca{D}$, and the morphisms are pairs $(f, g)$ of a
morphism in $\ca{C}$ and a morphism in $\ca{D}$. The product category
admits two projection functors

$$
\ca{C} \xot{\pi_1} (\ca{C} \times^c \ca{D}) \xto{\pi_2} \ca{D}\text{,}
$$

satisfying a universal property analogous to those of [product diagrams]
_in_ categories. Namely, given a setup like in the diagram below, there
is a unique^[When $\ca{C}$ and $\ca{D}$ are precategories, this functor
is only unique up to a natural isomorphism] functor which fits into the
dashed line and makes the whole diagram commute.

[product diagrams]: Cat.Diagram.Product.html

~~~{.quiver}
\[\begin{tikzcd}
  & {\mathcal{A}} \\
  {\mathcal{C}} & {\mathcal{C} \times^c \mathcal{D}} & {\mathcal{D}}
  \arrow["{\exists!}", dashed, from=1-2, to=2-2]
  \arrow[from=1-2, to=2-1]
  \arrow[from=1-2, to=2-3]
  \arrow[from=2-2, to=2-3]
  \arrow[from=2-2, to=2-1]
\end{tikzcd}\]
~~~

Formulating this universal property properly would take us further
afield into 2-category theory than is appropriate here.

```agda
_×ᶜ_ : Precategory o₁ h₁ → Precategory o₂ h₂ → Precategory _ _
C ×ᶜ D = prodcat where
  module C = Precategory C
  module D = Precategory D

  prodcat : Precategory _ _
  prodcat .Ob = Ob C × Ob D
  prodcat .Hom (a , a') (b , b') = Hom C a b × Hom D a' b'
  prodcat .Hom-set (a , a') (b , b') = ×-is-hlevel 2 (Hom-set C a b) (Hom-set D a' b')
  prodcat .id = id C , id D
  prodcat ._∘_ (f , f') (g , g') = f C.∘ g , f' D.∘ g'
  prodcat .idr (f , f') i = C.idr f i , D.idr f' i
  prodcat .idl (f , f') i = C.idl f i , D.idl f' i
  prodcat .assoc (f , f') (g , g') (h , h') i =
    C.assoc f g h i , D.assoc f' g' h' i

infixr 20 _×ᶜ_
```

We define the two projection functors $\ca{C} \times_\cat \ca{D} \to
\ca{C}$ (resp $\to \ca{D}$) as the evident liftings of the `fst`{.Agda}
and `snd`{.Agda} operations from the product _type_. Functoriality is
automatic because composites (and identities) are defined componentwise
in the product category.

```agda
Fst : Functor (C ×ᶜ D) C
Fst .F₀ = fst
Fst .F₁ = fst
Fst .F-id = refl
Fst .F-∘ _ _ = refl

Snd : Functor (C ×ᶜ D) D
Snd .F₀ = snd
Snd .F₁ = snd
Snd .F-id = refl
Snd .F-∘ _ _ = refl

Cat⟨_,_⟩ : Functor E C → Functor E D → Functor E (C ×ᶜ D)
Cat⟨ F , G ⟩ = f where
  f : Functor _ _
  f .F₀ x = F₀ F x , F₀ G x
  f .F₁ f = F₁ F f , F₁ G f
  f .F-id i = F-id F i , F-id G i
  f .F-∘ f g i = F-∘ F f g i , F-∘ G f g i
```

## Univalence

Isomorphisms in functor categories admit a short description, too: They
are maps which are componentwise isomorphisms. It follows, since paths
in product types are products of paths in the component types, that the
product of univalent categories is itself a univalent category.

<!--
```agda
module
  _ {o ℓ o′ ℓ′} {C : Precategory o ℓ} {D : Precategory o′ ℓ′}
    (c-cat : is-category C) (d-cat : is-category D) where
    private
      module C   = Cat.Reasoning C
      module D   = Cat.Reasoning D
      module C*D = Cat.Reasoning (C ×ᶜ D)
```
-->

```agda
    ×ᶜ-is-category : is-category (C ×ᶜ D)
    ×ᶜ-is-category A .centre = _ , C*D.id-iso
    ×ᶜ-is-category (A₀ , A₁) .paths ((B₀ , B₁) , isom) i = (Ap i , Bp i) , ip i where
      Ap : A₀ ≡ B₀
      Ap = iso→path C c-cat (F-map-iso Fst isom)

      Bp : A₁ ≡ B₁
      Bp = iso→path D d-cat (F-map-iso Snd isom)

      ip : PathP (λ i → (A₀ , A₁) C*D.≅ (Ap i , Bp i)) C*D.id-iso isom
      ip = C*D.≅-pathp _ _ $
        Σ-pathp-dep (Hom-pathp-reflr-iso C c-cat (C.idr _))
                    (Hom-pathp-reflr-iso D d-cat (D.idr _))
```
