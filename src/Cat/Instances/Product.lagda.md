```agda
open import Cat.Prelude

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

Given two categories $\ca{C}$ and $\ca{D}$, we construct their product
$\ca{C} \times_\cat \ca{D}$. The objects of the product are
pairs $(x,y)$ where $x \in \ca{C}$ and $y \in \ca{D}$; The product
admits projection functors $\ca{C} \times_\id{Cat} \ca{D} \to
\ca{C}$ (onto both factors, not just the first), and given a diagram of
categories as below, there is a unique (in the bicategorical sense)
functor $\mathcal{A} \to \ca{C} \times_\cat \ca{D}$ making the
diagram commute.

~~~{.quiver}
\[\begin{tikzcd}
  & {\mathcal{A}} \\
  {\mathcal{C}} & {\mathcal{C} \times_\id{Cat} \mathcal{D}} & {\mathcal{D}}
  \arrow["{\exists!}", dashed, from=1-2, to=2-2]
  \arrow[from=1-2, to=2-1]
  \arrow[from=1-2, to=2-3]
  \arrow[from=2-2, to=2-3]
  \arrow[from=2-2, to=2-1]
\end{tikzcd}\]
~~~

This would suggest that $\ca{C} \times_\cat \ca{D}$ is the
[categorical product] of $\ca{C}$ and $\ca{D}$ in a metaphorical
"category of categories", but homotopical considerations prevent such a
category from existing: The space of `functors`{.Agda ident=Functor}
$[\ca{C},\ca{D}]$ is a _groupoid_ (since the component with highest
h-level is the object mapping $\ca{C}_0 \to \ca{D}_0$), but the
hom-spaces in a precategory `must be sets`{.Agda ident=Hom-set}

[categorical product]: Cat.Diagram.Product.html

```agda
_×Cat_ : Precategory o₁ h₁ → Precategory o₂ h₂ → Precategory _ _
C ×Cat D = prodcat where
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

infixr 20 _×Cat_
```

We define the two projection functors $\ca{C} \times_\cat \ca{D} \to
\ca{C}$ (resp $\to \ca{D}$) as the evident liftings of the `fst`{.Agda}
and `snd`{.Agda} operations on the product type.

```agda
Fst : Functor (C ×Cat D) C
Fst .F₀ = fst
Fst .F₁ = fst
Fst .F-id = refl
Fst .F-∘ _ _ = refl

Snd : Functor (C ×Cat D) D
Snd .F₀ = snd
Snd .F₁ = snd
Snd .F-id = refl
Snd .F-∘ _ _ = refl

Cat⟨_,_⟩ : Functor E C → Functor E D → Functor E (C ×Cat D)
Cat⟨ F , G ⟩ = f where
  f : Functor _ _
  f .F₀ x = F₀ F x , F₀ G x
  f .F₁ f = F₁ F f , F₁ G f
  f .F-id i = F-id F i , F-id G i
  f .F-∘ f g i = F-∘ F f g i , F-∘ G f g i
```
