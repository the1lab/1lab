<!--
```agda
open import Cat.Functor.Adjoint renaming (_⊣_ to _⊣ᶜ_)
open import Cat.Bi.Base
open import Cat.Prelude
```
-->

```agda
module Cat.Bi.Diagram.Adjunction where
```

<!--
```agda
module Adjointᵇ {o ℓ ℓ'} (B : Prebicategory o ℓ ℓ') where
  open Prebicategory B
```
-->

# Adjunctions in a bicategory

Let $\bicat{B}$ be a [[bicategory]], $A, B : \bicat{B}$ be objects, and
$f : A \to B$ and $g : B \to A$ be 1-cells. Generalising the situation
where $f$ and $g$ are [[functors]], we say they are **adjoints** if
there exist 2-cells $\eta : \id \to gf$ and $\eps : fg \to \id$ (the
**unit** and **counit** respectively), satisfying the equations

<div class=mathpar>

~~~{.quiver}
\[\begin{tikzcd}
  & fgf \\
  f && f
  \arrow["{\varepsilon \blacktriangleleft f}", from=1-2, to=2-3]
  \arrow["{f \blacktriangleright \eta}", from=2-1, to=1-2]
  \arrow["{\mathrm{id}}"', from=2-1, to=2-3]
\end{tikzcd}\]
~~~

and

~~~{.quiver}
\[\begin{tikzcd}
  g && {g,} \\
  & gfg
  \arrow["{\mathrm{id}}", from=1-1, to=1-3]
  \arrow["{\eta \blacktriangleleft g}"', from=1-1, to=2-2]
  \arrow["{g \blacktriangleright \varepsilon}"', from=2-2, to=1-3]
\end{tikzcd}\]
~~~

</div>

called the **triangle identities** (because of their shape) or **zigzag
identities** (because it sounds cool). Note that we have to insert
appropriate associators and unitors in order to translate the diagrams
above into equations that are well-typed in a (weak) bicategory.

```agda
  record _⊣_ {a b : Ob} (f : a ↦ b) (g : b ↦ a) : Type ℓ' where
    field
      η : id ⇒ (g ⊗ f)
      ε : (f ⊗ g) ⇒ id

      zig : λ← f ∘ (ε ◀ f) ∘ α← (f , g , f) ∘ (f ▶ η) ∘ ρ→ f ≡ Hom.id
      zag : ρ← g ∘ (g ▶ ε) ∘ α→ (g , f , g) ∘ (η ◀ g) ∘ λ→ g ≡ Hom.id

  infixr 15 _⊣_
```

This means the triangle identities, rather
than simply expressing a compatibility relation between $\eta$ and
$\eps$ as is the case for [[adjoint functors]], instead exhibit a
complicated compatibility relation between $\eta$, $\eps$, and the
structural isomorphisms (the unitors and associator) of the ambient
bicategory.

<!--
```agda
  module _ {a b} {l : a ↦ b} {r : b ↦ a} {adj adj' : l ⊣ r} where
    private
      module adj  = _⊣_ adj
      module adj' = _⊣_ adj'

    adjoint-path : adj.η ≡ adj'.η → adj.ε ≡ adj'.ε → adj ≡ adj'
    adjoint-path p q i ._⊣_.η   = p i
    adjoint-path p q i ._⊣_.ε   = q i
    adjoint-path p q i ._⊣_.zig = is-prop→pathp
      (λ i → Hom.Hom-set l l (λ← _ ∘ q i ◀ l ∘ α← _ ∘ l ▶ p i ∘ ρ→ _) Hom.id)
      adj.zig adj'.zig i
    adjoint-path p q i ._⊣_.zag = is-prop→pathp
      (λ i → Hom.Hom-set r r (ρ← _ ∘ r ▶ q i ∘ α→ _ ∘ p i ◀ r ∘ λ→ _) Hom.id)
      adj.zag adj'.zag i
```
-->

## Adjunctions in $\Cat$

In the bicategory of categories, where 1-cells are functors, we should
expect that this notion of adjunction agrees with the definition of
adjoint functors.  This is indeed the case, which we can prove by
establishing an equivalence between the two.  This is not very
mathematically interesting: we just need to note that the triangle
identities above, when specialized to natural isomorphisms and applied
pointwise, coincide with those for an adjunction between functors.

<!--
```agda
module _ {o h}
  {C : Precategory o h} {D : Precategory o h} {F : Functor C D} {G : Functor D C}
  where

  open Adjointᵇ (Cat o h)
  open Functor
```
-->

```agda
  adjointᶜ→adjoint : F ⊣ᶜ G → F ⊣ G
  adjointᶜ→adjoint F⊣G ._⊣_.η   = _⊣ᶜ_.unit F⊣G
  adjointᶜ→adjoint F⊣G ._⊣_.ε   = _⊣ᶜ_.counit F⊣G
  adjointᶜ→adjoint F⊣G ._⊣_.zig = ext λ _ →
    idl _ ∙∙ ap₂ _∘_ refl (idl _ ∙ idr _) ∙∙ _⊣ᶜ_.zig F⊣G
    where open Precategory D
  adjointᶜ→adjoint F⊣G ._⊣_.zag = ext λ _ →
    idl _ ∙∙ ap₂ _∘_ refl (idl _ ∙ idr _) ∙∙ _⊣ᶜ_.zag F⊣G
    where open Precategory C

  adjoint→adjointᶜ : F ⊣ G → F ⊣ᶜ G
  adjoint→adjointᶜ F⊣G ._⊣ᶜ_.unit   = _⊣_.η F⊣G
  adjoint→adjointᶜ F⊣G ._⊣ᶜ_.counit = _⊣_.ε F⊣G
  adjoint→adjointᶜ F⊣G ._⊣ᶜ_.zig    =
    sym (idl _ ∙ ap₂ _∘_ refl (idl _ ∙ idr _)) ∙ _⊣_.zig F⊣G ηₚ _
    where open Precategory D
  adjoint→adjointᶜ F⊣G ._⊣ᶜ_.zag =
    sym (idl _ ∙ ap₂ _∘_ refl (idl _ ∙ idr _)) ∙ _⊣_.zag F⊣G ηₚ _
    where open Precategory C

  adjoint≃adjointᶜ : (F ⊣ G) ≃ (F ⊣ᶜ G)
  adjoint≃adjointᶜ .fst = adjoint→adjointᶜ
  adjoint≃adjointᶜ .snd = is-iso→is-equiv $ iso
    adjointᶜ→adjoint
    (λ x → adjoint-pathp refl refl refl refl)
    (λ x → adjoint-path refl refl)
```
