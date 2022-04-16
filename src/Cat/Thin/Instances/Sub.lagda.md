```agda
open import Cat.Diagram.Pullback.Properties
open import Cat.Functor.FullSubcategory
open import Cat.Diagram.Limit.Base
open import Cat.Diagram.Pullback
open import Cat.Diagram.Terminal
open import Cat.Diagram.Product
open import Cat.Instances.Slice
open import Cat.Prelude
open import Cat.Base
open import Cat.Thin

import Cat.Reasoning
import Cat.Univalent

module Cat.Thin.Instances.Sub {o ℓ} (C : Precategory o ℓ) where
```

# Preorders of Subobjects

Let $\ca{C}$ be a category (like the category $\sets$), and $c \in
\ca{C}$ be an object. We know that the [monomorphisms] $f : a \mono c$
into $c$ correspond to [embeddings] (though often we're interested in
the [regular subobjects] instead) of $a$ into $c$. In $\sets$, we have a
type --- not an object of the category due to size reasons --- which
[classifies these embeddings], so we can either look at $f : a \mono c$
or as the family $f^*(-) : c \to \prop$ it generates. In other
categories, such as [Groups], we're not so lucky: there's no such thing
as a "subgroup classifier".

[regular subobjects]: Cat.Diagram.Equaliser.RegularMono.html
[monomorphisms]: Cat.Morphism.html#monos
[embeddings]: 1Lab.Equiv.Embedding.html
[classifies these embeddings]: 1Lab.Equiv.Embedding.html#subtype-classifier
[Groups]: Algebra.Group.Cat.Base.html

<!--
```agda
private
  module C = Cat.Reasoning C
  open Precategory
  open /-Obj
  open /-Hom
```
-->

Fortunately, in any category, we can still think about "the subobjects
of $c$" as an organised collection: Specifically, we take the [full
subcategory] of the [slice] $\ca{C}/c$ spanned by the objects $(a,f)$
where $f$ is monic.

[full subcategory]: Cat.Functor.FullSubcategory.html
[slice]: Cat.Instances.Slice.html

```agda
Subobj : C.Ob → Precategory (o ⊔ ℓ) ℓ
Subobj O = Restrict {C = Slice C O} (C.is-monic ⊙ map)
```

Since the maps we're talking about are monomorphisms, the precategory
`Subobj`{.Agda} automatically has a [proposition]'s worth of maps
between any two objects; By the closure properties of [univalent
categories], the precategory of subobjects (of $c$) in a univalent
category $\ca{C}$ is univalent: The **poset of subobjects** of $\ca{C}$.

[proposition]: 1Lab.HLevel.html#is-prop
[univalent categories]: Cat.Univalent.html

```agda
Subobj-is-thin : ∀ {O} {A B : Ob (Subobj O)} → is-prop (Hom (Subobj O) A B)
Subobj-is-thin {B = amono} x y = p where
  p = /-Hom-path (amono .witness _ _ (x .commutes ∙ sym (y .commutes)))

Subobj-is-category : ∀ {O} → is-category C → is-category (Subobj O)
Subobj-is-category ccat =
  Restrict-is-category _ (C.is-monic-is-prop ⊙ map) (slice-is-category ccat)

Subobjects : is-category C → C.Ob → Poset (o ⊔ ℓ) ℓ
Subobjects ccat ob = univalent-thin-precat→Poset
  (Subobj ob)
  (λ A B → Subobj-is-thin {A = A} {B = B})
  (Subobj-is-category ccat)
```

## Constructions on subobjects

<!--
```agda
module _ {o : C.Ob} where
  private module Subs = Cat.Reasoning (Subobj o)
  open Terminal
  open Pullback
  open Product
```
-->

We begin by proving that the poset of subobjects has a "maximal
subobject", i.e., a [terminal object]. Since slice categories already
have a terminal object, it remains to show that the identity map is
monic, but this is immediate.

[terminal object]: Cat.Diagram.Terminal.html

```agda
  ⊤-subobj : Terminal (Subobj o)
  ⊤-subobj .top = cut C.id , λ g h p → C.introl refl ·· p ·· C.eliml refl
  ⊤-subobj .has⊤ x = Slice-terminal-object (x .object)
```

If the ambient category $\ca{C}$ has (binary) [pullbacks], then the
slices of $C$ has (binary) [products]. Since `pullbacks preserve
monomorphisms`{.Agda ident=is-monic→pullback-is-monic}, these correspond
to (binary) subobject intersections.

[pullbacks]: Cat.Diagram.Pullback.html
[products]: Cat.Diagram.Pullback.html

```agda
  subobj-products
    : ∀ {A B} → Pullback C (A .object .map) (B .object .map)
    → Product (Subobj o) A B
  subobj-products {A = Am} {B = Bm} pb = prod′ where
    prod : Product (Slice C o) (Am .object) (Bm .object)
    prod = Pullback→Fibre-product pb

    module prod = Product prod
    open Product
    open is-product
    prod′ : Product (Subobj o) Am Bm
    prod′ .apex = prod.apex , mono where abstract
      mono : C.is-monic (Am .object .map C.∘ pb .p₁)
      mono g h p =
        is-monic→pullback-is-monic (Bm .witness) (rotate-pullback (pb .has-is-pb))
          _ _ (Am .witness _ _ (C.assoc _ _ _ ∙ p ∙ sym (C.assoc _ _ _)))
    prod′ .π₁ = prod.π₁
    prod′ .π₂ = prod.π₂
    prod′ .has-is-product .⟨_,_⟩     = prod.⟨_,_⟩
    prod′ .has-is-product .π₁∘factor = prod.π₁∘factor
    prod′ .has-is-product .π₂∘factor = prod.π₂∘factor
    prod′ .has-is-product .unique    = prod.unique
```

<!--
```agda
module
  _ {o′ ℓ′} {J : Precategory o′ ℓ′} {o : Precategory.Ob C} (F : Functor J (Subobj o))
    where

  open Terminal
  open Cone-hom
  open Cone
  open /-Obj
  open /-Hom
```
-->

In general, monics are preserved by arbitrary limits; If you have a
diagram $F : J \to \Sub(o)$, and the category $\ca{C}/o$ has a limit for
$F$, then $F$ also has a limit in $\Sub(o)$.

```agda
  private
    module C/o = Cat.Reasoning (Subobj o)
    module F = Functor F

    F′ : Functor J (Slice C o)
    F′ = Forget-full-subcat F∘ F

  slice-lim→subobj-lim : Limit F′ → Limit F
  slice-lim→subobj-lim lim′ = lim where
    module lim′ = Terminal lim′
    module limob = Cone lim′.top

    mono : C.is-monic (map (lim′.top .apex))
    mono {c = c} g h p i = is-contr→is-prop (lim′.has⊤ cone) g′ h′ i .hom .map where
      cone : Cone F′
      cone .apex .domain = c
      cone .apex .map = limob.apex .map C.∘ h
      cone .ψ x .map = limob.ψ x .map C.∘ h
      cone .ψ x .commutes = C.pulll (limob.ψ x .commutes)
      cone .commutes f = /-Hom-path (C.pulll (ap map (limob.commutes f)))

      g′ : Cone-hom F′ _ _
      g′ .hom .map = g
      g′ .hom .commutes = p
      g′ .commutes o = /-Hom-path (
        F.₀ o .witness _ _ (
          F.₀ o .object .map C.∘ limob.ψ o .map C.∘ g ≡⟨ C.pulll (limob.ψ o .commutes) ⟩
          limob.apex .map C.∘ g                       ≡⟨ p ⟩
          limob.apex .map C.∘ h                       ≡˘⟨ C.pulll (limob.ψ o .commutes) ⟩
          F.₀ o .object .map C.∘ limob.ψ o .map C.∘ h ∎
          ))
      h′ : Cone-hom F′ _ _
      h′ .hom .map = h
      h′ .hom .commutes = refl
      h′ .commutes _ = /-Hom-path refl

    cone : Cone F
    cone .apex = limob.apex , mono
    cone .ψ = limob.ψ
    cone .commutes = limob.commutes

    lim : Limit F
    lim .top = cone
    lim .has⊤ other = contr ch unique where
      other′ : Cone F′
      other′ .apex = other .apex .object
      other′ .ψ = other .ψ
      other′ .commutes = other .commutes

      ch : Cone-hom F other cone
      ch .hom = lim′.has⊤ other′ .centre .hom
      ch .commutes = lim′.has⊤ other′ .centre .commutes

      unique : ∀ x → _
      unique x = Cone-hom-path _
        (ap hom (lim′.has⊤ other′ .paths (record
          { hom = x .hom ; commutes = x .commutes })))
```

In particular, since limits in $\ca{C}/o$ are computed as limits in
$\ca{C}$, if $\ca{C}$ is complete, then so are its subobject
precategories.

```agda
is-complete→subobj-is-complete
  : ∀ {o′ ℓ′} {c : Precategory.Ob C}
  → is-complete o′ ℓ′ C
  → is-complete o′ ℓ′ (Subobj c)
is-complete→subobj-is-complete lims F =
  slice-lim→subobj-lim F (is-complete→slice-is-complete lims _)
```
