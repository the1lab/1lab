```agda
open import Cat.Prelude

module Cat.Functor.Base where
```

<!--
```agda
private variable
  o h o₁ h₁ : Level
  C D : Precategory o h
open Precategory
open Functor
```
-->

# Functors

This module defines the most important clases of functors: Full,
faithful, fully faithful (abbreviated ff), _split_ essentially
surjective and ("_merely_") essentially surjective.

A functor is **full** when its action on hom-sets is surjective:

```agda
is-full : Functor C D → Type _
is-full {C = C} {D = D} F =
  ∀ {x y} (g : D .Hom (F₀ F x) (F₀ F y)) → ∃[ f ∈ C .Hom x y ] (F₁ F f ≡ g)
```

A functor is **faithful** when its action on hom-sets is injective:

```agda
is-faithful : Functor C D → Type _
is-faithful F = ∀ {x y} → injective (F₁ F {x = x} {y})
```

## ff Functors

A functor is **fully faithful** (abbreviated **ff**) when its action on
hom-sets is an equivalence. Since Hom-sets are sets, it suffices for the
functor to be full and faithful; Rather than taking this conjunction as
a definition, we use the more directly useful data as a definition and
prove the conjunction as a theorem.

```agda
is-fully-faithful : Functor C D → Type _
is-fully-faithful F = ∀ {x y} → is-equiv (F₁ F {x = x} {y})

fully-faithful→faithful : {F : Functor C D} → is-fully-faithful F → is-faithful F
fully-faithful→faithful {F = F} ff {_} {_} {x} {y} p =
  x                         ≡⟨ sym (equiv→retraction ff x) ⟩
  equiv→inverse ff (F₁ F x) ≡⟨ ap (equiv→inverse ff) p ⟩
  equiv→inverse ff (F₁ F y) ≡⟨ equiv→retraction ff y ⟩
  y                         ∎

full+faithful→ff
  : (F : Functor C D) → is-full F → is-faithful F → is-fully-faithful F
full+faithful→ff {C = C} {D = D} F surj inj .is-eqv = p where
  img-is-prop : ∀ {x y} f → is-prop (fibre (F₁ F {x = x} {y}) f)
  img-is-prop f (g , p) (h , q) = Σ-prop-path (λ _ → D .Hom-set _ _ _ _) (inj (p ∙ sym q))

  p : ∀ {x y} f → is-contr (fibre (F₁ F {x = x} {y}) f)
  p f .centre = ∥-∥-elim (λ _ → img-is-prop f) (λ x → x) (surj f)
  p f .paths = img-is-prop f _
```

A very important property of fully faithful functors (like $F$) is that
they are **conservative**: If the image of $f : x \to y$ under $F$ is an
isomorphism $Fx \cong Fy$, then $f$ was really an isomorphism $f : x
\cong y$.

```agda
module _ {C : Precategory o h} {D : Precategory o₁ h₁} where
  private
    module C = Precategory C
    module D = Precategory D

  import Cat.Morphism C as Cm
  import Cat.Morphism D as Dm

  is-ff→is-conservative
    : {F : Functor C D} → is-fully-faithful F
    → ∀ {X Y} (f : C.Hom X Y)  → Dm.is-invertible (F₁ F f)
    → Cm.is-invertible f
  is-ff→is-conservative {F = F} ff f isinv = i where
    open Cm.is-invertible
    open Cm.Inverses
```

Since the functor is ff, we can find a map "$F_1^{-1}(f) : y \to x$" in
the domain category to serve as an inverse for $f$:

```agda
    g : C.Hom _ _
    g = equiv→inverse ff (isinv .Dm.is-invertible.inv)

    Ffog =
      F₁ F (f C.∘ g)    ≡⟨ F-∘ F _ _ ⟩
      F₁ F f D.∘ F₁ F g ≡⟨ ap₂ D._∘_ refl (equiv→section ff _) ∙ isinv .Dm.is-invertible.invl ⟩
      D.id              ∎

    Fgof =
      F₁ F (g C.∘ f)    ≡⟨ F-∘ F _ _ ⟩
      F₁ F g D.∘ F₁ F f ≡⟨ ap₂ D._∘_ (equiv→section ff _) refl ∙ isinv .Dm.is-invertible.invr ⟩
      D.id              ∎

    i : Cm.is-invertible _
    i .inv = g
    i .inverses .invl =
      f C.∘ g                           ≡⟨ sym (equiv→retraction ff _) ⟩
      equiv→inverse ff (F₁ F (f C.∘ g)) ≡⟨ ap (equiv→inverse ff) (Ffog ∙ sym (F-id F)) ⟩
      equiv→inverse ff (F₁ F C.id)      ≡⟨ equiv→retraction ff _ ⟩
      C.id                              ∎
    i .inverses .invr =
      g C.∘ f                           ≡⟨ sym (equiv→retraction ff _) ⟩
      equiv→inverse ff (F₁ F (g C.∘ f)) ≡⟨ ap (equiv→inverse ff) (Fgof ∙ sym (F-id F)) ⟩
      equiv→inverse ff (F₁ F C.id)      ≡⟨ equiv→retraction ff _ ⟩
      C.id                              ∎

  is-ff→essentially-injective
    : {F : Functor C D} → is-fully-faithful F
    → ∀ {X Y} → F₀ F X Dm.≅ F₀ F Y
    → X Cm.≅ Y
  is-ff→essentially-injective {F = F} ff
    record { to = to ; from = from ; inverses = inverses } =
    Cm.make-iso (equiv→inverse ff to) inv invl invr
    where
      D-inv : Dm.is-invertible to
      D-inv = record { inv = from ; inverses = inverses }
      open Cm.is-invertible
        (is-ff→is-conservative {F = F} ff
          (equiv→inverse ff to)
          (subst Dm.is-invertible (sym (equiv→section ff _)) D-inv))
```

## Essential Fibres

The **essential fibre** of a functor $F : C \to D$ over an object $y :
D$ is the space of objects of $C$ which $F$ takes, up to isomorphism, to
$y$.

```agda
Essential-fibre : Functor C D → D .Ob → Type _
Essential-fibre {D = D} F y = Σ[ x ∈ _ ] (F₀ F x ≅ y)
  where open import Cat.Morphism D
```

A functor is **split essentially surjective** (abbreviated **split
eso**) if there is a procedure for finding points in the essential fibre
over any object. It's **essentially surjective** if the this procedure
_merely_, i.e. truncatedly, finds a point:

```agda
is-split-eso : Functor C D → Type _
is-split-eso F = ∀ y → Essential-fibre F y

is-eso : Functor C D → Type _
is-eso F = ∀ y → ∥ Essential-fibre F y ∥
```

<!--
```agda
module _ {C : Precategory o h} {D : Precategory o₁ h₁} where
  import Cat.Reasoning C as C
  import Cat.Reasoning D as D

  F-map-iso : ∀ {x y} (F : Functor C D) → x C.≅ y → F₀ F x D.≅ F₀ F y
  F-map-iso F x =
    D.make-iso (F₁ F x.to) (F₁ F x.from)
      (sym (F-∘ F _ _) ·· ap (F₁ F) x.invl ·· F-id F)
      (sym (F-∘ F _ _) ·· ap (F₁ F) x.invr ·· F-id F)
    where module x = C._≅_ x

  open import Cat.Univalent

  F-map-path : ∀ {x y} (F : Functor C D) (i : x C.≅ y)
             → (ccat : is-category C)
             → (dcat : is-category D)
             → ap (F₀ F) (iso→path C ccat i) ≡ iso→path D dcat (F-map-iso F i)
  F-map-path F i ccat dcat =
    J-iso C ccat
      (λ B p → ap (F₀ F) (iso→path C ccat p) ≡ iso→path D dcat (F-map-iso F p))
      idc
      i
    where abstract
      idc : ∀ {x} → ap (F₀ F) (iso→path C ccat (C.id-iso {x}) )
          ≡ iso→path D dcat (F-map-iso F C.id-iso)
      idc =
        ap (F₀ F) (iso→path C ccat C.id-iso)   ≡⟨ ap (ap (F₀ F)) (iso→path-id C ccat) ⟩
        ap (F₀ F) refl                         ≡˘⟨ equiv→retraction (path→iso-is-equiv D dcat) _ ⟩
        iso→path D dcat (path→iso D refl)      ≡⟨ ap (iso→path D dcat) (D.≅-pathp refl refl (transport-refl _ ∙ sym (F-id F))) ⟩
        iso→path D dcat (F-map-iso F C.id-iso) ∎

  is-ff→F-map-iso-is-equiv
    : {F : Functor C D} → is-fully-faithful F
    → ∀ {X Y} → is-equiv (F-map-iso {X} {Y} F)
  is-ff→F-map-iso-is-equiv {F = F} ff = is-iso→is-equiv isom where
    isom : is-iso _
    isom .is-iso.inv = is-ff→essentially-injective {F = F} ff
    isom .is-iso.rinv x = D.≅-pathp refl refl (equiv→section ff _)
    isom .is-iso.linv x = C.≅-pathp refl refl (equiv→retraction ff _)
```
-->
