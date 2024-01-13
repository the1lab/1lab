<!--
```agda
open import Cat.Functor.Base
open import Cat.Prelude

import Cat.Reasoning
```
-->

```agda
module Cat.Functor.Properties where
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

:::{.definition #full-functor}
A functor is **full** when its action on hom-sets is surjective:

```agda
is-full : Functor C D → Type _
is-full {C = C} {D = D} F =
  ∀ {x y} (g : D .Hom (F₀ F x) (F₀ F y)) → ∃[ f ∈ C .Hom x y ] (F₁ F f ≡ g)
```
:::

:::{.definition #faithful-functor}
A functor is **faithful** when its action on hom-sets is injective:

```agda
is-faithful : Functor C D → Type _
is-faithful F = ∀ {x y} → injective (F₁ F {x = x} {y})
```
:::

<!--
```agda
module _ {C : Precategory o h} {D : Precategory o₁ h₁} where
  private module _ where
    module C = Cat.Reasoning C
    module D = Cat.Reasoning D
    open Cat.Reasoning using (_≅_ ; Inverses)
    open _≅_ public
    open Inverses public

  faithful→iso-fibre-prop
    : ∀ (F : Functor C D)
    → is-faithful F
    → ∀ {x y} → (f : F₀ F x D.≅ F₀ F y)
    → is-prop (Σ[ g ∈ x C.≅ y ] (F-map-iso F g ≡ f))
  faithful→iso-fibre-prop F faithful f (g , p) (g' , q) =
    Σ-prop-path (λ _ → D.≅-is-set _ _) $
    ext (faithful (ap D.to (p ∙ sym q)))
```
-->

## Fully faithful functors {defines="fully-faithful-functor fully-faithful ff"}

A functor is **fully faithful** (abbreviated **ff**) when its action on
hom-sets is an equivalence. Since Hom-sets are sets, it suffices for the
functor to be full and faithful; Rather than taking this conjunction as
a definition, we use the more directly useful data as a definition and
prove the conjunction as a theorem.

```agda
is-fully-faithful : Functor C D → Type _
is-fully-faithful F = ∀ {x y} → is-equiv (F₁ F {x = x} {y})

fully-faithful→faithful : {F : Functor C D} → is-fully-faithful F → is-faithful F
fully-faithful→faithful f = Equiv.injective (_ , f)

fully-faithful→full : {F : Functor C D} → is-fully-faithful F → is-full F
fully-faithful→full {F = F} ff g = inc (equiv→inverse ff g , equiv→counit ff g)

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
    → ∀ {X Y} (f : C.Hom X Y) → Dm.is-invertible (F₁ F f)
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
    module ff {a} {b} = Equiv (_ , ff {a} {b})

    Ffog =
      F₁ F (f C.∘ g)    ≡⟨ F-∘ F _ _ ⟩
      F₁ F f D.∘ F₁ F g ≡⟨ ap₂ D._∘_ refl (ff.ε _) ∙ isinv .Dm.is-invertible.invl ⟩
      D.id              ∎

    Fgof =
      F₁ F (g C.∘ f)    ≡⟨ F-∘ F _ _ ⟩
      F₁ F g D.∘ F₁ F f ≡⟨ ap₂ D._∘_ (ff.ε _) refl ∙ isinv .Dm.is-invertible.invr ⟩
      D.id              ∎

    i : Cm.is-invertible _
    i .inv = g
    i .inverses .invl =
      f C.∘ g                    ≡⟨ sym (ff.η _) ⟩
      ff.from ⌜ F₁ F (f C.∘ g) ⌝ ≡⟨ ap! (Ffog ∙ sym (F-id F)) ⟩
      ff.from (F₁ F C.id)        ≡⟨ ff.η _ ⟩
      C.id                       ∎
    i .inverses .invr =
      g C.∘ f                    ≡⟨ sym (ff.η _) ⟩
      ff.from ⌜ F₁ F (g C.∘ f) ⌝ ≡⟨ ap! (Fgof ∙ sym (F-id F)) ⟩
      ff.from (F₁ F C.id)        ≡⟨ ff.η _ ⟩
      C.id                       ∎

  is-ff→essentially-injective
    : {F : Functor C D} → is-fully-faithful F
    → ∀ {X Y} → F₀ F X Dm.≅ F₀ F Y
    → X Cm.≅ Y
  is-ff→essentially-injective {F = F} ff im = im' where
    -- Cm.make-iso (equiv→inverse ff to) inv invl invr
    open Dm._≅_ im using (to ; from ; inverses)
    D-inv' : Dm.is-invertible (F₁ F (equiv→inverse ff to))
    D-inv' .Dm.is-invertible.inv = from
    D-inv' .Dm.is-invertible.inverses =
      subst (λ e → Dm.Inverses e from) (sym (equiv→counit ff _)) inverses

    open Cm.is-invertible (is-ff→is-conservative {F = F} ff (equiv→inverse ff to) D-inv')

    im' : _ Cm.≅ _
    im' .to   = equiv→inverse ff to
    im' .from = inv
    im' .inverses .Cm.Inverses.invl = invl
    im' .inverses .Cm.Inverses.invr = invr
```

## Essential fibres {defines="essential-fibre"}

The **essential fibre** of a functor $F : C \to D$ over an object $y :
D$ is the space of objects of $C$ which $F$ takes, up to isomorphism, to
$y$.

```agda
Essential-fibre : Functor C D → D .Ob → Type _
Essential-fibre {D = D} F y = Σ[ x ∈ _ ] (F₀ F x ≅ y)
  where open import Cat.Morphism D
```

:::{.definition #split-eso-functor alias="eso-functor essentially-surjective essential-surjection split-essential-surjection split-essentially-surjective"}
A functor is **split essentially surjective** (abbreviated **split
eso**) if there is a procedure for finding points in the essential fibre
over any object. It's **essentially surjective** if this procedure
_merely_, i.e. truncatedly, finds a point:
:::

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
  private module _ where
    open import Cat.Reasoning using (_≅_ ; Inverses)
    open _≅_ public
    open Inverses public

  is-ff→F-map-iso-is-equiv
    : {F : Functor C D} → is-fully-faithful F
    → ∀ {X Y} → is-equiv (F-map-iso {x = X} {Y} F)
  is-ff→F-map-iso-is-equiv {F = F} ff = is-iso→is-equiv isom where
    isom : is-iso _
    isom .is-iso.inv    = is-ff→essentially-injective {F = F} ff
    isom .is-iso.rinv x = ext (equiv→counit ff _)
    isom .is-iso.linv x = ext (equiv→unit ff _)
```
-->

## Pseudomonic functors {defines="pseudomonic pseudomonic-functor"}

A functor is **pseudomonic** if it is faithful and full on isomorphisms.
Pseudomonic functors are arguably the correct notion of subcategory, as
they ensure that we are not able to distinguish between isomorphic objects
when creating a subcategory.

<!--
```agda
module _ {C : Precategory o h} {D : Precategory o₁ h₁} where
  import Cat.Reasoning C as C
  import Cat.Reasoning D as D
```
-->

```agda
  is-full-on-isos : Functor C D → Type (o ⊔ h ⊔ h₁)
  is-full-on-isos F =
    ∀ {x y} → (f : (F .F₀ x) D.≅ (F .F₀ y)) → ∃[ g ∈ x C.≅ y ] (F-map-iso F g ≡ f)

  record is-pseudomonic (F : Functor C D) : Type (o ⊔ h ⊔ h₁) where
    no-eta-equality
    field
      faithful : is-faithful F
      isos-full : is-full-on-isos F

  open is-pseudomonic
```

Somewhat surprisingly, pseudomonic functors are [conservative].
As $F$ is full on isos, there merely exists some iso $g$ in the fibre
of $f$. However, invertibility is a property of morphisms, so we can
untruncate the mere existence. Once we have our hands on the isomorphism,
we perform a simple calculation to note that it yields an inverse to $f$.

[conservative]: Cat.Functor.Conservative.html

```agda
  pseudomonic→conservative
    : ∀ {F : Functor C D}
    → is-pseudomonic F
    → ∀ {x y} (f : C.Hom x y) → D.is-invertible (F₁ F f)
    → C.is-invertible f
  pseudomonic→conservative {F = F} pseudo {x} {y} f inv =
    ∥-∥-rec C.is-invertible-is-prop
      (λ (g , p) →
        C.make-invertible (C.from g)
          (sym (ap (C._∘ _) (pseudo .faithful (ap D.to p))) ∙ C.invl g)
          (sym (ap (_ C.∘_) (pseudo .faithful (ap D.to p))) ∙ C.invr g))
      (pseudo .isos-full (D.invertible→iso _ inv))
```

In a similar vein, pseudomonic functors are essentially injective.
The proof follows a similar path to the prior one, hinging on the
fact that faithful functors are an embedding on isos.

```agda
  pseudomonic→essentially-injective
    : ∀ {F : Functor C D}
    → is-pseudomonic F
    → ∀ {x y} → F₀ F x D.≅ F₀ F y
    → x C.≅ y
  pseudomonic→essentially-injective {F = F} pseudo f =
    ∥-∥-rec (faithful→iso-fibre-prop F (pseudo .faithful) f)
      (λ x → x)
      (pseudo .isos-full f) .fst
```

Fully faithful functors are pseudomonic, as they are faithful and
essentially injective.

```agda
  ff→pseudomonic
    : ∀ {F : Functor C D}
    → is-fully-faithful F
    → is-pseudomonic F
  ff→pseudomonic {F} ff .faithful = fully-faithful→faithful {F = F} ff
  ff→pseudomonic {F} ff .isos-full f =
    inc (is-ff→essentially-injective {F = F} ff f ,
         ext (equiv→counit ff (D.to f)))
```

## Equivalence on objects functors

A functor $F : \cC \to \cD$ is an **equivalence on objects** if its action
on objects is an equivalence.

```agda
is-equiv-on-objects : (F : Functor C D) → Type _
is-equiv-on-objects F = is-equiv (F .F₀)
```

If $F$ is an equivalence-on-objects functor, then it is (split)
essentially surjective.

```agda
equiv-on-objects→split-eso
  : ∀ (F : Functor C D) → is-equiv-on-objects F → is-split-eso F
equiv-on-objects→split-eso {D = D} F eqv y =
  equiv→inverse eqv y , path→iso (equiv→counit eqv y)

equiv-on-objects→eso : ∀ (F : Functor C D) → is-equiv-on-objects F → is-eso F
equiv-on-objects→eso F eqv y = inc (equiv-on-objects→split-eso F eqv y)
```
