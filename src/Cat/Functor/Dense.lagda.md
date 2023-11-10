<!--
```agda
open import Cat.Instances.Shape.Terminal
open import Cat.Diagram.Colimit.Base
open import Cat.Functor.Properties
open import Cat.Functor.Kan.Nerve
open import Cat.Instances.Comma
open import Cat.Prelude

import Cat.Functor.Reasoning as Fr
```
-->

```agda
module Cat.Functor.Dense where
```

# Dense subcategories

A $\kappa$-small subcategory $\cC \sube \cD$ of a locally $\kappa$-small
category $\cD$ (hence a [[fully faithful functor]] $F : \cC \mono \cD$)
is called **dense** if objects of $\cD$ are generated under [[colimits]]
by those of $\cC$, in a certain canonical way. In particular, any
functor $F$ and object $d : \cD$ can be put into a diagram

$$
J : (F \searrow d) \xto{\mathrm{pr}} C \xto{F} D\text{,}
$$

where $(F \searrow d) \to C$ is the projection functor from the
corresponding [comma category], in such a way that the object $d$ is the
nadir of a cocone over $J$.

[comma category]: Cat.Instances.Comma.html

<!--
```agda
module
  _ {o ℓ} {C : Precategory ℓ ℓ} {D : Precategory o ℓ} (F : Functor C D)
  where
  open Functor
  open ↓Obj
  open ↓Hom
  open _=>_

  private
    module C = Precategory C
    module D = Precategory D
    module F = Fr F
```
-->

```agda
  dense-cocone : ∀ d → F F∘ Dom F (const! d) => Const d
  dense-cocone d .η x = x .map
  dense-cocone d .is-natural _ _ f = f .sq

  is-dense : Type _
  is-dense = ∀ d → is-colimit {J = F ↘ d} (F F∘ Dom _ _) d (dense-cocone d)
```

The functor $F$ is called _dense_ if this cocone is colimiting for every
$d : \cD$. The importance of density is that, for a dense functor $F$,
the induced [nerve] functor is fully faithful.

[nerve]: Cat.Functor.Kan.Nerve.html

```agda
  is-dense→nerve-is-ff : is-dense → is-fully-faithful (Nerve F)
  is-dense→nerve-is-ff is-dense = is-iso→is-equiv $ iso inv invr invl where
    module is-dense d = is-colimit (is-dense d)

    inv : ∀ {x y} → (Nerve F .F₀ x => Nerve F .F₀ y) → D.Hom x y
    inv nt =
      is-dense.universal _
        (λ j → nt .η _ (j .map))
        λ f → sym (nt .is-natural _ _ _ $ₚ _) ∙ ap (nt .η _) (f .sq ∙ D.idl _)

    invr : ∀ {x y} (f : Nerve F .F₀ x => Nerve F .F₀ y) → Nerve F .F₁ (inv f) ≡ f
    invr f = ext λ x i → is-dense.factors _ {j = ↓obj i} _ _

    invl : ∀ {x y} (f : D.Hom x y) → inv (Nerve F .F₁ f) ≡ f
    invl f = sym $ is-dense.unique _ _ _ f (λ _ → refl)
```

Another way of putting this is that probes by a dense subcategory are
enough to tell morphisms (and so objects) in the ambient category apart.

```agda
  dense→separating
    : is-dense
    → {X Y : D.Ob} {f g : D.Hom X Y}
    → (∀ {Z} (h : D.Hom (F.₀ Z) X) → f D.∘ h ≡ g D.∘ h)
    → f ≡ g
  dense→separating dense h =
    fully-faithful→faithful {F = Nerve F} (is-dense→nerve-is-ff dense) $
      ext λ x g → h g
```
