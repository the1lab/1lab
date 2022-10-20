```agda
open import Cat.Diagram.Colimit.Base
open import Cat.Functor.Kan.Nerve
open import Cat.Instances.Comma
open import Cat.Functor.Base
open import Cat.Prelude

import Cat.Functor.Reasoning as Fr
import Cat.Reasoning as Cr

module Cat.Functor.Dense where
```

# Dense subcategories

A $\kappa$-small subcategory $\ca{C} \sube \ca{D}$ of a locally
$\kappa$-small category $\ca{D}$ (hence a \r{fully faithful} functor $F
: \ca{C} \mono \ca{D}$) is called **dense** if objects of $\ca{D}$ are
generated under \r{colimits} by those of $\ca{C}$, in a certain
canonical way. In particular, any functor $F$ and object $d : \ca{D}$
can be put into a diagram

$$
J : (F \searrow d) \xto{\mathrm{pr}} C \xto{\iota} D\text{,}
$$

where $(\iota \searrow d) \to C$ is the projection functor from the
corresponding [comma category], in such a way that the object $d$ is the
nadir of a cocone over $J$.

[comma category]: Cat.Instances.Comma.html

<!--
```agda
module
  _ {o ℓ} {C : Precategory ℓ ℓ} {D : Precategory o ℓ} (F : Functor C D)
  where
  open Cocone-hom
  open Functor
  open Cocone
  open ↓Obj
  open ↓Hom
  open _=>_

  private
    module C = Cr C
    module D = Cr D
    module F = Fr F
```
-->

```agda
  is-dense : Type _
  is-dense = ∀ d → is-colimit {J = F ↘ d} (F F∘ Dom _ _) $ λ where
    .coapex     → d
    .ψ x        → x .map
    .commutes f → f .sq ∙ D.idl _
```

The functor $F$ is called _dense_ if this cocone is colimiting for every
$d : \ca{D}$. The important of density is that, for a dense functor $F$,
the induced [nerve] functor is fully faithful.

[nerve]: Cat.Functor.Kan.Nerve.html

```agda
  is-dense→nerve-is-ff : is-dense → is-ff (Nerve F)
  is-dense→nerve-is-ff is-colim = is-iso→is-equiv $ iso inv invr invl where
    nt→cone : ∀ {x y} → (Nerve F .F₀ x => Nerve F .F₀ y) → Cocone _
    nt→cone {x} {y} nt .coapex = y
    nt→cone {x} {y} nt .ψ o = nt .η _ (o .map)
    nt→cone {x} {y} nt .commutes {γ} {δ} f =
      nt .η _ (δ .map) D.∘ F.₁ (f .α)   ≡˘⟨ nt .is-natural _ _ _ $ₚ _ ⟩
      nt .η _ ⌜ δ .map D.∘ F.₁ (f .α) ⌝ ≡⟨ ap! (f .sq ∙ D.idl _) ⟩
      nt .η _ (γ .map)                  ∎

    inv : ∀ {x y} → (Nerve F .F₀ x => Nerve F .F₀ y) → D.Hom x y
    inv {x} {y} nt = is-colim x (nt→cone nt) .centre .hom

    invr : ∀ {x y} (f : Nerve F .F₀ x => Nerve F .F₀ y) → Nerve F .F₁ (inv f) ≡ f
    invr f = Nat-path λ x → funext λ i →
      is-colim _ (nt→cone f) .centre .commutes record { map = i }

    invl : ∀ {x y} (f : D.Hom x y) → inv (Nerve F .F₁ f) ≡ f
    invl f = ap hom $ is-colim _ (nt→cone _) .paths $ λ where
      .hom        → f
      .commutes o → refl
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
    ff→faithful (Nerve F) (is-dense→nerve-is-ff dense) $
      Nat-path λ x → funext λ g → h g
```
