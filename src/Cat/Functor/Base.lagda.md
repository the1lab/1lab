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
isFull : Functor C D → Type _
isFull {C = C} {D = D} F = 
  ∀ {x y} (g : D .Hom (F₀ F x) (F₀ F y)) → ∃[ f ∈ C .Hom x y ] (F₁ F f ≡ g)
```

A functor is **faithful** when its action on hom-sets is injective:

```agda
isFaithful : Functor C D → Type _
isFaithful F = ∀ {x y} → injective (F₁ F {x = x} {y})
```

## ff Functors

A functor is **fully faithful** (abbreviated **ff**) when its action on
hom-sets is an equivalence. Since Hom-sets are sets, it suffices for the
functor to be full and faithful; Rather than taking this conjunction as
a definition, we use the more directly useful data as a definition and
prove the conjunction as a theorem.

```agda
isFf : Functor C D → Type _
isFf F = ∀ {x y} → isEquiv (F₁ F {x = x} {y})

full+faithful→ff : (F : Functor C D) → isFull F → isFaithful F → isFf F
full+faithful→ff {C = C} {D = D} F surj inj .isEqv = p where
  isProp-img : ∀ {x y} f → isProp (fibre (F₁ F {x = x} {y}) f)
  isProp-img f (g , p) (h , q) = Σ≡Prop (λ _ → D .Hom-set _ _ _ _) (inj (p ∙ sym q))

  p : ∀ {x y} f → isContr (fibre (F₁ F {x = x} {y}) f)
  p f .centre = ∥-∥-elim (λ _ → isProp-img f) (λ x → x) (surj f)
  p f .paths = isProp-img f _
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

  isFf→isConservative 
    : {F : Functor C D} → isFf F 
    → ∀ {X Y} (f : C.Hom X Y)  → Dm.isInvertible (F₁ F f)
    → Cm.isInvertible f
  isFf→isConservative {F = F} ff f isinv = i where
    open Cm.isInvertible
    open Cm.Inverses
```

Since the functor is ff, we can find a map "$F_1^{-1}(f) : y \to x$" in
the domain category to serve as an inverse for $f$:

```agda
    g : C.Hom _ _
    g = equiv→inverse ff (isinv .Dm.isInvertible.inv)

    Ffog = 
      F₁ F (f C.∘ g)    ≡⟨ F-∘ F _ _ ⟩ 
      F₁ F f D.∘ F₁ F g ≡⟨ ap₂ D._∘_ refl (equiv→section ff _) ∙ isinv .Dm.isInvertible.invˡ ⟩ 
      D.id              ∎

    Fgof = 
      F₁ F (g C.∘ f)    ≡⟨ F-∘ F _ _ ⟩ 
      F₁ F g D.∘ F₁ F f ≡⟨ ap₂ D._∘_ (equiv→section ff _) refl ∙ isinv .Dm.isInvertible.invʳ ⟩ 
      D.id              ∎

    i : Cm.isInvertible _
    i .inv = g
    i .inverses .invˡ = 
      f C.∘ g                           ≡⟨ sym (equiv→retraction ff _) ⟩
      equiv→inverse ff (F₁ F (f C.∘ g)) ≡⟨ ap (equiv→inverse ff) (Ffog ∙ sym (F-id F)) ⟩
      equiv→inverse ff (F₁ F C.id)      ≡⟨ equiv→retraction ff _ ⟩
      C.id                              ∎
    i .inverses .invʳ =
      g C.∘ f                           ≡⟨ sym (equiv→retraction ff _) ⟩
      equiv→inverse ff (F₁ F (g C.∘ f)) ≡⟨ ap (equiv→inverse ff) (Fgof ∙ sym (F-id F)) ⟩
      equiv→inverse ff (F₁ F C.id)      ≡⟨ equiv→retraction ff _ ⟩
      C.id                              ∎

  isFf→essInjective  
    : {F : Functor C D} → isFf F 
    → ∀ {X Y} → F₀ F X Dm.≅ F₀ F Y
    → X Cm.≅ Y
  isFf→essInjective {F = F} ff 
    record { to = to ; from = from ; inverses = inverses } = 
    Cm.makeIso (equiv→inverse ff to) inv invˡ invʳ
    where 
      D-inv : Dm.isInvertible to
      D-inv = record { inv = from ; inverses = inverses }
      open Cm.isInvertible 
        (isFf→isConservative {F = F} ff 
          (equiv→inverse ff to) 
          (subst Dm.isInvertible (sym (equiv→section ff _)) D-inv))
```

## Essential Fibres

The **essential fibre** of a functor $F : C \to D$ over an object $y :
D$ is the space of objects of $C$ which $F$ takes, up to isomorphism, to
$y$.

```agda
EssentialFibre : Functor C D → D .Ob → Type _
EssentialFibre {D = D} F y = Σ[ x ∈ _ ] (F₀ F x ≅ y)
  where open import Cat.Morphism D
```

A functor is **split essentially surjective** (abbreviated **split
eso**) if there is a procedure for finding points in the essential fibre
over any object. It's **essentially surjective** if the this procedure
_merely_, i.e. truncatedly, finds a point:

```agda
isSplitEso : Functor C D → Type _
isSplitEso F = ∀ y → EssentialFibre F y

isEso : Functor C D → Type _
isEso F = ∀ y → ∥ EssentialFibre F y ∥
```
