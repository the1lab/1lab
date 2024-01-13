<!--
```agda
open import Cat.Instances.Functor
open import Cat.Diagram.Initial
open import Cat.Displayed.Total
open import Cat.Functor.Adjoint
open import Cat.Instances.Comma
open import Cat.Displayed.Base
open import Cat.Prelude

import Cat.Reasoning as Cr
```
-->

```agda
module Cat.Displayed.Total.Free
  {o ℓ o' ℓ'} {B : Precategory o ℓ}
  (E : Displayed B o' ℓ') where
```

# Free objects in total categories

When the [[total category]] of a [[displayed category]] $\cE
\liesover \cB$ is being regarded as a _category of structured
$\cB$-objects_, a natural question to consider is whether any object
$x : \cB$ can be equipped with a _free_ $\cE$ structure --- in the
sense of having a [[left adjoint]] to the projection functor $\pi^f :
\int\cE \to \cB$.

The displayed formulation admits a particularly nice phrasing of the
condition for "having free objects". To wit: a **system of free
objects** for a displayed category $\cE$ is a section $F$ of the
displayed object space --- a function assigning objects $F(x) :
\cE^*x$ to objects $x : \cB$ --- having the property that these
are "initial" among displayed maps:


<!--
```agda
private
  module B = Cr B
  module E = Displayed E
open Initial
open Functor
open ↓Obj
open ↓Hom
```
-->

```agda
module
  _ (system : ∀ x → E.Ob[ x ])
    (is-free : ∀ {x y} (f : B.Hom x y) (y' : E.Ob[ y ])
             → is-contr (E.Hom[ f ] (system x) y'))
  where
```

For any base morphism $x \xto{f} y : \cB$ and displayed object $y'
\liesover y$, there must be a contractible space of morphisms $F(x)
\to_{f} y'$ over $f$. The elegance of this definition speaks to the
strength of the displayed framework for considering structured
categories: It is a much shorter, and much more ergonomic, rephrasing of
the condition that all comma categories $x \downarrow \pi^f$ have
initial objects.

```agda
  private
    universal : ∀ x → Universal-morphism x (πᶠ E)
    universal x .bot = record { y = x , system x ; map = B.id }
    universal x .has⊥ m' = contr the-map unique where
      the-map : Precategory.Hom (x ↙ πᶠ E) (universal x .bot) m'
      the-map .α = tt
      the-map .β = total-hom (m' .map) (is-free (m' .map) (y m' .snd) .centre)
      the-map .sq = refl

      unique : ∀ x → the-map ≡ x
      unique h = ↓Hom-path _ _ refl $
        total-hom-path E (B.intror refl ·· h .sq ·· B.elimr refl)
          (is-prop→pathp (λ i → is-contr→is-prop (is-free _ _)) _ _)
```

Since a system of free objects gives a system of universal morphisms, we
have a left adjoint to the projection functor.

```agda
  Free : Functor B (∫ E)
  Free = universal-maps→L (πᶠ E) universal

  Free⊣πᶠ : Free ⊣ πᶠ E
  Free⊣πᶠ = universal-maps→L⊣R (πᶠ E) universal
```

Even though the `Free` functor is produced by general abstract nonsense,
it admits an elementary description, which agrees with the one above
definitionally on objects, and differs on morphisms by an extra identity
map on the left.

```agda
  private
    Free' : Functor B (∫ E)
    Free' .F₀ o = o , system o
    Free' .F₁ h = total-hom h (is-free _ _ .centre)
    Free' .F-id = total-hom-path E refl (is-free _ _ .paths _)
    Free' .F-∘ f g = total-hom-path E refl (is-free _ _ .paths _)

    Free≡Free' : Free ≡ Free'
    Free≡Free' = Functor-path (λ _ → refl) λ f → total-hom-path E (B.idl _) λ i →
      is-free (B.idl f i) (system _) .centre
```
