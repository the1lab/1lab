```agda
open import Cat.Bi.Instances.Discrete
open import Cat.Displayed.Cartesian
open import Cat.Instances.Discrete
open import Cat.Instances.Functor
open import Cat.Displayed.Fibre
open import Cat.Displayed.Base
open import Cat.Bi.Base
open import Cat.Prelude

import Cat.Displayed.Reasoning
import Cat.Displayed.Solver
import Cat.Reasoning
import Cat.Morphism as Mor

module Cat.Displayed.Cartesian.Indexing
  {o ℓ o′ ℓ′} {B : Precategory o ℓ}
  (E : Displayed B o′ ℓ′)
  (cartesian : Cartesian-fibration E)
  where
```

<!--
```agda
open Cat.Displayed.Reasoning E
open Cat.Displayed.Solver E
open Cat.Reasoning B
open Displayed E
open Functor
open Cartesian-fibration cartesian
open Cartesian-lift
open Cartesian
```
-->

# Reindexing for Cartesian fibrations

A [cartesian fibration] can be thought of as a [displayed category]
$\ca{E}$ whose [fibre categories] $\ca{E}^*(b)$ depend
([pseudo])functorially on the object $b : \ca{B}$ from the base
category. A canonical example is [the canonical self-indexing]: If
$\ca{C}$ is a category with [pullbacks], then each $b \xto{f} a :
\ca{C}$ gives rise to [a functor] $\ca{C}/a \to \ca{C}/b$, the _change
of base_ along $f$.

[cartesian fibration]: Cat.Displayed.Cartesian.html
[displayed category]: Cat.Displayed.Base.html
[fibre categories]: Cat.Displayed.Fibre.html
[pseudo]: Cat.Bi.Base.html#pseudofunctors
[the canonical self-indexing]: Cat.Displayed.Instances.Slice.html
[pullbacks]: Cat.Diagram.Pullback.html
[a functor]: Cat.Functor.Pullback.html

```agda
module _ {𝒶 𝒷} (f : Hom 𝒶 𝒷) where
  base-change : Functor (Fibre E 𝒷) (Fibre E 𝒶)
  base-change .F₀ ob = has-lift f ob .x′
  base-change .F₁ {x} {y} vert =
    has-lift f y .universal id
      (hom[ id-comm-sym ] (vert ∘′ has-lift f x .lifting))
```

<!--
```agda
  base-change .F-id {x} = sym $
    has-lift f x .unique id′
      (  sym (from-pathp p)
      ·· (hom[]-∙ _ _ ·· reindex _ _ ·· sym (hom[]-∙ _ _))
      ·· from-pathp q
      )
    where
    p = eval′-sound (f ↑ `∘ `id) (has-lift f x .lifting ↑ `∘ `id)
    q = eval′-sound (f ↑ `∘ `id) (`hom[_]_ {f = `id `∘ (f ↑)} id-comm-sym (`id `∘ has-lift f x .lifting ↑))

  base-change .F-∘ {x} {y} {z} f′ g′ = sym $ has-lift f z .unique _
    (  pulll-indexr _ (has-lift f z .commutes _ _)
    ·· ap hom[] (
        whisker-l _ ∙ ap hom[] (
          sym (from-pathp (assoc′ _ _ _))
        ∙ ap hom[] (ap (f′ ∘′_) (has-lift f y .commutes _ _))))
    ·· hom[]-∙ _ _ ·· hom[]-∙ _ _
    ·· ap hom[] (
        whisker-r _
      ∙ ap hom[] (sym (from-pathp (symP (assoc′ _ _ _)))))
    ·· hom[]-∙ _ _ ·· hom[]-∙ _ _
    ·· reindex _ (ap (_∘ _) (idl id) ∙ id-comm-sym)
    ·· sym (hom[]-∙ _ _) ∙ ap hom[] (sym (whisker-l _)))
```
-->

Moreover, this assignment is _itself_ functorial in $f$: Along the
identity morphism, it's the same thing as not changing bases at all.

```agda
module _ {𝒶} where
  private
    module FC = Cat.Reasoning (Cat[ Fibre E 𝒶 , Fibre E 𝒶 ])
    module Fa = Cat.Reasoning (Fibre E 𝒶)

  base-change-id : base-change id FC.≅ Id
```

<details>
<summary> I'll warn you in advance that this proof is not for the faint
of heart. </summary>
```agda
  base-change-id = make-natural-iso
    (λ x → has-lift id x .lifting)
    (λ x → Fa.make-invertible (has-lift id x .universal _ (hom[ sym (idl id) ] id′))
      (ap hom[] (has-lift id x .commutes _ _) ·· hom[]-∙ _ _ ·· reindex _ _ ∙ transport-refl id′)
      (sym ( has-lift id x .unique Fa.id (sym (from-pathp (symP (idr′ _))))
           ∙ sym (has-lift id x .unique _ (pulll-indexr _ (has-lift id x .commutes _ _)
           ∙ ap hom[] (whisker-l _
           ∙ reindex _ (idl _ ∙ sym (idr _) ∙ ap (_∘ id) (sym (idr _)))
           ∙ sym (hom[]-∙ _ _)
           ∙ ap hom[] (from-pathp (idl′ _)))
           ∙ hom[]-∙ _ _ ∙ reindex _ _)))))
    λ x y f → ap hom[] (sym (has-lift id y .commutes _ _) ∙ ap₂ _∘′_ refl
      (ap (has-lift id y .universal _) (sym (reindex _ refl ∙ transport-refl _))))
```
</details>

And similarly, composing changes of base is the same thing as changing base along a composite.

```agda
module _ {𝒶} {𝒷} {𝒸} (f : Hom 𝒷 𝒸) (g : Hom 𝒶 𝒷) where
  private
    module FC = Cat.Reasoning (Cat[ Fibre E 𝒸 , Fibre E 𝒶 ])
    module Fa = Cat.Reasoning (Fibre E 𝒶)

  base-change-comp : base-change (f ∘ g) FC.≅ (base-change g F∘ base-change f)
```

<details>
<summary> This proof is a truly nightmarish application of universal
properties and I recommend that nobody look at it, ever. </summary>.

```agda
  base-change-comp = make-natural-iso
    (λ x → has-lift g _ .universal _ (has-lift f _ .universal _ (hom[ ap (f ∘_) (sym (idr g)) ] (has-lift (f ∘ g) x .lifting))))
    (λ x → Fa.make-invertible (has-lift (f ∘ g) _ .universal _ (hom[ sym (idr _) ] (has-lift f _ .lifting ∘′ has-lift g _ .lifting)))
      (sym (has-lift g _ .unique _ (sym (from-pathp (symP (idr′ _))))
          ∙ sym (has-lift g _ .unique _ (pulll-indexr _ (has-lift g _ .commutes _ _) ∙ has-lift f _ .unique _ (pulll-indexr _ (has-lift f _ .commutes _ _) ∙ ap hom[] (whisker-l _ ∙ ap hom[] (has-lift (f ∘ g) _ .commutes _ _)) ∙ hom[]-∙ _ _ ∙ hom[]-∙ _ _)
            ∙ sym (has-lift f x .unique _ (whisker-r _ ∙ reindex _ _))))))
      (sym (has-lift (f ∘ g) _ .unique _ (sym (from-pathp (symP (idr′ _))))
      ∙ sym (has-lift (f ∘ g) _ .unique _ (pulll-indexr _ (has-lift (f ∘ g) _ .commutes _ _)
      ∙ ap hom[] (whisker-l _ ∙ ap hom[] (sym (from-pathp (assoc′ _ _ _)) ∙ ap hom[] (ap₂ _∘′_ refl (has-lift g _ .commutes _ _) ∙ has-lift f _ .commutes _ _)))
      ∙ hom[]-∙ _ _ ∙ hom[]-∙ _ _ ∙ hom[]-∙ _ _ ∙ reindex _ _)))))
    λ x y f′ →
      ap hom[]
        (has-lift g (has-lift f y .x′) .unique _
          (sym (from-pathp (symP (assoc′ _ _ _ )))
          ·· ap hom[ sym (assoc _ _ _) ] (ap₂ _∘′_ (has-lift g _ .commutes id _) refl)
          ·· ap hom[ sym (assoc _ _ _) ] (whisker-l _)
          ·· hom[]-∙ _ _
          ·· ap hom[] (sym (from-pathp (assoc′ (F₁ (base-change f) f′) (has-lift g _ .lifting) (has-lift g _ .universal _ _))) ∙ ap hom[] (ap₂ _∘′_ refl (has-lift g _ .commutes _ _))) ∙ hom[]-∙ _ _ ∙ reindex _ (idl _ ∙ ap (g ∘_) (sym (idl id))))
        ) ∙ ap hom[]
        (sym (has-lift g _ .unique _ (sym (from-pathp (symP (assoc′ _ _ _))) ∙ ap hom[ sym (assoc _ _ _) ] (ap₂ _∘′_ (has-lift g _ .commutes _ _) refl)
        ∙ sym (has-lift f y .unique _ (pulll-indexr _ (has-lift f y .commutes _ _) ∙ ap hom[] (whisker-l _ ∙ ap hom[] (sym (from-pathp (assoc′ _ _ _)) ∙ ap hom[] (ap₂ _∘′_ refl (has-lift f x .commutes _ _))) ∙ hom[]-∙ _ _)
        ∙ hom[]-∙ _ _ ∙ ap hom[] (whisker-r _) ∙ reindex _ (idl _ ∙ ap (f ∘_) (ap (g ∘_) (sym (idl id)))))
        ∙ sym (has-lift f y .unique _ (pulll-indexr _ (has-lift f y .commutes _ _) ∙ ap hom[] (whisker-l  _) ∙ hom[]-∙ _ _ ∙ ap hom[] (has-lift (f ∘ g) y .commutes _ _) ∙ hom[]-∙ _ _ ∙ sym (hom[]-∙ _ _ ∙ reindex _ _)))))))
```
</details>
