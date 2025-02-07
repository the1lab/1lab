<!--
```agda
open import Cat.Functor.Adjoint.Continuous
open import Cat.Instances.Functor.Duality
open import Cat.Diagram.Colimit.Base
open import Cat.Functor.Equivalence
open import Cat.Diagram.Limit.Base
open import Cat.Instances.Functor
open import Cat.Instances.Product
open import Cat.Functor.Closed
open import Cat.Diagram.Duals
open import Cat.Prelude
```
-->

```agda
module Cat.Instances.Functor.Limits where
```

# Limits in functor categories

Let $\cC$ be a category admitting $\cD$-shaped limits. Then the
functor category $[\cE,\cS]$, for $\cE$ _any_ category, also
admits $\cD$-shaped limits. In particular, if $\cC$ is
$(\iota,\kappa)$-complete, then so is $[\cE,\cC]$.

```agda
module _
  {o₁ ℓ₁} {C : Precategory o₁ ℓ₁}
  {o₂ ℓ₂} {D : Precategory o₂ ℓ₂}
  {o₃ ℓ₃} {E : Precategory o₃ ℓ₃}
  (has-D-lims : (F : Functor D C) → Limit F)
  (F : Functor D Cat[ E , C ])
  where
```

<!--
```agda
  open Functor
  open _=>_

  import Cat.Reasoning C as C
  import Cat.Reasoning D as D
  import Cat.Reasoning E as E

  private
    module F = Functor F
```
-->

Let $F : \cD \to [\cE,\cC]$ be a diagram, and suppose $\cC$
admits limits of $\cD$-shaped diagrams; We wish to compute the limit
$\lim F$. First, observe that we can `Uncurry`{.Agda} $F$ to obtain a
functor $F' : \cD \times \cE \to \cC$; By fixing the value of
the $\cE$ coordinate (say, to $x$), we obtain a family $F(-, x)$ of
$\cD$-shaped diagrams in $\cC$, which, by assumption, all have
limits.

```agda
    F-uncurried : Functor (D ×ᶜ E) C
    F-uncurried = Uncurry {C = D} {D = E} {E = C} F

    import Cat.Functor.Bifunctor {C = D} {D = E} {E = C} F-uncurried as F'
    module D-lim x = Limit (has-D-lims (F'.Left x))
```

Let us call the limit of $F(-, x)$ --- taken in $\cC$ ---
`lim-for`{.Agda}, and similarly the unique, "terminating" cone
homomorphism $K \to \lim F(-, x)$ will be called `!-for`{.Agda}.

```agda
    !-for : ∀ {x y} (f : E.Hom x y) → C.Hom (D-lim.apex x) (D-lim.apex y)
    !-for {x} {y} f =
      D-lim.universal y
        (λ j → F'.Right j .F₁ f C.∘ D-lim.ψ x j)
        (λ g →
          C.extendl F'.first∘second
          ∙ ap₂ C._∘_ refl (D-lim.commutes x g))

    functor-apex : Functor E C
    functor-apex .F₀ x = D-lim.apex x
    functor-apex .F₁ {x} {y} f = !-for f
    functor-apex .F-id =
      sym $ D-lim.unique _ _ _ _ λ j →
        C.idr _ ∙ sym (D-lim.commutes _ _)
    functor-apex .F-∘ f g =
      sym $ D-lim.unique _ _ _ _ λ j →
        C.pulll (D-lim.factors _ _ _)
        ∙ C.pullr (D-lim.factors _ _ _)
        ∙ C.pulll (sym (F'.Right _ .F-∘ _ _))

  functor-limit : Limit F
  functor-limit = to-limit $ to-is-limit ml where
    open make-is-limit

    ml : make-is-limit F functor-apex
    ml .ψ j .η x = D-lim.ψ x j
    ml .ψ j .is-natural x y f =
      D-lim.factors _ _ _ ∙ ap₂ C._∘_ (C.eliml (F.F-id ηₚ _)) refl
    ml .commutes f = ext λ j →
      C.pushr (C.introl (F.₀ _ .F-id)) ∙ D-lim.commutes j f
    ml .universal eps p .η x = D-lim.universal x
      (λ j → eps j .η x)
      (λ f → ap₂ C._∘_ (C.elimr (F.₀ _ .F-id)) refl ∙ p f ηₚ x)
    ml .universal eps p .is-natural x y f = D-lim.unique₂ y _
      (λ g → C.pulll (ap₂ C._∘_ (C.elimr (F.₀ _ .F-id)) refl ∙ p g ηₚ y))
      (λ j → C.pulll (D-lim.factors _ _ _))
      (λ j →
          C.pulll (D-lim.factors _ _ _)
        ∙ C.pullr (D-lim.factors _ _ _)
        ∙ ap₂ C._∘_ (C.eliml (F.F-id ηₚ _)) refl
        ∙ sym (eps j .is-natural x y f))
    ml .factors eps p = ext λ j →
      D-lim.factors j _ _
    ml .unique eps p other q = ext λ x →
      D-lim.unique _ _ _ _ λ j → q j ηₚ x
```

As a corollary, if $\cD$ is an $(o,\ell)$-complete category, then so
is $[\cC,\cD]$.

```agda
Functor-cat-is-complete :
  ∀ {o ℓ} {o₁ ℓ₁} {C : Precategory o₁ ℓ₁} {o₂ ℓ₂} {D : Precategory o₂ ℓ₂}
  → is-complete o ℓ D → is-complete o ℓ Cat[ C , D ]
Functor-cat-is-complete D-complete = functor-limit D-complete
```

<!--
```agda
module _
  {o₁ ℓ₁} {C : Precategory o₁ ℓ₁}
  {o₂ ℓ₂} {D : Precategory o₂ ℓ₂}
  {o₃ ℓ₃} {E : Precategory o₃ ℓ₃}
  (has-D-colims : ∀ (F : Functor D C) → Colimit F)
  (F : Functor D Cat[ E , C ])
  where

  functor-colimit : Colimit F
  functor-colimit = colim where
    F' : Functor (D ^op) Cat[ E ^op , C ^op ]
    F' = op-functor→ F∘ Functor.op F

    F'-lim : Limit F'
    F'-lim = functor-limit
      (λ f → subst Limit F^op^op≡F (Colimit→Co-limit (has-D-colims (Functor.op f))))
      F'

    LF'' : Limit (op-functor← {C = E} {D = C} F∘ (op-functor→ F∘ Functor.op F))
    LF'' = right-adjoint-limit (is-equivalence.F⊣F⁻¹ op-functor-is-equiv) F'-lim

    LFop : Limit (Functor.op F)
    LFop = subst Limit (F∘-assoc ∙ ap (_F∘ Functor.op F) op-functor←→ ∙ F∘-idl) LF''

    colim : Colimit F
    colim = Co-limit→Colimit LFop

Functor-cat-is-cocomplete :
  ∀ {o ℓ} {o₁ ℓ₁} {C : Precategory o₁ ℓ₁} {o₂ ℓ₂} {D : Precategory o₂ ℓ₂}
  → is-cocomplete o ℓ D → is-cocomplete o ℓ Cat[ C , D ]
Functor-cat-is-cocomplete D-cocomplete = functor-colimit D-cocomplete
```
-->
