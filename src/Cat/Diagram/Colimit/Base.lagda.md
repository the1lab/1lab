```agda
open import Cat.Functor.Kan.Left
open import Cat.Instances.Functor
open import Cat.Instances.Shape.Terminal
open import Cat.Prelude

import Cat.Functor.Reasoning as Func
import Cat.Reasoning

module Cat.Diagram.Colimit.Base where
```

<!--
```agda
private variable
  o ℓ o′ ℓ′ : Level
```
-->

# Idea

Colimits are dual to limits [limit]; much like their cousins, they
generalize constructions in several settings to arbitrary categories.
A colimit (if it exists), is the "best solution" to an
"identification problem". This is in contrast to the limit, which
acts as a solution to an "equational problem".

[limit]: Cat.Diagram.Limit.Base.html

We define colimits in a similar way to limits; the only difference being
that we define a colimits of a diagram $F$ as [left kan extensions]
instead of [right kan extensions]. This gives us the expected
"mapping out" universal property, as opposed to the "mapping in" property
associated to limits.

[left kan extension]: Cat.Functor.Kan.Left.html
[right kan extension]: Cat.Functor.Kan.Right.html

Note that approach to colimits is not what normally presented in
introductory material. Instead, most books opt to define colimits
via [cocones], as they are less abstract, though harder to work with
in the long run.

[cocones]: Cat.Diagram.Colimit.Cocone.html

<!--
```agda
private variable
  o₁ o₂ o₃ h₁ h₂ h₃ : Level
```
-->

```agda
module _ {J : Precategory o₁ h₁} {C : Precategory o₂ h₂} (Diagram : Functor J C) where
  private
    module C = Precategory C

  is-colimit : C.Ob → Type _
  is-colimit x = is-left-kan-extension !F Diagram (const! x)

  Colimit : Type _
  Colimit = Lan !F Diagram
```

These definitions are a bit difficult to work with as they are, so we
define more human-friendly interface.

```agda
module is-colimit
  {J : Precategory o₁ h₁} {C : Precategory o₂ h₂}
  {Diagram : Functor J C} {coapex}
  (L : is-colimit Diagram coapex)
  where
```

<!--
```agda

  private
    module J = Cat.Reasoning J
    module C = Cat.Reasoning C
    module Diagram = Functor Diagram
  
    open is-left-kan-extension L
    open Functor
    open _=>_
```
-->

If $x$ is the limit of $D$, then we have map to $x$ from every object
in the diagram.

```agda
  ψ : (j : J.Ob) → C.Hom (Diagram.₀ j) coapex
  ψ j = hom
    module colimit-proj where
      hom : C.Hom (Diagram.₀ j) coapex
      hom = eta .η j
```

<!--
```agda
  {-# DISPLAY colimit-proj.hom x = ψ x #-}
```
-->

Furthermore, these maps must commute with all morphisms in the diagram.

```agda
  commutes : ∀ {x y} (f : J.Hom x y) → ψ y C.∘ Diagram.₁ f ≡ ψ x
  commutes {x} f = eta .is-natural x _ f ∙ C.idl _
```

We also have a universal map out of $x$ to any other object $y$
that also has the required commuting maps into the diagram.

```agda
  universal
    : ∀ {x : C.Ob}
    → (eps : ∀ j → C.Hom (Diagram.₀ j) x)
    → (∀ {x y} (f : J.Hom x y) → eps y C.∘ Diagram.₁ f ≡ eps x)
    → C.Hom coapex x
  universal {x = x} eps p = hom
    module colimit-universal where
      eps-nt : Diagram => const! x F∘ !F
      eps-nt .η = eps
      eps-nt .is-natural _ _ f = p f ∙ sym (C.idl _)

      hom : C.Hom coapex x
      hom = σ {M = const! x} eps-nt .η tt
```

<!--
```agda
  {-# DISPLAY colimit-universal.hom eta p = universal eta p #-}
```
-->

Furthermore, all maps into $x$ from the diagram commute with the
universal map.

```agda
  factors
    : ∀ {j : J.Ob} {x : C.Ob}
    → (eps : ∀ j → C.Hom (Diagram.₀ j) x)
    → (p : ∀ {x y} (f : J.Hom x y) → eps y C.∘ Diagram.₁ f ≡ eps x)
    → universal eps p C.∘ ψ j ≡ eps j
  factors eta p = σ-comm {α = colimit-universal.eps-nt eta p} ηₚ _
```

Finally, this map is unique.

```agda
  unique
    : ∀ {x : C.Ob}
    → (eps : ∀ j → C.Hom (Diagram.₀ j) x)
    → (p : ∀ {x y} (f : J.Hom x y) → eps y C.∘ Diagram.₁ f ≡ eps x)
    → (other : C.Hom coapex x)
    → (∀ j → other C.∘ ψ j ≡ eps j)
    → other ≡ universal eps p
  unique {x = x} eps _ other q =
    sym $ σ-uniq {σ′ = other-nt} (Nat-path (λ j → sym (q j))) ηₚ tt
    where
      other-nt : const! coapex => const! x
      other-nt .η _ = other
      other-nt .is-natural _ _ _ = C.id-comm

  unique₂
    : ∀ {x : C.Ob}
    → (eps : ∀ j → C.Hom (Diagram.₀ j) x)
    → (p : ∀ {x y} (f : J.Hom x y) → eps y C.∘ Diagram.₁ f ≡ eps x)
    → ∀ {o1} → (∀ j → o1 C.∘ ψ j ≡ eps j)
    → ∀ {o2} → (∀ j → o2 C.∘ ψ j ≡ eps j)
    → o1 ≡ o2
  unique₂ eps p q r = unique eps p _ q ∙ sym (unique eps p _ r)
```

We also provide an interface for the bundled form of colimits.

```agda
module Colimit
  {J : Precategory o₁ h₁} {C : Precategory o₂ h₂}
  {Diagram : Functor J C}
  (L : Colimit Diagram)
  where
```

<!--
```agda
  private
    import Cat.Reasoning J as J
    import Cat.Reasoning C as C
    module Diagram = Functor Diagram
    open Lan L
    open Functor
    open _=>_
```
-->

The coapex of the colimit can be obtained by applying the extension functor
to the single object of `⊤Cat`{.Agda}.

```agda
  coapex : C.Ob
  coapex = Ext .F₀ tt
```

We also show that the coapex is indeed the colimit of the diagram.
This is a bit annoying, as Agda isn't able to realize that all functors
out of `⊤Cat`{.Agda} are constant.

```agda
  has-colimit : is-colimit Diagram coapex
  has-colimit .is-left-kan-extension.eta .η = eta .η
  has-colimit .is-left-kan-extension.eta .is-natural x y f =
    eta .is-natural x y f ∙ ap (C._∘ _) (Ext .F-id)
  has-colimit .is-left-kan-extension.σ α .η = σ α .η
  has-colimit .is-left-kan-extension.σ α .is-natural x y f =
    ap (_ C.∘_) (sym (Ext .F-id)) ∙ σ α .is-natural tt tt tt
  has-colimit .is-left-kan-extension.σ-comm =
    Nat-path (λ _ → σ-comm ηₚ _)
  has-colimit .is-left-kan-extension.σ-uniq {M = M} {σ′ = σ′} p =
    Nat-path (λ _ → σ-uniq {σ′ = nt} (Nat-path (λ j → p ηₚ j)) ηₚ _)
    where
      nt : Ext => M
      nt .η = σ′ .η
      nt .is-natural x y f = ap (_ C.∘_) (Ext .F-id) ∙ σ′ .is-natural x y f
```

## Constructing Colimits

Writing out colimits as kan extensions can get a bit tedious, so we also
define a nicer interface for constructing colimits.


```agda
module _ {J : Precategory o₁ h₁} {C : Precategory o₂ h₂}
  where
  private
    module J = Precategory J
    module C = Cat.Reasoning C

  record make-is-colimit
    (Diagram : Functor J C) (coapex : C.Ob)
    : Type (o₁ ⊔ h₁ ⊔ o₂ ⊔ h₂)
    where
    no-eta-equality
    open Functor Diagram
    field
      ψ : (j : J.Ob) → C.Hom (F₀ j) coapex
      commutes : ∀ {x y} (f : J.Hom x y) → ψ y C.∘ F₁ f ≡ ψ x
      universal
        : ∀ {x : C.Ob}
        → (eps : ∀ j → C.Hom (F₀ j) x)
        → (∀ {x y} (f : J.Hom x y) → eps y C.∘ F₁ f ≡ eps x)
        → C.Hom coapex x
      factors
        : ∀ {j : J.Ob} {x : C.Ob}
        → (eps : ∀ j → C.Hom (F₀ j) x)
        → (p : ∀ {x y} (f : J.Hom x y) → eps y C.∘ F₁ f ≡ eps x)
        → universal eps p C.∘ ψ j ≡ eps j
      unique
        : ∀ {x : C.Ob}
        → (eps : ∀ j → C.Hom (F₀ j) x)
        → (p : ∀ {x y} (f : J.Hom x y) → eps y C.∘ F₁ f ≡ eps x)
        → (other : C.Hom coapex x)
        → (∀ j → other C.∘ ψ j ≡ eps j)
        → other ≡ universal eps p

  to-is-colimit
    : ∀ {Diagram : Functor J C} {coapex}
    → make-is-colimit Diagram coapex
    → is-colimit Diagram coapex
  to-is-colimit {Diagram} {coapex} mkcolim = colim where
    open make-is-colimit mkcolim
    open is-left-kan-extension
    open Functor
    open _=>_

    colim : is-colimit Diagram coapex
    colim .eta .η = ψ
    colim .eta .is-natural _ _ f =
      commutes f ∙ sym (C.idl _)
    colim .σ {M = M} α .η _ =
      universal (α .η) (λ f → α .is-natural _ _ f ∙ C.eliml (M .F-id))
    colim .σ {M = M} α .is-natural _ _ _ =
       C.idr _ ∙ C.introl (M .F-id)
    colim .σ-comm {α = α} = Nat-path λ j →
      factors (α .η) _
    colim .σ-uniq {α = α} {σ′ = σ′} p = Nat-path λ _ →
      sym $ unique (α .η) _ (σ′ .η _) (λ j → sym (p ηₚ j))
```

## Uniqueness

[Much like limits], colimits are unique up to isomorphism.

[Much like limits]: Cat.Diagram.Limit.Base#uniqueness

<!--
```agda
module _ {o₁ h₁ o₂ h₂ : _} {J : Precategory o₁ h₁} {C : Precategory o₂ h₂}
         (Diagram : Functor J C)
       where
  private
    module J = Precategory J
    module C = Cat.Reasoning C
    module Diagram = Functor Diagram
```
-->

```agda
  colimits-unique
    : ∀ {x y}
    → is-colimit Diagram x
    → is-colimit Diagram y
    → x C.≅ y
  colimits-unique {x} {y} L L′ =
    C.make-iso
      (L.universal L′.ψ L′.commutes)
      (L′.universal L.ψ L.commutes)
      (L′.unique₂ L′.ψ L′.commutes
        (λ j → C.pullr (L′.factors L.ψ L.commutes) ∙ L.factors L′.ψ L′.commutes)
        λ j → C.idl _)
      (L.unique₂ L.ψ L.commutes
        (λ j → C.pullr (L.factors L′.ψ L′.commutes) ∙ L′.factors L.ψ L.commutes)
        λ j → C.idl _)
    where
      module L = is-colimit L
      module L′ = is-colimit L′
```

## Preservation of Colimits

The definitions here are the same idea as [preservation of limits], just
dualized.

[preservation of limits]: Cat.Diagram.Limit.Base#preservation-of-limits

<!--
```agda
module _ {J : Precategory o₁ h₁} {C : Precategory o₂ h₂} {D : Precategory o₃ h₃}
         (F : Functor C D) (Diagram : Functor J C) where
  private
    module D = Precategory D
    module C = Precategory C
    module J = Precategory J
    module F = Func F
```
-->

```agda
  preserves-colimit : Type _
  preserves-colimit = ∀ x → is-colimit Diagram x → is-colimit (F F∘ Diagram) (F.₀ x)

  reflects-colimit : Type _
  reflects-colimit = ∀ x → is-colimit (F F∘ Diagram) (F.₀ x) → is-colimit Diagram x

  record creates-colimit : Type (o₁ ⊔ h₁ ⊔ o₂ ⊔ h₂ ⊔ o₃ ⊔ h₃) where
    field
      preserves : preserves-colimit
      reflects : reflects-colimit
```

## Cocontinuity

```agda
is-cocontinuous
  : ∀ {oshape hshape}
      {C : Precategory o₁ h₁}
      {D : Precategory o₂ h₂}
  → Functor C D → Type _
```

A cocontinuous functor is one that --- for every shape of diagram `J`,
and every diagram `diagram`{.Agda} of shape `J` in `C` --- preserves the
colimit for that diagram.

```agda
is-cocontinuous {oshape = oshape} {hshape} {C = C} F =
  ∀ {J : Precategory oshape hshape} {Diagram : Functor J C}
  → preserves-colimit F Diagram
```

## Cocompleteness

A category is **cocomplete** if admits for limits of arbitrary shape.
However, in the presence of excluded middle, if a category admits
coproducts indexed by its class of morphisms, then it is automatically
[thin]. Since excluded middle is independent of type theory, we can not
prove that any non-thin categories have arbitrary colimits.

Instead, categories are cocomplete _with respect to_ a pair of
universes: A category is **$(o, \ell)$-cocomplete** if it has colimits
for any diagram indexed by a precategory with objects in $\ty\ o$ and
morphisms in $\ty\ \ell$.

```agda
is-cocomplete : ∀ {oc ℓc} o ℓ → Precategory oc ℓc → Type _
is-cocomplete o ℓ C = ∀ {D : Precategory o ℓ} (F : Functor D C) → Colimit F
```
