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
  is-colimit x = is-lan !F Diagram (const! x)

  Colimit : Type _
  Colimit = Lan !F Diagram
```

## Concretely

The above definition is very concise, and has the benefit of being
abstract: this means that we can directly re-use definitions and
theorems for kan extensions for colimits. However, this also means
that the definition is abstract: it makes working with colimits
_in general_ easier, at the cost of making _specific_ colimits more
difficult, as the data we actually care about has been obfuscated.

For instance, it's quite hard to actually show that a specific object
is a colimit of aa diagram, as you have to wrap all the relevant data
in a few layers of abstraction. To work around this, we provide an
auxiliary record type, `make-is-colimit`{.Agda}, which computes the
appropriate left extension.

<!--
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
```
-->A

First, we require morphisms from the every value to the diagram to
the coapex; we call this family $\phi$. Moreover, if $f : x \to y$ is
a morphism in the "shape" category $\cJ$, then $\psi y \circ Ff = \psi x$,
IE: the $\psi$ family is actually natural.

```agda
    field
      ψ : (j : J.Ob) → C.Hom (F₀ j) coapex
      commutes : ∀ {x y} (f : J.Hom x y) → ψ y C.∘ F₁ f ≡ ψ x
```

The rest of the data ensures that $\psi$ is the universal family
of maps iwth this property; if $\epsilon_j : Fj \to x$ is another natural
family, then each $\epsilon_j$ factors through the coapex by a _unique_
universal morphism:

```agda
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

    unique₂
      : ∀ {x : C.Ob}
      → (eps : ∀ j → C.Hom (F₀ j) x)
      → (p : ∀ {x y} (f : J.Hom x y) → eps y C.∘ F₁ f ≡ eps x)
      → ∀ {o1} → (∀ j → o1 C.∘ ψ j ≡ eps j)
      → ∀ {o2} → (∀ j → o2 C.∘ ψ j ≡ eps j)
      → o1 ≡ o2
    unique₂ eps p q r = unique eps p _ q ∙ sym (unique eps p _ r)
```

Once we have this data, we can use it to construct a value of
`is-colimit`{.Agda}. The naturality condition we required above may
seem too weak, but the full naturality condition can be derived from
the rest of the data.

```agda
  to-is-colimit
    : ∀ {Diagram : Functor J C} {coapex}
    → make-is-colimit Diagram coapex
    → is-colimit Diagram coapex
  to-is-colimit {Diagram} {coapex} mkcolim = colim where
    open make-is-colimit mkcolim
    open is-lan
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

We also want to be able to use the interface of `make-is-colimit`{.Agda}
when we have our hands on a colimit. To do this, we provide a function
for *un*making a colimit.

```agda
  unmake-colimit
    : ∀ {D : Functor J C} {F : Functor ⊤Cat C}
    → is-lan !F D F
    → make-is-colimit D (Functor.F₀ F tt)
  unmake-colimit {D} {F} colim = mc module unmake-colimit where
    coapex = Functor.F₀ F tt
    open is-lan colim
    open Functor D
    open make-is-colimit
    open _=>_

    module _ {x} (eps : ∀ j → C.Hom (F₀ j) x)
                 (p : ∀ {x y} (f : J.Hom x y) →  eps y C.∘ F₁ f ≡ eps x)
      where

      eps-nt : D => const! x F∘ !F
      eps-nt .η = eps
      eps-nt .is-natural _ _ f = p f ∙ sym (C.idl _)

      hom : C.Hom coapex x
      hom = σ {M = const! x} eps-nt .η tt

    mc : make-is-colimit D coapex
    mc .ψ = eta.η
    mc .commutes f = eta.is-natural _ _ f ∙ C.eliml (Functor.F-id F)
    mc .universal = hom
    mc .factors e p = σ-comm {α = eps-nt e p} ηₚ _
    mc .unique {x = x} eta p other q =
      sym $ σ-uniq {σ′ = other-nt} (Nat-path λ j → sym (q j)) ηₚ tt
      where
        other-nt : F => const! x
        other-nt .η _ = other
        other-nt .is-natural _ _ _ = C.elimr (Functor.F-id F) ∙ sym (C.idl _)
```

<!--
```agda
module is-colimit
  {J : Precategory o₁ h₁} {C : Precategory o₂ h₂}
  {D : Functor J C} {F : Functor ⊤Cat C} (t : is-lan !F D F)
  where

  open make-is-colimit (unmake-colimit {F = F} t) public
```
-->

We also provide a similar interface for the bundled form of colimits.

```agda
module Colimit
  {J : Precategory o₁ h₁} {C : Precategory o₂ h₂} {D : Functor J C} (L : Colimit D)
  where
```

<!--
```agda
  private
    import Cat.Reasoning J as J
    import Cat.Reasoning C as C
    module Diagram = Functor D
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

<!--
```agda
  open is-colimit has-lan public  
```
-->


# Uniqueness

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

# Preservation of Colimits

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
  Preserves-colimit : Type _
  Preserves-colimit = ∀ x → is-colimit Diagram x → is-colimit (F F∘ Diagram) (F.₀ x)

  Reflects-colimit : Type _
  Reflects-colimit = ∀ x → is-colimit (F F∘ Diagram) (F.₀ x) → is-colimit Diagram x

  record creates-colimit : Type (o₁ ⊔ h₁ ⊔ o₂ ⊔ h₂ ⊔ o₃ ⊔ h₃) where
    field
      preserves-colimit : Preserves-colimit
      reflects-colimit : Reflects-colimit
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
  → Preserves-colimit F Diagram
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
