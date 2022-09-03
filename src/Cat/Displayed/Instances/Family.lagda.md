```agda
open import Cat.Displayed.Cartesian
open import Cat.Functor.Equivalence
open import Cat.Instances.Discrete
open import Cat.Instances.Functor
open import Cat.Displayed.Fibre
open import Cat.Displayed.Base
open import Cat.Functor.Base
open import Cat.Univalent
open import Cat.Prelude

import Cat.Reasoning

module Cat.Displayed.Instances.Family {o h} (C : Precategory o h) where
```

<!--
```agda
open Cat.Reasoning C
open Displayed
open Functor
open _=>_
```
-->

# The family fibration

We can canonically treat any `Precategory`{.Agda} $\mathcal{C}$ as being
displayed over `Sets`{.Agda}, regardless of the size of the object- and
Hom-spaces of $\mathcal{C}$.

In a neutral presentation of displayed category theory, the collection
of objects over $S$ would given by the space of functors
$[\id{Disc}(S),C]$, regarding $S$ as a discrete category.  This is
essentially an $S$-indexed family of objects of $C$, hence the name
"family fibration". To reduce the noise, however, in HoTT we can (ab)use
the fact that all precategories have a _space of objects_, and say that
the objects over $S$ are precisely the families $S \to \id{Ob}_\ca{C}$.

```agda
Family : ∀ {ℓ} → Displayed (Sets ℓ) _ _
Family .Ob[_] S = ∣ S ∣ → Ob
```

The set of maps over a function $f : A \to B$ (in $\sets$) is the set of
families of morphisms $F(x) \to G(fx)$. Here we are abusing that, for
functors between discrete categories, naturality is automatic.

```agda
Family .Hom[_] {A} {B} f F G =
  ∀ x → Hom (F x) (G (f x))
Family .Hom[_]-set f x y = hlevel 2
```

The identity and composition operations are as for natural
transformations, but without the requirement for naturality.

```agda
Family .id′ x = id
Family ._∘′_ {f = f} {g = g} f′ g′ x = f′ (g x) ∘ g′ x
Family .idr′ _ = funext λ x → idr _
Family .idl′ _ = funext λ x → idl _
Family .assoc′ _ _ _ = funext λ _ → assoc _ _ _
```

The family fibration is a Cartesian fibration, essentially by solving an
_associativity_ problem. Given a function $f : x \to y$ and a family $Y$
over $y$, we must _define_ a family $X$ over $x$ and give a universal
family of functions $X(a) \to Y(f(a))$. But we may simply take $X(a) :=
Y(f(a))$, and family is constantly the identity map.

```agda
open Cartesian-fibration
open Cartesian-lift
open Cartesian

Family-is-cartesian : ∀ {ℓ} → Cartesian-fibration (Family {ℓ = ℓ})
Family-is-cartesian = iscart where
  cart : ∀ {x y : Set _} (f : ∣ x ∣ → ∣ y ∣)
           (y′ : ∣ y ∣ → Ob)
       → Cartesian Family f λ _ → id
  cart f y′ .universal m nt = nt
  cart f y′ .commutes m h′ = funext λ _ → idl _
  cart f y′ .unique m′ p = funext λ _ → introl refl ∙ happly p _

  iscart : Cartesian-fibration Family
  iscart .has-lift f y′ .x′ z = y′ (f z)
  iscart .has-lift f y′ .lifting x = id
  iscart .has-lift {x = x} {y} f y′ .cartesian = cart {x = x} {y} f y′
```

## Fibres

We now prove that the [fibres](Cat.Displayed.Fibre.html) of the family
fibration are indeed the expected functor categories. This involves a
bit of annoying calculation, but it will let us automatically prove that
the family fibration is fibrewise univalent whenever $\ca{C}$ is.

```agda
module _ {ℓ} (X : Set ℓ) where
  private
    lift-f = Disc-adjunct {C = C} {iss = is-hlevel-suc 2 (X .is-tr)}
    module F = Cat.Reasoning (Fibre Family X)

  Families→functors : Functor (Fibre Family X) Cat[ Disc′ X , C ]
  Families→functors .F₀ = Disc-adjunct
  Families→functors .F₁ f .η = f
  Families→functors .F₁ {X} {Y} f .is-natural x y =
    J (λ y p → f y ∘ lift-f X .F₁ p ≡ lift-f Y .F₁ p ∘ f x)
      (ap (f x ∘_) (lift-f X .F-id) ·· id-comm ·· ap (_∘ f x) (sym (lift-f Y .F-id)))
  Families→functors .F-id = Nat-path λ x → refl
  Families→functors .F-∘ f g =
    ap (Families→functors .F₁) (transport-refl _) ∙ Nat-path λ x → refl

  Families→functors-is-ff : is-fully-faithful Families→functors
  Families→functors-is-ff = is-iso→is-equiv
    (iso η (λ x → Nat-path λ _ → refl) λ x → refl)

  open is-precat-iso
  Families→functors-is-iso : is-precat-iso Families→functors
  Families→functors-is-iso .has-is-ff = Families→functors-is-ff
  Families→functors-is-iso .has-is-iso =
    is-iso→is-equiv (iso F₀
      (λ x → Functor-path (λ _ → refl)
        (J (λ _ p → lift-f (x .F₀) .F₁ p ≡ x .F₁ p)
           (lift-f (x .F₀) .F-id ∙ sym (x .F-id))))
      (λ x → refl))

  Families-are-categories : is-category C → is-category (Fibre Family X)
  Families-are-categories isc .to-path im = funext λ x →
    isc .to-path $ make-iso (im .F.to x) (im .F.from x)
      (happly (sym (transport-refl (λ y → im .F.to y ∘ im .F.from y)) ∙ im .F.invl) x)
      (happly (sym (transport-refl (λ y → im .F.from y ∘ im .F.to y)) ∙ im .F.invr) x)
  Families-are-categories isc .to-path-over im = F.≅-pathp refl _ $ funextP λ a →
    Hom-pathp-reflr {C = C} (elimr refl ∙ ap to (Univalent.iso→path→iso isc _))
```
