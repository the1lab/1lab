<!--
```agda
open import Cat.Displayed.Cartesian.Indexing
open import Cat.Displayed.Instances.Pullback
open import Cat.Displayed.Instances.Lifting
open import Cat.Displayed.Cartesian
open import Cat.Functor.Equivalence
open import Cat.Displayed.Functor
open import Cat.Instances.Functor
open import Cat.Displayed.Fibre
open import Cat.Displayed.Base
open import Cat.Prelude

import Cat.Displayed.Reasoning
import Cat.Reasoning
```
-->

```agda
module Cat.Displayed.Instances.Diagrams
  {o ℓ o' ℓ'}
  {B : Precategory o ℓ}
  (E : Displayed B o' ℓ')
  where

open Cat.Reasoning B
open Displayed E
open Cat.Displayed.Reasoning E
open Functor
open _=>_
```

# The Diagram Fibration

The appropriate notion of structure for a displayed category $\cE
\liesover \cB$ is fibrewise structure: structure found in each [fibre
category], preserved by the reindexing functors when $\cE$ is an
(op)fibration.

For instance, the correct notion of $\cJ$-shaped limit in $\cE$ are the
**fibred limits**: where every fibre category has limits of shape $\cJ$,
and these are preserved by reindexing. Unfortunately, proof assistants:
since none of the commutativity conditions for limits are definitional,
this definition condemns the formaliser to transport hell.

[fibre category]: Cat.Displayed.Fibre.html

Instead, we opt for a more abstract approach, which starts with a
reorganization of what a fibrewise diagram in $\cE$ is. Recall that the
[fibration of liftings] describes liftings of functors $\cJ \to \cB$
along the projection functor $\pi : \int \cE \to \cB$. If we focus on
liftings along a constant functor $\Delta_{x} : \cJ \to \cB$, we get a
diagram in $\cE$ that lies entirely in the fibre $\cE_{x}$: a fibrewise
diagram!

we could concisely define the fibration of fibrewise diagrams
as the base change of $\cE \to \cB$ along the functor $\cB \to [\cJ,
\cB]$ that takes an object to the constant diagram on that object, but
this runs into some annoying issues with transports. Therefore, we
unfold the definition instead.

[fibration of liftings]: Cat.Displayed.Instances.Lifting.html

<!--
```agda
open Lifting
open _=[_]=>l_
```
-->

```agda
Diagrams
 : ∀ {oj ℓj} (J : Precategory oj ℓj)
 → Displayed B _ _
Diagrams J .Ob[_] b = Lifting {J = J} E (Const b)
Diagrams J .Hom[_] u F G = F =[ const-nt u ]=>l G
Diagrams J .Hom[_]-set _ _ _ = Nat-lift-is-set
Diagrams J .id′ .η′ _ = id′
Diagrams J .id′ .is-natural′ _ _ _ =
  cast[] $ idl′ _ ∙[] symP (idr′ _)
Diagrams J ._∘′_ α β .η′ j = α .η′ j ∘′ β .η′ j
Diagrams J ._∘′_ α β .is-natural′ x y f =
  cast[] $ pullr[] _ (β .is-natural′ x y f) ∙[] extendl[] _ (α .is-natural′ x y f)
Diagrams J .idr′ α = Nat-lift-pathp λ _ → idr′ _
Diagrams J .idl′ α = Nat-lift-pathp λ _ → idl′ _
Diagrams J .assoc′ α β γ = Nat-lift-pathp λ _ → assoc′ _ _ _
```

<!--
```agda
module _ {oj ℓj} (J : Precategory oj ℓj) where
  private module J = Precategory J
  open Lifting
  open _=[_]=>l_
```
-->

## As a fibration

We begin by characterizing the cartesian maps in the diagram fibration.
Like the fibration of liftings, these are the pointwise cartesian maps.
This proof is identical to `pointwise-cartesian→Liftings-cartesian`{.Agda},
but we are off by some definitional equalities, so we have to unfold
some things.

```agda
  pointwise-cartesian→Diagram-cartesian
    : ∀ {x y : Ob} {F : Lifting E (Const x)} {G : Lifting E (Const y)}
    → {u : Hom x  y} {α : F =[ const-nt u ]=>l G}
    → (∀ j → is-cartesian E u (α .η′ j))
    → is-cartesian (Diagrams J) u α
  pointwise-cartesian→Diagram-cartesian {u = u} {α = α} pointwise = cart where
    module pointwise x = is-cartesian (pointwise x)

    cart : is-cartesian (Diagrams J) u α
    cart .is-cartesian.universal m β .η′ x =
      pointwise.universal x m (β .η′ x)
    cart .is-cartesian.universal m β .is-natural′ x y f =
      pointwise.uniquep₂ _ _ _ _ _ _
        (pulll[] _ (pointwise.commutes _ _ _) ∙[] β .is-natural′ _ _ _)
        (pulll[] _ (α .is-natural′ x y f)
        ∙[] pullr[] _ (pointwise.commutes _ _ _))
    cart .is-cartesian.commutes m β =
      Nat-lift-pathp (λ _ → pointwise.commutes _ _ _)
    cart .is-cartesian.unique β' p =
      Nat-lift-pathp (λ x → pointwise.unique _ _ λ i → p i .η′ x)
```

We can use the previous fact to show that the fibration of diagrams is
actually a fibration. Luckily, we get to re-use a lot of the proof
that the fibration of liftings is a fibration.

```agda
  Diagram-fibration : Cartesian-fibration E → Cartesian-fibration (Diagrams J)
  Diagram-fibration fib .Cartesian-fibration.has-lift f F = cart-lift where
    module fib = Cartesian-fibration.has-lift fib
    open Cartesian-fibration (Liftings-fibration E J fib)

    cart-lift : Cartesian-lift _ f F
    cart-lift .Cartesian-lift.x′ = has-lift.x′ (const-nt f) F
    cart-lift .Cartesian-lift.lifting = has-lift.lifting (const-nt f) F
    cart-lift .Cartesian-lift.cartesian =
      pointwise-cartesian→Diagram-cartesian (λ _ → fib.cartesian _ _)
```

## The constant fibrewise diagram functor

Crucially, we have a "constant fibrewise diagram functor" that takes an
object $x' : E_{x}$ to the constant diagram. However, defining this
functor will require a small bit of machinery.

To begin, we characterize liftings of the constant functor, and natural
transformations between them.

```agda
  ConstL : ∀ {x} → Ob[ x ] → Lifting {J = J} E (Const x)
  ConstL x' .F₀′ _ = x'
  ConstL x' .F₁′ _ = id′
  ConstL x' .F-id′ = refl
  ConstL x' .F-∘′ _ _ = symP (idr′ _)

  const-ntl
    : ∀ {x y x' y'} {f : Hom x y} → Hom[ f ] x' y'
    → (ConstL x') =[ const-nt f ]=>l (ConstL y')
  const-ntl f' .η′ _ = f'
  const-ntl f' .is-natural′ _ _ _ =
    idr′ _ ∙[] symP (idl′ _)
```

We also have a vertical functor from $\cE$ to the fibration of diagrams
of shape $\cJ$, which takes an $x'$ to the constant diagram.

```agda
  ConstFibD : Vertical-functor E (Diagrams J)
  ConstFibD .Vertical-functor.F₀′ = ConstL
  ConstFibD .Vertical-functor.F₁′ = const-ntl
  ConstFibD .Vertical-functor.F-id′ =
    Nat-lift-pathp (λ x → refl)
  ConstFibD .Vertical-functor.F-∘′ =
    Nat-lift-pathp (λ x → refl)
```

Furthermore, this functor is fibred.

```agda
  ConstFibD-fibred : is-vertical-fibred ConstFibD
  ConstFibD-fibred f′ cart =
    pointwise-cartesian→Diagram-cartesian (λ _ → cart)
```

We will use the fibred version of this functor quite a bit, so we give
it a nice short name.

```agda
  Δd : Vertical-fibred-functor E (Diagrams J)
  Δd .Vertical-fibred-functor.vert = ConstFibD
  Δd .Vertical-fibred-functor.F-cartesian = ConstFibD-fibred
```

Next, we note that liftings of the constant functor correspond with
diagrams in fibre categories.

```agda
  ConstL→Diagram
    : ∀ {x} → Lifting {J = J} E (Const x) → Functor J (Fibre E x)
  Diagram→ConstL
    : ∀ {x} → Functor J (Fibre E x) → Lifting {J = J} E (Const x)
```

<!--
```agda
  ConstL→Diagram F' .F₀ = F' .F₀′
  ConstL→Diagram F' .F₁ = F' .F₁′
  ConstL→Diagram F' .F-id = F' .F-id′
  ConstL→Diagram F' .F-∘ f g =
    from-pathp⁻ $ cast[] {q = sym (idl _)} (F' .F-∘′ f g)

  Diagram→ConstL F .F₀′ = F .F₀
  Diagram→ConstL F .F₁′ = F .F₁
  Diagram→ConstL F .F-id′ = F .F-id
  Diagram→ConstL F .F-∘′ f g =
    cast[] {p = sym (idl _)} $ to-pathp⁻ (F .F-∘ f g)
```
-->

Furthermore, natural transformations between diagrams in a fibre of $E$
correspond to natural transformations between liftings of a constant
functor.

```agda
  ConstL-natl→Diagram-nat
    : ∀ {x} {F G : Functor J (Fibre E x)}
    → Diagram→ConstL F =[ const-nt id ]=>l Diagram→ConstL G
    → F => G

  Diagram-nat→ConstL-natl
    : ∀ {x} {F G : Functor J (Fibre E x)}
    → F => G
    → Diagram→ConstL F =[ const-nt id ]=>l Diagram→ConstL G
```

<!--
```agda
  ConstL-natl→Diagram-nat α' .η = α' .η′
  ConstL-natl→Diagram-nat α' .is-natural x y f =
    ap hom[] (cast[] $ α' .is-natural′ x y f)

  Diagram-nat→ConstL-natl α .η′ = α .η
  Diagram-nat→ConstL-natl {F = F} {G = G} α .is-natural′ x y f =
    cast[] $
      to-pathp (α .is-natural x y f)
      ∙[] symP (transport-filler (λ i → Hom[ idl id i ] _ _) (F₁ G f ∘′ α .η x))
```
-->

## Fibre Categories

The fibre category of the fibration of diagrams are equivalent to
functor categories $[\cJ, \cE_x]$.

```agda
  Fibrewise-diagram : ∀ {x} → Functor Cat[ J , Fibre E x ] (Fibre (Diagrams J) x)
  Fibrewise-diagram .F₀ = Diagram→ConstL
  Fibrewise-diagram .F₁ = Diagram-nat→ConstL-natl
  Fibrewise-diagram .F-id = Nat-lift-pathp λ _ → refl
  Fibrewise-diagram .F-∘ _ _ = Nat-lift-pathp λ _ → sym (Regularity.reduce!)
```

Again, this isomorphism is *almost* definitional.

```agda
  Fibrewise-diagram-is-iso : ∀ {x} → is-precat-iso (Fibrewise-diagram {x})
  Fibrewise-diagram-is-iso .is-precat-iso.has-is-ff =
    is-iso→is-equiv $ iso
      (ConstL-natl→Diagram-nat)
      (λ α' → Nat-lift-pathp (λ _ → refl))
      (λ α → Nat-path (λ _ → refl))
  Fibrewise-diagram-is-iso .is-precat-iso.has-is-iso =
    is-iso→is-equiv $ iso
      ConstL→Diagram
      (λ F' → Lifting-pathp E refl (λ _ → refl) (λ _ → refl))
      (λ F → Functor-path (λ _ → refl) (λ _ → refl))
```
