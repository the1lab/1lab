```agda
open import Cat.Displayed.Base
open import Cat.Displayed.Cartesian
open import Cat.Displayed.Total

open import Cat.Instances.Functor
open import Cat.Instances.Functor.Compose
open import Cat.Prelude

import Cat.Reasoning
import Cat.Displayed.Reasoning
import Cat.Functor.Reasoning

module Cat.Displayed.Instances.Lifting
  {o ℓ o' ℓ'}
  {B : Precategory o ℓ}
  (E : Displayed B o' ℓ')
  where

open Cat.Reasoning B
open Displayed E
open Cat.Displayed.Reasoning E

open Functor
open _=>_
open Total-hom
```

# Liftings

A category $\cE$ displayed over $\cB$ contains the same data as a functor
into $\cB$, just packaged in a way that makes it easier to talk about
lifting properties. If we take this perspective, we can start considering
diagrams of functors. In particular, we can consider lifts of a functor
$F : \cJ \to \cB$, as in the following diagram:


~~~{.quiver}
\begin{tikzcd}
  \cJ && \cE \\
  \\
  && \cB
  \arrow["\pi", from=1-3, to=3-3]
  \arrow["F"', from=1-1, to=3-3]
  \arrow[dashed, from=1-1, to=1-3]
\end{tikzcd}
~~~

If we unfold this in terms of displayed categories, such a lifting
$L : \cJ \to \cE$ would give a diagram in $\cE$ *above* a diagram in
$\cB$.

<!--
```agda
module _ {oj ℓj} {J : Precategory oj ℓj} where
  private module J = Precategory J
```
-->

```agda
  record Lifting (F : Functor J B) : Type (o' ⊔ ℓ' ⊔ oj ⊔ ℓj) where
    no-eta-equality
    field
      F₀′ : (j : J.Ob) → Ob[ F .F₀ j ]
      F₁′ : ∀ {i j} → (f : J.Hom i j) → Hom[ F .F₁ f ] (F₀′ i) (F₀′ j)
      F-id′ : ∀ {j} → F₁′ (J.id {j}) ≡[ F .F-id ] id′
      F-∘′ : ∀ {i j k} (f : J.Hom j k) (g : J.Hom i j)
           → F₁′ (f J.∘ g) ≡[ F .F-∘ f g ] F₁′ f ∘′ F₁′ g

  open Lifting
```

Liftings of a functor $F : \cJ \to \cB$ yield functors from $\cJ$ to the
total category of $\cE$.

```agda
  Lifting→Functor : ∀ {F : Functor J B} → Lifting F → Functor J (∫ E)
  Lifting→Functor {F} F' .F₀ j = F .F₀ j , F' .F₀′ j
  Lifting→Functor {F} F' .F₁ f = total-hom (F .F₁ f) (F' .F₁′ f)
  Lifting→Functor {F} F' .F-id = total-hom-path E (F .F-id) (F' .F-id′)
  Lifting→Functor {F} F' .F-∘ f g = total-hom-path E (F .F-∘ f g) (F' .F-∘′ f g)
```

Furthermore, such liftings commute *extremely strictly*. Not only are
the two functors equal, the action on objects and morphisms are
*definitionally* equal! This highlights the utility of the theory
of displayed categories; by reorganizing our data, we can talk about
a higher level of strictness than usual.

```agda
  Lifting-is-lifting
    : ∀ {F : Functor J B} → (F' : Lifting F)
    → F ≡ (πᶠ E F∘ Lifting→Functor F')
  Lifting-is-lifting F' = Functor-path (λ _ → refl) (λ f → refl)

  Lifting-nat-iso
    : ∀ {F : Functor J B} → (F' : Lifting F)
    → natural-iso F (πᶠ E F∘ Lifting→Functor F')
  Lifting-nat-iso F' = to-natural-iso ni where
    open make-natural-iso

    ni : make-natural-iso _ _
    ni .eta _ = id
    ni .inv _ = id
    ni .eta∘inv _ = idl _
    ni .inv∘eta _ = idl _
    ni .natural _ _ _ = id-comm
```

## Natural Transformations between Liftings

As liftings are a reorganization of functors, it is reasonable to expect
that we have some notion of natural transformation. Let
$F, G : \cJ \to \cB$, and $F', G'$ be liftings of $F$ and $G$, respectively.
Furthermore, let $\alpha : F \to G$ be a natural transformation.
A *natural transformation of liftings* between $F'$ and $G'$ over
$\alpha$ is given by a family of morphisms $\eta_{j}$ between $F'(j)$ and
$G'(j)$.

```agda
  record _=[_]=>l_
    {F G : Functor J B}
    (F' : Lifting F) (α : F => G) (G' : Lifting G)
    : Type (ℓ' ⊔ oj ⊔ ℓj) where
    no-eta-equality
    field
      η′ : ∀ (j) → Hom[ α .η j ] (F' .F₀′ j) (G' .F₀′ j)
      is-natural′ : ∀ (i j : J.Ob) (f : J.Hom i j)
                  → η′ j ∘′ F' .F₁′ f ≡[ α .is-natural i j f ] G' .F₁′ f  ∘′ η′ i

  open _=[_]=>l_
```

<!--
```agda
  NatLift-pathp
    : ∀ {F G : Functor J B} {F' : Lifting F} {G' : Lifting G}
    → {α : F => G} {β : F => G} {α' : F' =[ α ]=>l G'} {β' : F' =[ β ]=>l G'}
    → {p : α ≡ β}
    → (∀ j → α' .η′ j ≡[ p ηₚ j ] β' .η′ j)
    → PathP (λ i → F' =[ p i ]=>l G') α' β'
  NatLift-pathp q i .η′ x = q x i
  NatLift-pathp {F' = F'} {G'} {α' = α'} {β'} {p = p} q i .is-natural′ x y f =
    is-set→squarep (λ i j → Hom[ p i .is-natural x y f j ]-set _ _)
      (λ j → q y j ∘′ F' .F₁′ f)
      (α' .is-natural′ x y f)
      (β' .is-natural′ x y f)
      (λ j → G' .F₁′ f ∘′ q x j) i

  private unquoteDecl eqv = declare-record-iso eqv (quote _=[_]=>l_)

  NatLift-is-set
    : ∀ {F G : Functor J B} {F' : Lifting F} {G' : Lifting G}
    → {α : F => G} → is-set (F' =[ α ]=>l G')
  NatLift-is-set =
    Iso→is-hlevel 2 eqv $
    Σ-is-hlevel 2 (Π-is-hlevel 2 λ _ → Hom[ _ ]-set _ _) λ _ →
    Π-is-hlevel 2 λ _ → Π-is-hlevel 2 λ _ → Π-is-hlevel 2 λ _ →
    PathP-is-hlevel 2 (Hom[ _ ]-set _ _)
```
-->

Diagramatically, the situation is as follows:

~~~{.quiver}
\begin{tikzcd}
  \cJ &&& \cE \\
  \\
  \\
  &&& \cB
  \arrow["\pi", from=1-4, to=4-4]
  \arrow[""{name=0, anchor=center, inner sep=0}, "F"{description}, curve={height=12pt}, from=1-1, to=4-4]
  \arrow[""{name=1, anchor=center, inner sep=0}, "G"{description}, curve={height=-12pt}, from=1-1, to=4-4]
  \arrow[""{name=2, anchor=center, inner sep=0}, "{G'}"{description}, curve={height=-12pt}, from=1-1, to=1-4]
  \arrow[""{name=3, anchor=center, inner sep=0}, "{F'}"{description}, curve={height=12pt}, from=1-1, to=1-4]
  \arrow["\alpha", shorten <=4pt, shorten >=4pt, Rightarrow, from=0, to=1]
  \arrow["{\alpha'}", shorten <=3pt, shorten >=3pt, Rightarrow, from=3, to=2]
\end{tikzcd}
~~~

As expected natural transformations of liftings yield natural
transformations between the associated functors.

```agda
  NatLift→Nat
    : ∀ {F G : Functor J B} {F' : Lifting F} {G' : Lifting G}
    → {α : F => G} → F' =[ α ]=>l G' → Lifting→Functor F' => Lifting→Functor G'
  NatLift→Nat {α = α} α' .η x .hom = α .η x
  NatLift→Nat {α = α} α' .η x .preserves = α' .η′ x
  NatLift→Nat {α = α} α' .is-natural x y f =
    total-hom-path E (α .is-natural x y f) (α' .is-natural′ x y f)
```

As liftings are definitional, any natural transformation $F \to G$ is also
a natural transformation $\pi \circ F' \to \pi \circ G'$; showing this
requires repacking some data due to the lack of some $\eta$-rules.

```agda
  Nat→NatLift
    : ∀ {F G : Functor J B} (F' : Lifting F) (G' : Lifting G)
    → F => G → πᶠ E F∘ Lifting→Functor F' => πᶠ E F∘ Lifting→Functor G'
  Nat→NatLift F' G' α .η = α .η
  Nat→NatLift F' G' α .is-natural = α .is-natural
```

This allows us to characterize natural transformations of liftings:
they are precisely the natural transformations that *definitionally*
lie over their bases.

```agda
  NatLift-is-lifting
    : ∀ {F G : Functor J B} {F' : Lifting F} {G' : Lifting G}
    → {α : F => G} → (α' : F' =[ α ]=>l G')
    → πᶠ E ▸ NatLift→Nat α' ≡ Nat→NatLift F' G' α
  NatLift-is-lifting α' = Nat-path (λ _ → refl)
```

The identity natural transformation is easy to define, as is vertical
composition.

```agda
  idntl : ∀ {F : Functor J B} {F' : Lifting F} → F' =[ idnt ]=>l F'
  idntl .η′ j = id′
  idntl .is-natural′ i j f = idl′ _ ∙[] symP (idr′ _)

  _∘ntl_
    : ∀ {F G H : Functor J B} {F' : Lifting F} {G' : Lifting G} {H' : Lifting H}
    → {α : G => H} {β : F => G}
    → G' =[ α ]=>l H' → F' =[ β ]=>l G' → F' =[ α ∘nt β ]=>l H'
  _∘ntl_ α' β' .η′ j = α' .η′ j ∘′ β' .η′ j
  _∘ntl_  {F' = F'} {G'} {H'} α' β' .is-natural′ i j f' = 
    (α' .η′ j ∘′ β' .η′ j) ∘′ F' .F₁′ f' ≡[]⟨ pullr[] _ (β' .is-natural′ i j f') ⟩
    α' .η′ j ∘′ G' .F₁′ f' ∘′ β' .η′ i   ≡[]⟨ extendl[] _ (α' .is-natural′ i j f') ⟩
    H' .F₁′ f' ∘′ α' .η′ i ∘′ β' .η′ i   ∎
```

## The Fibration of Liftings

The liftings of functors $\cJ \to \cB$ assemble into a displayed category
over the functor category $[\cJ, \cB]$.

```agda
Liftings
  : ∀ {oj ℓj} (J : Precategory oj ℓj)
  → Displayed Cat[ J , B ] (o' ⊔ ℓ' ⊔ oj ⊔ ℓj) (ℓ' ⊔ oj ⊔ ℓj)
Liftings J = disp where
  module J = Precategory J

  disp : Displayed Cat[ J , B ] _ _
  disp .Displayed.Ob[_] = Lifting
  disp .Displayed.Hom[_] α F' G' = F' =[ α ]=>l G'
  disp .Displayed.Hom[_]-set _ _ _ = NatLift-is-set
  disp .Displayed.id′ = idntl
  disp .Displayed._∘′_ = _∘ntl_
  disp .Displayed.idr′ _ = NatLift-pathp (λ _ → idr′ _)
  disp .Displayed.idl′ _ = NatLift-pathp (λ _ → idl′ _)
  disp .Displayed.assoc′ _ _ _ = NatLift-pathp (λ _ → assoc′ _ _ _)
```

When $\cE$ is a fibration, then so is the displayed category of liftings.

```agda
Liftings-fibration
  : ∀ {oj ℓj}
  → (fib : Cartesian-fibration E)
  → (J : Precategory oj ℓj)
  → Cartesian-fibration (Liftings J)
Liftings-fibration fib J .Cartesian-fibration.has-lift {F} {G} α G' = cart-lift where
  module F = Cat.Functor.Reasoning F
  module G = Cat.Functor.Reasoning G
  module J = Precategory J
  open Cartesian-fibration fib
  open Lifting
  open _=[_]=>l_
```

We begin by constructing the lifting over $F$; we can do this by
reindexing $G'$ pointwise.

```agda
  G'* : Lifting F
  G'* .F₀′ j = has-lift.x′ (α .η j) (G' .F₀′ j)
  G'* .F₁′ f =
    has-lift.universal _ _ _
      (hom[ α .is-natural _ _ f ]⁻ (G' .F₁′ f ∘′ has-lift.lifting _ _))
  G'* .F-id′ =
    symP $ has-lift.uniquep _ _ _ (sym (F .F-id)) (α .is-natural _ _ _) id′ $
      has-lift.lifting _ _ ∘′ id′          ≡[]⟨ idr′ _ ⟩
      has-lift.lifting _ _                 ≡[]⟨ symP (idl′ _) ⟩
      id′ ∘′ has-lift.lifting _ _          ≡[]⟨ (λ i → G' .F-id′ (~ i) ∘′ has-lift.lifting (α .η _) (G' .F₀′ _)) ⟩
      G' .F₁′ J.id ∘′ has-lift.lifting _ _ ∎
  G'* .F-∘′ f g =
    symP $ has-lift.uniquep _ _ _
      (sym (F .F-∘ f g)) (α .is-natural _ _ _ ) (G'* .F₁′ f ∘′ G'* .F₁′ g) $
        has-lift.lifting _ _ ∘′ G'* .F₁′ f ∘′ G'* .F₁′ g        ≡[]⟨ pulll[] _ (has-lift.commutes _ _ _ _) ⟩
        hom[] (G' .F₁′ f ∘′ has-lift.lifting _ _) ∘′ G'* .F₁′ g ≡[ ap (_∘ F.F₁ g) (α .is-natural _ _ _) ]⟨ to-pathp⁻ (whisker-l (sym (α .is-natural _ _ _))) ⟩
        (G' .F₁′ f ∘′ has-lift.lifting _ _) ∘′ G'* .F₁′ g       ≡[]⟨ pullr[] _ (has-lift.commutes _ _ _ _) ⟩
        G' .F₁′ f ∘′ hom[] (G' .F₁′ g ∘′ has-lift.lifting _ _)  ≡[ ap (G.F₁ f ∘_) (α .is-natural _ _ _) ]⟨ to-pathp⁻ (whisker-r (sym (α .is-natural _ _ _))) ⟩
        G' .F₁′ f ∘′ (G' .F₁′ g ∘′ has-lift.lifting _ _)        ≡[]⟨ pulll[] _ (symP (G' .F-∘′ f g)) ⟩
        G' .F₁′ (f J.∘ g) ∘′ has-lift.lifting _ _               ∎
```

As we have constructed the lift of $G$ via reindexing, we can use
the existing cartesian lifts to build the lift of $\alpha$. This also
implies that our natural transformation is cartesian.

```agda
  α'* : G'* =[ α ]=>l G'
  α'* .η′ x = has-lift.lifting (α .η x) (G' .F₀′ x)
  α'* .is-natural′ x y f = has-lift.commutesp (α .η y) (G' .F₀′ y) _ _

  α'*-cartesian : is-cartesian (Liftings J) α α'*
  α'*-cartesian .is-cartesian.universal β γ' .η′ x =
    has-lift.universal (α .η x) (G' .F₀′ x) (β .η x) (γ' .η′ x)
  α'*-cartesian .is-cartesian.universal β γ' .is-natural′ x y f =
    has-lift.uniquep₂ _ _ _ (β .is-natural x y f) _ _ _
      (pulll[] _ (has-lift.commutes _ _ _ _) ∙[] γ' .is-natural′ _ _ _)
      (pulll[] _ (has-lift.commutes _ _ _ _)
       ∙[] to-pathp⁻ (whisker-l (sym (α .is-natural _ _ _)))
       ∙[ ap (_∘ β .η x) (α .is-natural _ _ _) ] pullr[] _ (has-lift.commutes _ _ _ _))
  α'*-cartesian .is-cartesian.commutes β γ' =
    NatLift-pathp (λ x → has-lift.commutes _ _ _ _)
  α'*-cartesian .is-cartesian.unique γ' p =
    NatLift-pathp λ x → has-lift.unique _ _ _ (λ i → p i .η′ x)

  cart-lift : Cartesian-lift (Liftings J) α G'
  cart-lift .Cartesian-lift.x′ = G'*
  cart-lift .Cartesian-lift.lifting = α'*
  cart-lift .Cartesian-lift.cartesian = α'*-cartesian
```
