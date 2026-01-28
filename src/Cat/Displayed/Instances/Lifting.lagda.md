<!--
```agda
open import Cat.Displayed.Cartesian
open import Cat.Functor.Equivalence
open import Cat.Instances.Functor
open import Cat.Displayed.Total
open import Cat.Functor.Compose
open import Cat.Displayed.Base
open import Cat.Prelude

import Cat.Displayed.Reasoning
import Cat.Reasoning
```
-->

```agda
module Cat.Displayed.Instances.Lifting where
```

<!--
```agda
open Functor
open _=>_
open ∫Hom
```
-->

# Liftings

A category $\cE$ [[displayed over|displayed category]] $\cB$ contains
the same data as a functor into $\cB$, just packaged in a way that makes
it easier to talk about lifting properties. If we take this perspective,
we can start considering diagrams of functors. In particular, we can
consider lifts of functors $F : \cJ \to \cB$, as in the following
diagram:

~~~{.quiver}
\begin{tikzcd}
  \cJ && \cE \\
  \\
  && \cB
  \arrow["\pi", lies over, from=1-3, to=3-3]
  \arrow["F"', from=1-1, to=3-3]
  \arrow[dashed, from=1-1, to=1-3]
\end{tikzcd}
~~~

If we unfold this in terms of displayed categories, such a lifting $L :
\cJ \to \cE$ would give a $\cJ$-shaped diagram in $\cE$ *lying over* a
corresponding diagram in $\cB$.

<!--
```agda
module _
  {o ℓ o' ℓ' oj ℓj}
  {B : Precategory o ℓ}
  {J : Precategory oj ℓj}
  (E : Displayed B o' ℓ')
  where
  private module J = Precategory J

  open Cat.Displayed.Reasoning E
  open Cat.Reasoning B
```
-->

```agda
  record Lifting (F : Functor J B) : Type (o' ⊔ ℓ' ⊔ oj ⊔ ℓj) where
    no-eta-equality
    field
      F₀'   : (j : J.Ob) → Ob[ F .F₀ j ]
      F₁'   : ∀ {i j} → (f : J.Hom i j) → Hom[ F .F₁ f ] (F₀' i) (F₀' j)

      F-id' : ∀ {j} → F₁' (J.id {j}) ≡[ F .F-id ] id'
      F-∘'  : ∀ {i j k} (f : J.Hom j k) (g : J.Hom i j)
            → F₁' (f J.∘ g) ≡[ F .F-∘ f g ] F₁' f ∘' F₁' g

  open Lifting
```

<!--
```agda
  Lifting-pathp
    : {F G : Functor J B} {F' : Lifting F} {G' : Lifting G}
    → (p : F ≡ G)
    → (q : ∀ x → PathP (λ i → Ob[ p i .F₀ x ]) (F' .F₀' x) (G' .F₀' x))
    → (∀ {x y} → (f : J.Hom x y)
       → PathP (λ i → Hom[ p i .F₁ f ] (q x i) (q y i)) (F' .F₁' f) (G' .F₁' f))
    → PathP (λ i → Lifting (p i)) F' G'
  Lifting-pathp p q r i .F₀' x = q x i
  Lifting-pathp p q r i .F₁' f = r f i
  Lifting-pathp {F' = F'} {G' = G'} p q r i .F-id' {x} =
    is-set→squarep (λ i j → Hom[ (p i .F-id j) ]-set (q x i) (q x i))
      (r J.id)
      (F' .F-id')
      (G' .F-id')
      (λ _ → id') i
  Lifting-pathp {F' = F'} {G' = G'} p q r i .F-∘' {x} {y} {z} f g =
    is-set→squarep (λ i j → Hom[ p i .F-∘ f g j ]-set (q x i) (q z i))
      (r (f J.∘ g))
      (F' .F-∘' f g)
      (G' .F-∘' f g)
      (λ j → r f j ∘' r g j) i
```
-->

Liftings of a functor $F : \cJ \to \cB$ yield functors from $\cJ$ to the
[[total category]] of $\cE$.

```agda
  Lifting→Functor : ∀ {F : Functor J B} → Lifting F → Functor J (∫ E)
  Lifting→Functor {F} F' .F₀ j = F .F₀ j , F' .F₀' j
  Lifting→Functor {F} F' .F₁ f = ∫hom (F .F₁ f) (F' .F₁' f)
  Lifting→Functor {F} F' .F-id = ∫Hom-path E (F .F-id) (F' .F-id')
  Lifting→Functor {F} F' .F-∘ f g = ∫Hom-path E (F .F-∘ f g) (F' .F-∘' f g)
```

Furthermore, such liftings commute *extremely strictly*. Not only are
the two functors equal, the action on objects and morphisms are
*definitionally* equal! This highlights the utility of the theory
of displayed categories; by reorganizing our data, we can talk about a
higher level of strictness than usual.

```agda
  Lifting-is-lifting
    : ∀ {F : Functor J B} → (F' : Lifting F)
    → F ≡ (πᶠ E F∘ Lifting→Functor F')
  Lifting-is-lifting F' = Functor-path (λ _ → refl) (λ f → refl)

  Lifting-nat-iso
    : ∀ {F : Functor J B} → (F' : Lifting F)
    → F ≅ⁿ πᶠ E F∘ Lifting→Functor F'
  Lifting-nat-iso F' = to-natural-iso ni where
    open make-natural-iso

    ni : make-natural-iso _ _
    ni .eta _ = id
    ni .inv _ = id
    ni .eta∘inv _ = idl _
    ni .inv∘eta _ = idl _
    ni .natural _ _ _ = id-comm
```

## Natural transformations between liftings

As liftings are a reorganization of functors, it is reasonable to expect
that we can express natural transformations between these. Fix functors
$F, G : \cJ \to \cB$, and let $F', G'$ be their liftings along $\pi :
\cE \liesover \cB$. Furthermore, let $\alpha : F \to G$ be a natural
transformation. A **natural transformation of liftings** between $F'$
and $G'$ over $\alpha$ is given by a family of morphisms $\eta_{j}$
between $F'(j)$ and $G'(j)$.

<!--
```agda
module _ {o ℓ o' ℓ' oj ℓj} {B : Precategory o ℓ} {J : Precategory oj ℓj} {E : Displayed B o' ℓ'} where
  private module J = Precategory J

  open Cat.Displayed.Reasoning E
  open Cat.Reasoning B
  open Lifting
```
-->

```agda
  record _=[_]=>l_
    {F G : Functor J B}
    (F' : Lifting E F) (α : F => G) (G' : Lifting E G)
    : Type (ℓ' ⊔ oj ⊔ ℓj) where
    no-eta-equality

    field
      η' : ∀ (j) → Hom[ α .η j ] (F' .F₀' j) (G' .F₀' j)

      is-natural' : ∀ (i j : J.Ob) (f : J.Hom i j)
                  → η' j ∘' F' .F₁' f ≡[ α .is-natural i j f ] G' .F₁' f  ∘' η' i
```

<!--
```agda
  open _=[_]=>l_

  Nat-lift-pathp
    : ∀ {F G : Functor J B} {F' : Lifting E F} {G' : Lifting E G}
    → {α : F => G} {β : F => G} {α' : F' =[ α ]=>l G'} {β' : F' =[ β ]=>l G'}
    → {p : α ≡ β}
    → (∀ j → α' .η' j ≡[ p ηₚ j ] β' .η' j)
    → PathP (λ i → F' =[ p i ]=>l G') α' β'
  Nat-lift-pathp q i .η' x = q x i
  Nat-lift-pathp {F' = F'} {G'} {α' = α'} {β'} {p = p} q i .is-natural' x y f =
    is-set→squarep (λ i j → Hom[ p i .is-natural x y f j ]-set _ _)
      (λ j → q y j ∘' F' .F₁' f)
      (α' .is-natural' x y f)
      (β' .is-natural' x y f)
      (λ j → G' .F₁' f ∘' q x j) i

  private unquoteDecl eqv = declare-record-iso eqv (quote _=[_]=>l_)

  instance
    H-Level-Nat-Lift
      : ∀ {F G : Functor J B} {F' : Lifting E F} {G' : Lifting E G} {α : F => G} {n}
      → H-Level (F' =[ α ]=>l G') (2 + n)
    H-Level-Nat-Lift = basic-instance 2 $ Iso→is-hlevel! 2 eqv
```
-->

Diagrammatically, the situation is as follows:

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
  Nat-lift→Nat
    : ∀ {F G : Functor J B} {F' : Lifting E F} {G' : Lifting E G}
    → {α : F => G} → F' =[ α ]=>l G' → Lifting→Functor E F' => Lifting→Functor E G'
  Nat-lift→Nat {α = α} α' .η x .fst = α .η x
  Nat-lift→Nat {α = α} α' .η x .snd = α' .η' x
  Nat-lift→Nat {α = α} α' .is-natural x y f =
    ∫Hom-path E (α .is-natural x y f) (α' .is-natural' x y f)
```

As liftings are definitional, any natural transformation $F \to G$ is
also a natural transformation $\pi \circ F' \to \pi \circ G'$; showing
this requires repacking some data due to the lack of some $\eta$-rules.

```agda
  Nat→Nat-lift
    : ∀ {F G : Functor J B} (F' : Lifting E F) (G' : Lifting E G)
    → F => G → πᶠ E F∘ Lifting→Functor E F' => πᶠ E F∘ Lifting→Functor E G'
  Nat→Nat-lift F' G' α .η          = α .η
  Nat→Nat-lift F' G' α .is-natural = α .is-natural
```

This allows us to characterize natural transformations of liftings: they
are precisely the natural transformations that *definitionally* lie over
their bases.

```agda
  Nat-lift-is-lifting
    : ∀ {F G : Functor J B} {F' : Lifting E F} {G' : Lifting E G}
    → {α : F => G} → (α' : F' =[ α ]=>l G')
    → πᶠ E ▸ Nat-lift→Nat α' ≡ Nat→Nat-lift F' G' α
  Nat-lift-is-lifting α' = ext λ _ → refl
```

The identity natural transformation is easy to define, as is vertical
composition.

```agda
  idntl : ∀ {F : Functor J B} {F' : Lifting E F} → F' =[ idnt ]=>l F'
  idntl .η' j = id'
  idntl .is-natural' i j f = cast[] $ idl' _ ∙[] symP (idr' _)

  _∘ntl_
    : ∀ {F G H : Functor J B} {F' : Lifting E F} {G' : Lifting E G} {H' : Lifting E H}
    → {α : G => H} {β : F => G}
    → G' =[ α ]=>l H' → F' =[ β ]=>l G' → F' =[ α ∘nt β ]=>l H'
  _∘ntl_ α' β' .η' j = α' .η' j ∘' β' .η' j
  _∘ntl_  {F' = F'} {G'} {H'} α' β' .is-natural' i j f' = begin
    (α' .η' j ∘' β' .η' j) ∘' F' .F₁' f' ≡[]⟨ pullr[] _ (β' .is-natural' i j f') ⟩
    α' .η' j ∘' G' .F₁' f' ∘' β' .η' i   ≡[]⟨ extendl[] _ (α' .is-natural' i j f') ⟩
    H' .F₁' f' ∘' α' .η' i ∘' β' .η' i   ∎[]
```

## The fibration of liftings

The liftings of functors $\cJ \to \cB$ assemble into a displayed
category over the functor category $[\cJ, \cB]$. We shall denote this
category $\cE^{\cJ}$, as it is the displayed analog of the fibration
$\pi \circ - : \cE^{\cJ} \liesover \cB^{\cJ}$, where $\pi : \cE
\liesover \cB$ is a fibration.

<!--
```agda
module _
  {o ℓ o' ℓ' oj ℓj}
  {B : Precategory o ℓ}
  (E : Displayed B o' ℓ')
  (J : Precategory oj ℓj)
  where
  private module J = Precategory J

  open Cat.Displayed.Reasoning E
  open Cat.Reasoning B
  open Lifting
  open _=[_]=>l_
```
-->

```agda
  Liftings : Displayed Cat[ J , B ] (o' ⊔ ℓ' ⊔ oj ⊔ ℓj) (ℓ' ⊔ oj ⊔ ℓj)
  Liftings .Displayed.Ob[_] = Lifting E
  Liftings .Displayed.Hom[_] α F' G' = F' =[ α ]=>l G'
  Liftings .Displayed.Hom[_]-set _ _ _ = hlevel 2
  Liftings .Displayed.id'  = idntl
  Liftings .Displayed._∘'_ = _∘ntl_
  Liftings .Displayed.idr' _ = Nat-lift-pathp (λ _ → idr' _)
  Liftings .Displayed.idl' _ = Nat-lift-pathp (λ _ → idl' _)
  Liftings .Displayed.assoc' _ _ _ = Nat-lift-pathp (λ _ → assoc' _ _ _)
```

<!--
```agda
  Liftings .Displayed.hom[_] p f .η' x = hom[ p ηₚ x ] (f .η' x)
  Liftings .Displayed.hom[_] p f .is-natural' i j g = to-pathp[] $
    smashl _ _
    ∙ ap hom[] (from-pathp[]⁻ (f .is-natural'  i j g))
    ∙ hom[]-∙ _ _
    ∙ reindex _ _
    ∙ sym (whisker-r _)
  Liftings .Displayed.coh[_] p f = Nat-lift-pathp λ _ → coh[ p ηₚ _ ] (f .η' _)
```
-->

If a natural transformation of liftings is pointwise cartesian, then
it is cartesian.

```agda
  pointwise-cartesian→Liftings-cartesian
    : ∀ {F G : Functor J B} {F' : Lifting E F} {G' : Lifting E G}
    → {α : F => G} {α' : F' =[ α ]=>l G'}
    → (∀ x → is-cartesian E (α .η x) (α' .η' x))
    → is-cartesian Liftings α α'
  pointwise-cartesian→Liftings-cartesian {α = α} {α' = α'} pointwise = cart where
    module pointwise x = is-cartesian (pointwise x)

    cart : is-cartesian Liftings α α'
    cart .is-cartesian.universal β γ' .η' x =
      pointwise.universal x (β .η x) (γ' .η' x)
    cart .is-cartesian.universal β γ' .is-natural' x y f =
      pointwise.uniquep₂ _ _ _ _ _ _
        (pulll[] _ (pointwise.commutes _ _ _) ∙[] γ' .is-natural' _ _ _)
        (pulll[] _ (α' .is-natural' x y f)
        ∙[] pullr[] _ (pointwise.commutes _ _ _))
    cart .is-cartesian.commutes β γ' =
      Nat-lift-pathp (λ _ → pointwise.commutes _ _ _)
    cart .is-cartesian.unique γ' p =
      Nat-lift-pathp (λ x → pointwise.unique _ _ λ i → p i .η' x)
```


When $\cE$ is a fibration, then so is the displayed category of liftings.

```agda
  Liftings-fibration
    : (fib : Cartesian-fibration E)
    → Cartesian-fibration Liftings
  Liftings-fibration fib {F} {G} α G' = α-lift where
    module F = Functor F
    module G = Functor G

    open Cartesian-fibration E fib
    open Lifting
    open _=[_]=>l_
```

We begin by constructing the lifting over $F$; we can do this by
reindexing $G'$ pointwise.

```agda
    G'* : Lifting E F
    G'* .F₀' j = (α .η j) ^* (G' .F₀' j)
    G'* .F₁' f =
      π*.universal _
        (hom[ α .is-natural _ _ f ]⁻ (G' .F₁' f ∘' π* _ _))
```

<details>
<summary>The functoriality proofs are a bit gnarly, so we leave them in this `<details>` block.
</summary>

```agda
    G'* .F-id' = symP $ π*.uniquep _ _ _ _ $ begin
      π* _ _ ∘' id'          ≡[]⟨ idr' _ ⟩
      π* _ _                 ≡[]⟨ symP (idl' _) ⟩
      id' ∘' π* _ _          ≡[]⟨ (λ i → G' .F-id' (~ i) ∘' π* (α .η _) (G' .F₀' _)) ⟩
      G' .F₁' J.id ∘' π* _ _ ∎[]

    G'* .F-∘' f g = symP $ π*.uniquep _ _ _ _ $ begin
      π* _ _ ∘' G'* .F₁' f ∘' G'* .F₁' g        ≡[]⟨ pulll[] _ (π*.commutes _ _) ⟩
      hom[] (G' .F₁' f ∘' π* _ _) ∘' G'* .F₁' g ≡[ ap (_∘ F.F₁ g) (α .is-natural _ _ _) ]⟨ to-pathp[]⁻ (whisker-l (sym (α .is-natural _ _ _))) ⟩
      (G' .F₁' f ∘' π* _ _) ∘' G'* .F₁' g       ≡[]⟨ pullr[] _ (π*.commutes _ _) ⟩
      G' .F₁' f ∘' hom[] (G' .F₁' g ∘' π* _ _)  ≡[ ap (G.F₁ f ∘_) (α .is-natural _ _ _) ]⟨ to-pathp[]⁻ (whisker-r (sym (α .is-natural _ _ _))) ⟩
      G' .F₁' f ∘' (G' .F₁' g ∘' π* _ _)        ≡[]⟨ pulll[] _ (symP (G' .F-∘' f g)) ⟩
      G' .F₁' (f J.∘ g) ∘' π* _ _               ∎[]
```

</details>

As we have constructed the lift of $G$ via reindexing, we can use
the existing cartesian lifts to build the lift of $\alpha$. This also
implies that our natural transformation is cartesian.

```agda
    α'* : G'* =[ α ]=>l G'
    α'* .η' x = π* (α .η x) (G' .F₀' x)
    α'* .is-natural' x y f = π*.commutesp _ _

    α-lift : Cartesian-lift Liftings α G'
    α-lift .Cartesian-lift.x' = G'*
    α-lift .Cartesian-lift.lifting = α'*
    α-lift .Cartesian-lift.cartesian = pointwise-cartesian→Liftings-cartesian λ x →
      π*.cartesian
```

## Total category

As noted earlier, the total category of $\cE^{\cJ}$ *is* the functor
category $[\cJ, \int \cE]$. First, we shall need a heaping pile of
repackaging lemmas.

```agda
  ∫Functor→Lifting         : (F : Functor J (∫ E)) → Lifting E (πᶠ E F∘ F)
  Functor+Lifting→∫Functor : (F : Functor J B) → Lifting E F → Functor J (∫ E)

  ∫Nat→Nat : ∀ {F G : Functor J (∫ E)} → F => G → πᶠ E F∘ F => πᶠ E F∘ G
  Nat+Nat-lift→∫Nat
    : ∀ {F G : Functor J (∫ E)}
    → (α : πᶠ E F∘ F => πᶠ E F∘ G)
    → (α' : ∫Functor→Lifting F =[ α ]=>l ∫Functor→Lifting G)
    → F => G

  ∫Nat→Nat-lift
    : ∀ {F G : Functor J (∫ E)} → (α : F => G)
    → ∫Functor→Lifting F =[ ∫Nat→Nat α ]=>l ∫Functor→Lifting G
```

Since none of these constructions have deeper mathematical content than
their types, we omit the definitions from the page entirely.

<!--
```agda
  ∫Functor→Lifting F .F₀' j = F .F₀ j .snd
  ∫Functor→Lifting F .F₁' f = F .F₁ f .snd
  ∫Functor→Lifting F .F-id' = cast[] (ap snd (F .F-id))
  ∫Functor→Lifting F .F-∘' f g = cast[] (ap snd (F .F-∘ f g))

  Functor+Lifting→∫Functor F F' .F₀ x .fst = F .F₀ x
  Functor+Lifting→∫Functor F F' .F₀ x .snd = F' .F₀' x
  Functor+Lifting→∫Functor F F' .F₁ f .fst = F .F₁ f
  Functor+Lifting→∫Functor F F' .F₁ f .snd = F' .F₁' f
  Functor+Lifting→∫Functor F F' .F-id =
    ∫Hom-path E (F .F-id) (F' .F-id')
  Functor+Lifting→∫Functor F F' .F-∘ f g =
    ∫Hom-path E (F .F-∘ f g) (F' .F-∘' f g)

  ∫Nat→Nat α .η x = α .η x .fst
  ∫Nat→Nat α .is-natural x y f = ap fst (α .is-natural x y f)

  Nat+Nat-lift→∫Nat α α' .η x .fst = α .η x
  Nat+Nat-lift→∫Nat α α' .η x .snd = α' .η' x
  Nat+Nat-lift→∫Nat α α' .is-natural x y f =
    ∫Hom-path E (α .is-natural x y f) (α' .is-natural' x y f)

  ∫Nat→Nat-lift α .η' x = α .η x .snd
  ∫Nat→Nat-lift α .is-natural' x y f = ap snd (α .is-natural x y f)
```
-->

Using these repackagings, we can define the promised functor from $[\cJ,
\int \cE]$ into the total category of the fibration of liftings.

```agda
  Functors→Liftings : Functor Cat[ J , ∫ E ] (∫ Liftings)
  Functors→Liftings .F₀ F .fst = πᶠ E F∘ F
  Functors→Liftings .F₀ F .snd = ∫Functor→Lifting F

  Functors→Liftings .F₁ α .fst = ∫Nat→Nat α
  Functors→Liftings .F₁ α .snd = ∫Nat→Nat-lift α

  Functors→Liftings .F-id = ∫Hom-path Liftings (ext λ _ → refl)
    (Nat-lift-pathp (λ _ → refl))
  Functors→Liftings .F-∘ f g = ∫Hom-path Liftings (ext (λ _ → refl))
    (Nat-lift-pathp (λ _ → refl))
```

This functor has a remarkably strict inverse, regardless of univalence
of the fibrations and/or categories involved. It's almost definitionally
an isomorphism: because of our lack of $\eta$-laws, we must explicitly
appeal to some extensionality lemmas.

```agda
  Functors→Liftings-is-iso : is-precat-iso Functors→Liftings
  Functors→Liftings-is-iso .is-precat-iso.has-is-ff = is-iso→is-equiv $ iso
    (λ α → Nat+Nat-lift→∫Nat (α .fst) (α .snd))
    (λ _ → ∫Hom-path Liftings
      (ext            λ _ → refl)
      (Nat-lift-pathp λ _ → refl))
    (λ _ → ext λ _ → ∫Hom-path E refl refl)
  Functors→Liftings-is-iso .is-precat-iso.has-is-iso = is-iso→is-equiv $ iso
    (λ F → Functor+Lifting→∫Functor (F .fst) (F .snd))
    (λ _ → Functor-path (λ _ → refl) (λ _ → refl) ,ₚ
      Lifting-pathp E _ (λ _ → refl) (λ _ → refl))
    (λ _ → Functor-path (λ _ → refl ,ₚ refl) λ _ → refl)
```
