```agda
open import Cat.Diagram.Initial
open import Cat.Instances.Comma
open import Cat.Prelude

import Cat.Functor.Reasoning as Func
import Cat.Reasoning

module Cat.Functor.Adjoint where
```

<!--
```agda
private variable
  o h : Level
  C D : Precategory o h

open Functor hiding (op)

adj-level : ∀ {o₁ h₁ o₂ h₂} (C : Precategory o₁ h₁) (D : Precategory o₂ h₂)
          → Level
adj-level {o₁ = o₁} {h₁} {o₂} {h₂} _ _ = o₁ ⊔ o₂ ⊔ h₁ ⊔ h₂
```
-->

# Adjoint functors

Category theory is, in general, the study of how things can be related.
For instance, structures at the level of sets (e.g. the collection of
natural numbers) are often interestingly related by propositions (i.e.
the proposition $x \le y$). Structures at the level of groupoids (e.g.
the collection of all sets) are interestingly related by sets (i.e. the
set of maps $x \to y$). Going further, we have structures at the level
of 2-groupoids, which could be given an interesting _category_ of
relations, etc.

A particularly important relationship is, of course, "sameness". Going
up the ladder of category number, we have equality at the (-1)-level,
isomorphism at the 0-level, and what's generally referred to as
"equivalence" at higher levels. It's often interesting to weaken these
relations, by making some components directed: This starts at the level
of categories, where "directing" an equivalence gives us the concept of
**adjunction**.

An _equivalence of categories_ between $\ca{C}$ and $\ca{D}$ is given by
a pair of functors $L : \ca{C} \leftrightarrows \ca{D} : R$, equipped
with natural _isomorphisms_ $\eta : \id{Id} \cong (R \circ L)$ (the
"unit") and $\eps : (L \circ R) \cong \id{Id}$ (the "counit"). We
still want the correspondence to be bidirectional, so we can't change
the types of $R$, $L$; What we _can_ do is weaken the natural
isomorphisms to natural _transformations_. The data of an **adjunction**
starts as such:

```agda
record _⊣_ (L : Functor C D) (R : Functor D C) : Type (adj-level C D) where
  private
    module C = Precategory C
    module D = Precategory D

  field
    unit   : Id => (R F∘ L)
    counit : (L F∘ R) => Id

  module unit = _=>_ unit
  module counit = _=>_ counit renaming (η to ε)
```

Unfortunately, the data that we have here is not particularly coherent.
The `unit`{.Agda} and `counit`{.Agda} let us introduce $R\circ L$ and
eliminate $L\circ R$ in a composition, which gives us two ways of mapping
$L \To L$. One is the identity, and the other is going through
the unit: $L \To L\circ R\circ L \To L$ (the situation
with $R$ is symmetric). We must impose further equations on the natural
transformations to make sure these match:

```agda
  field
    zig : ∀ {A} → counit.ε (F₀ L A) D.∘ F₁ L (unit.η A) ≡ D.id
    zag : ∀ {B} → F₁ R (counit.ε B) C.∘ unit.η (F₀ R B) ≡ C.id

infixr 15 _⊣_
```

These are called "triangle identities" because of the shape they have as
commutative diagrams:

<div class=mathpar>

~~~{.quiver}
\[\begin{tikzcd}
  R & RLR \\
  & R
  \arrow[from=1-1, to=2-2]
  \arrow["{\eta R}", from=1-1, to=1-2]
  \arrow["R\epsilon", from=1-2, to=2-2]
\end{tikzcd}\]
~~~

~~~{.quiver}
\[\begin{tikzcd}
  L & LRL \\
  & L
  \arrow[from=1-1, to=2-2]
  \arrow["L\eta", from=1-1, to=1-2]
  \arrow["{\epsilon L}", from=1-2, to=2-2]
\end{tikzcd}\]
~~~

</div>

# Universal morphisms

<!--
```agda
module _
  {o h o' h'}
  {C : Precategory o h}
  {D : Precategory o' h'}
  where

  private
    module C = Precategory C
    module D = Precategory D
```
-->

Another perspective on adjoint functors is given by finding "most
efficient solutions" to the "problem" posed by a functor. For instance,
the ([ff]) inclusion of [prosets] into [strict precategories] poses the
problem of turning a precategory into a proset. While this can't be done
in a 1:1 way (precategories are strictly more general than prosets), we
_can_ still ponder whether there is some "most efficient" way to turn a
category into a proset.

[ff]: Cat.Functor.Base.html#ff-functors
[prosets]: Cat.Thin.html#prosets
[strict precategories]: Cat.Instances.StrictCat.html#strict-precategories

While we can't directly consider maps from precategories to proset, we
_can_ consider maps from precategories to the inclusion of a proset; Let
us write $\ca{C}$ for a generic precategory, $\ca{P}$ for a generic
proset, and $U(\ca{P})$ for $\ca{P}$ considered as a precategory. Any
functor $\ca{C} \to U(\ca{P})$ can be seen as "a way to turn $\ca{C}$
into a proset", but not all of these can be the "most efficient" way. In
fact, there is a vast sea of uninteresting ways to turn a precategory
into a proset: turn them all into the [terminal] proset!

[terminal]: Cat.Diagram.Terminal.html

A "most efficient" solution, then, would be one through which all others
factor. A "universal" way of turning a strict precategory into a proset:
A **universal morphism** from $\ca{C}$ to $U$. The way we think about
universal morphisms (reusing the same variables) is as [initial objects]
in the [comma category] $\ca{C} \swarrow U$, where that category is
conceptualised as being "the category of maps from $\ca{C}$ to $U$".

[initial objects]: Cat.Diagram.Initial.html
[comma category]: Cat.Instances.Comma.html

```agda
  Universal-morphism : C.Ob → Functor D C → Type _
  Universal-morphism X R = Initial (X ↙ R)
```

Abstracting away, suppose that $R : D \to C$ has universal morphisms for
every object of $C$. To show the correspondence between these two ideas
of adjunction, we show that this assignment extends to a functor $L : C
\to D$, with $L \dashv R$ as defined above.

<!--
```agda
module _
  {o h o' h'}
  {C : Precategory o h}
  {D : Precategory o' h'}
  (R : Functor D C)
  (universal-map-for : ∀ c → Universal-morphism c R)
  where

  open Initial
  open ↓Hom using (β)
  open ↓Obj using (map)

  open Precategory

  private
    import Cat.Reasoning C as C
    import Cat.Reasoning D as D
    module R = Functor R
```
-->

## Defining the L

We first show that the assignment of universal morphisms restricts to a
functorial assignment $L : C \to D$. Recall that an object in $X
\swarrow R$ is given by a codomain $y$ and a map $X \to R(y)$. We define
$L_0(x)$ to be the codomain of the universal morphism:

```agda
  L₀ : C.Ob → D.Ob
  L₀ x = universal-map-for x .bot .↓Obj.y

  L₀′ : (c : C.Ob) → C.Hom c (R.₀ (L₀ c))
  L₀′ x = universal-map-for x .bot .map
```

Given an arrow $a \to b$ in $\ca{C}$, we can send it to a
uniquely-determined _object_ in $a \swarrow R$: We take the universal
arrow assigned to $b$ (an object of $b \swarrow R$), and precompose with
$a$. This object will then serve as the domain of the morphism part of
$L$, which is given by the unique assignment arrows out of the initial
object in $a \swarrow R$ (see `lift↓`{.Agda} below).

```agda
  private
    to-ob : ∀ {a b} → C.Hom a b → (a ↙ R) .Precategory.Ob
    to-ob {a} {b} h = record { map = L₀′ b C.∘ h }

    lift↓ : ∀ {x y} (g : C.Hom x y)
          → Precategory.Hom (x ↙ R) (universal-map-for x .bot) (to-ob g)
    lift↓ {x} {y} g = ¡ (universal-map-for x) {to-ob g}

  L₁ : ∀ {a b} → C.Hom a b → D.Hom (L₀ a) (L₀ b)
  L₁ {a} {b} x = lift↓ x .β
```

<details>
<summary>
It now suffices to show the functor identities hold for `L₁`{.Agda}.
They follow essentially from the uniqueness of maps out of an initial
object.
</summary>

```agda
  private abstract
    L-id : ∀ {a} → L₁ (C.id {a}) ≡ D.id {L₀ a}
    L-id {a} = ap β (¡-unique (universal-map-for a)
                      (record { sq = C.elimr refl
                                  ·· C.elimr refl
                                  ·· sym (C.eliml R.F-id) }))

    lemma : ∀ {x y z} (f : C.Hom y z) (g : C.Hom x y)
          → R.₁ (L₁ f D.∘ L₁ g) C.∘ (L₀′ x)
          ≡ to-ob (f C.∘ g) .map C.∘ C.id
    lemma {x} {y} {z} f g =
      R.₁ (lift↓ f .β D.∘ lift↓ g .β) C.∘ (L₀′ x)       ≡⟨ C.pushl (R.F-∘ _ _) ⟩
      R.₁ (lift↓ f .β) C.∘ R.₁ (lift↓ g .β) C.∘ (L₀′ x) ≡⟨ ap (R.₁ (lift↓ f .β) C.∘_) (sym (lift↓ g .↓Hom.sq) ∙ C.idr _) ⟩
      R.₁ (lift↓ f .β) C.∘ L₀′ y C.∘ g                  ≡⟨ C.extendl (sym (lift↓ f .↓Hom.sq) ∙ C.idr _) ⟩
      L₀′ z C.∘ f C.∘ g                                 ≡˘⟨ C.idr _ ⟩
      to-ob (f C.∘ g) .map C.∘ C.id                     ∎

    L-∘ : ∀ {x y z} (f : C.Hom y z) (g : C.Hom x y)
        → L₁ (f C.∘ g) ≡ L₁ f D.∘ L₁ g
    L-∘ f g = ap β (¡-unique (universal-map-for _) (record { sq = sym (lemma f g) }))
```
</details>

That out of the way, we have our $L$ functor. We now have to show that
it defines a left adjoint to the $R$ we started with.

```agda
  universal-maps→L : Functor C D
  universal-maps→L .F₀ = L₀
  universal-maps→L .F₁ = L₁
  universal-maps→L .F-id = L-id
  universal-maps→L .F-∘ = L-∘
```

<!--
```agda
  open _⊣_
  open _=>_
```
-->

## Building the adjunction

We now prove that $L \dashv R$, which, recall, means giving natural
transformations $\eta : \id{Id} \To (R F\circ L)$ (the
_adjunction unit_) and $\eps : (L \circ R) \To \id{Id}$ (the
_adjunction counit_). We begin with the counit, since that's more
involved.

The construction begins by defining a function `mapd`{.Agda} which sends
each object of $\ca{C}$ to the initial object in $x \swarrow R$. Note
that this is the same as `L₀`{.Agda}, but returning the entire object
rather than a part of it.

```agda
  private
    mapd : ∀ (x : C.Ob) → Ob (x ↙ R)
    mapd x = universal-map-for x .bot
```

Now for an object $x : \ca{D}$, we have $R(x) : \ca{C}$, so by the
assumption that $R$ has a collection of universal objects, the comma
category $R(x) \swarrow R$ has an initial object; Let us write that
object as $(L(R(x)), !)$ --- recall that here, $! : R(x) \to RLR(x)$.

This means, in particular, that for any other object $(y, f)$ (with $y
\in \ca{D}$ and $f : R(x) \to R(y)$ in $\ca{C}$), there is a unique map
$\id{mapd}(x) \to (y, f)$, which breaks down as a map $\beta :
L(R(x)) \to y$ such that the square below commutes.

~~~{.quiver}
\[\begin{tikzcd}
  {R(x)} & {RLR(x)} \\
  & {R(y)}
  \arrow["{!}", from=1-1, to=1-2]
  \arrow["{R(\beta)}", from=1-2, to=2-2]
  \arrow["f"', from=1-1, to=2-2]
\end{tikzcd}\]
~~~

```agda
    ε : ∀ (x : D.Ob) → Hom (R.₀ x ↙ R) (mapd (R.₀ x)) _
    ε x = Initial.¡ (universal-map-for (R.₀ x)) {x = record { y = x ; map = C.id }}
```

The magic trick is that, if we pick $(x, \id{id})$ as the object of
$R(x)\swarrow R$ to map into, then $\beta$ in the diagram above must be
$LR(x) \to x$! We choose this map as our adjunction counit. A tedious
calculation shows that this assignment is natural, essentially because
$\beta$ is unique.

```agda
  universal-maps→L⊣R : universal-maps→L ⊣ R
  universal-maps→L⊣R .counit .η x = ε x .↓Hom.β
  universal-maps→L⊣R .counit .is-natural x y f =
    ap ↓Hom.β (
      ¡-unique₂ (universal-map-for (R.₀ x)) {record { map = R.₁ f }}
      (record { sq =
        R.₁ f C.∘ C.id                                          ≡⟨ C.idr _ ⟩
        R.₁ f                                                   ≡˘⟨ C.cancell (sym (ε y .↓Hom.sq) ∙ C.idr _) ⟩
        R.₁ (ε y .β) C.∘ _ C.∘ R.₁ f                            ≡˘⟨ ap₂ C._∘_ refl (sym (lift↓ (R.₁ f) .↓Hom.sq) ∙ C.idr _) ⟩
        R.₁ (ε y .β) C.∘ R.₁ (L₁ (R.₁ f)) C.∘ mapd (R.₀ x) .map ≡⟨ C.pulll (sym (R.F-∘ _ _)) ⟩
        R.₁ (ε y .β D.∘ L₁ (R.₁ f)) C.∘ mapd (R.₀ x) .map       ∎ })
      (record { sq =
        R.₁ f C.∘ C.id                               ≡˘⟨ ap (R.₁ f C.∘_) (sym (ε x .↓Hom.sq) ∙ C.idr _) ⟩
        R.₁ f C.∘ R.₁ (ε x .β) C.∘ mapd (R.₀ x) .map ≡⟨ C.pulll (sym (R.F-∘ _ _)) ⟩
        R.₁ (f D.∘ ε x .β) C.∘ mapd (R.₀ x) .map     ∎ }))
```

For the adjunction unit, the situation is a lot easier. Recall that we
_defined_ $L(x)$ on objects (`L₀`{.Agda}) to be the codomain part of the
initial object of $x \swarrow R$; The _map_ part of that object then
gives us a natural family of morphisms $x \to R(L(x))$. By definition.
It's so "by definition" that Agda can figure out the components by
itself:

```agda
  universal-maps→L⊣R .unit .η x              = _
  universal-maps→L⊣R .unit .is-natural x y f = sym (C.idr _) ∙ lift↓ f .↓Hom.sq
```

If you think back to the adjunction counit, you'll recall that it
satisfied a triangle that looks like the one below, and that the top map
(the map component of the initial object) is what we defined the
adjunction unit to be, so.. It's `zag`{.Agda}.

~~~{.quiver}
\[\begin{tikzcd}
  {R(x)} && {RLR(x)} \\
  \\
  && R(x)
  \arrow["{\id{id}}"', from=1-1, to=3-3]
  \arrow["{!}", from=1-1, to=1-3]
  \arrow["{R(\beta)}", from=1-3, to=3-3]
\end{tikzcd}\]
~~~

```agda
  universal-maps→L⊣R .zag {x} = sym (ε x .↓Hom.sq) ∙ C.idr _
```

The other triangle identity is slightly more annoying, but it works just
as well. It follows from the uniqueness of maps out of the initial
object:

```agda
  universal-maps→L⊣R .zig {x} =
    ap ↓Hom.β (
      ¡-unique₂ (universal-map-for x) {record { map = α }}
        (record { sq =
          α C.∘ C.id                     ≡⟨ C.idr _ ⟩
          α                              ≡˘⟨ C.cancell (sym (ε (L₀ x) .↓Hom.sq) ∙ C.idr _) ⟩
          R.₁ _ C.∘ _ C.∘ α              ≡˘⟨ C.pullr (sym (lift↓ α .↓Hom.sq) ∙ C.idr _) ⟩
          (R.₁ _ C.∘ R.₁ (F₁ L α)) C.∘ α ≡˘⟨ ap (C._∘ α) (R.F-∘ _ _) ⟩
          R.₁ (_ D.∘ F₁ L α) C.∘ α       ∎
        })
        (record { sq = C.id-comm ∙ ap (C._∘ _) (sym R.F-id) })
    )
    where α = L₀′ x
          L = universal-maps→L
```

## From an adjunction

To finish the correspondence, we show that any (left) adjoint functor $L
\dashv R$ defines a system of universal arrows $- \swarrow R$; This
means that, not only does a "universal way of solving $R$" _give_ a left
adjoint to $R$, it _is_ a left adjoint to $R$.

<!--
```agda
module _
  {L : Functor C D} {R : Functor D C}
  (adj : L ⊣ R)
  where

  private
    import Cat.Functor.Reasoning L as L
    import Cat.Functor.Reasoning R as R
    import Cat.Reasoning C as C
    import Cat.Reasoning D as D
    module adj = _⊣_ adj
```
-->

So, given an object $x \in \ca{C}$, we must find an object $y$ and a
universal map $x \to R(y)$. Recall that, in the previous section, we
constructed the left adjoint $L$'s action on objects by using our system
of universal arrows; Symetrically, in this section, we take the codomain
to be $y = L(x)$. We must then find an arrow $x \to RLx$, but this is
exactly the adjunction unit $\eta$!

```agda
  L⊣R→map-to-R : ∀ x → Precategory.Ob (x ↙ R)
  L⊣R→map-to-R x .↓Obj.x = tt
  L⊣R→map-to-R x .↓Obj.y = L.₀ x
  L⊣R→map-to-R x .↓Obj.map = adj.unit.η _
```

We must now show that the unit $\eta$ is universal among the pairs $(y,
f)$, with $f$ a map $x \to R(y)$. Recall that for our object $(Lx,
\eta)$ to be [initial], we must find an arrow $(y, f) \to (Lx, \eta)$,
and prove that this is the only possible such arrow; And that morphisms
in the comma category $x \swarrow R$ break down as maps $g : Lx \to y$ such
that the triangle below commutes:

[initial]: Cat.Diagram.Initial.html

~~~{.quiver}
\[\begin{tikzcd}
  x && RLx \\
  \\
  && Ry
  \arrow["f"', from=1-1, to=3-3]
  \arrow["\eta", from=1-1, to=1-3]
  \arrow["Rg", from=1-3, to=3-3]
\end{tikzcd}\]
~~~

We can actually read off the map $g$ pretty directly from the diagram:
It must be a map $Lx \to y$, but we've been given a map $LRx \to x$ (the
adjunction counit) and a map $x \to Ry$; We may then take our $g$ to be
the composite

$$
Lx \to LRy \to y
$$

```agda
  L⊣R→map-to-R-is-initial
    : ∀ x → is-initial (x ↙ R) (L⊣R→map-to-R x)
  L⊣R→map-to-R-is-initial x other-map .centre .↓Hom.α = tt
  L⊣R→map-to-R-is-initial x other-map .centre .↓Hom.β =
    adj.counit.ε _ D.∘ L.₁ (other-map .↓Obj.map)
  L⊣R→map-to-R-is-initial x other-map .centre .↓Hom.sq =
    sym (
      R.₁ (adj.counit.ε _ D.∘ L.₁ om.map) C.∘ adj.unit.η _       ≡⟨ ap₂ C._∘_ (R.F-∘ _ _) refl ∙ sym (C.assoc _ _ _) ⟩
      R.₁ (adj.counit.ε _) C.∘ R.₁ (L.₁ om.map) C.∘ adj.unit.η _ ≡˘⟨ C.refl⟩∘⟨ adj.unit.is-natural _ _ _ ⟩
      (R.₁ (adj.counit.ε _) C.∘ adj.unit.η _ C.∘ om.map)         ≡⟨ C.cancell adj.zag ⟩
      om.map                                                     ≡⟨ sym (C.idr _) ⟩
      om.map C.∘ C.id                                            ∎
    )
    where module om = ↓Obj other-map
```

Checking that the triangle above commutes is a routine application of
naturality and the triangle identities; The same is true for proving
that the map $g$ above is unique.

```agda
  L⊣R→map-to-R-is-initial x other-map .paths y =
    ↓Hom-path _ _ refl (
      adj.counit.ε _ D.∘ L.₁ om.map                            ≡⟨ D.refl⟩∘⟨ L.expand (sym (C.idr _) ∙ y .↓Hom.sq) ⟩
      adj.counit.ε _ D.∘ L.₁ (R.₁ y.β) D.∘ L.₁ (adj.unit.η _)  ≡⟨ D.pulll (adj.counit.is-natural _ _ _) ⟩ -- nvmd
      (y.β D.∘ adj.counit.ε _) D.∘ L.₁ (adj.unit.η _)          ≡⟨ D.cancelr adj.zig ⟩
      y.β                                                      ∎
    )
    where
      module om = ↓Obj other-map
      module y = ↓Hom y
```

Hence, we can safely say that having a functor $L$ and an adjunction $L
\dashv R$ is the same thing as having a functor $R$ and a system of
universal arrows into $R$:

```
  L⊣R→universal-maps : ∀ x → Universal-morphism x R
  L⊣R→universal-maps x .Initial.bot = L⊣R→map-to-R x
  L⊣R→universal-maps x .Initial.has⊥ = L⊣R→map-to-R-is-initial x
```

<!-- TODO [Amy 2022-03-02]
prove that we recover L by going L⊣R → universal maps → L⊣R. this is
straightforward but I'm tired
-->

# Adjuncts

Another view on adjunctions, one which is productive when thinking about
adjoint *endo*functors $L \dashv R$, is the concept of _adjuncts_. Any
pair of natural transformations _typed like_ a unit and counit allow you
to pass between the Hom-sets $\hom(La,b)$ and $\hom(a,Rb)$, by composing
the functorial action of $L$ (resp $R$) with the natural
transformations:

<!--
```agda
module _ {L : Functor C D} {R : Functor D C} (adj : L ⊣ R) where
  private
    module L = Func L
    module R = Func R
    module C = Cat.Reasoning C
    module D = Cat.Reasoning D
    module adj = _⊣_ adj
```
-->

```agda
  L-adjunct : ∀ {a b} → D.Hom (L.₀ a) b → C.Hom a (R.₀ b)
  L-adjunct f = R.₁ f C.∘ adj.unit.η _

  R-adjunct : ∀ {a b} → C.Hom a (R.₀ b) → D.Hom (L.₀ a) b
  R-adjunct f = adj.counit.ε _ D.∘ L.₁ f
```

The important part that the actual data of an adjunction gets you is
these functions are inverse _equivalences_ between the hom-sets
$\hom(La,b) \cong \hom(a,Rb)$.

```agda
  L-R-adjunct : ∀ {a b} → is-right-inverse (R-adjunct {a} {b}) L-adjunct
  L-R-adjunct f =
    R.₁ (adj.counit.ε _ D.∘ L.₁ f) C.∘ adj.unit.η _        ≡⟨ R.pushl refl ⟩
    R.₁ (adj.counit.ε _) C.∘ R.₁ (L.₁ f) C.∘ adj.unit.η _  ≡˘⟨ C.refl⟩∘⟨ adj.unit.is-natural _ _ _ ⟩
    R.₁ (adj.counit.ε _) C.∘ adj.unit.η _ C.∘ f            ≡⟨ C.cancell adj.zag ⟩
    f                                                      ∎

  R-L-adjunct : ∀ {a b} → is-left-inverse (R-adjunct {a} {b}) L-adjunct
  R-L-adjunct f =
    adj.counit.ε _ D.∘ L.₁ (R.₁ f C.∘ adj.unit.η _)       ≡⟨ D.refl⟩∘⟨ L.F-∘ _ _ ⟩
    adj.counit.ε _ D.∘ L.₁ (R.₁ f) D.∘ L.₁ (adj.unit.η _) ≡⟨ D.extendl (adj.counit.is-natural _ _ _) ⟩
    f D.∘ adj.counit.ε _ D.∘ L.₁ (adj.unit.η _)           ≡⟨ D.elimr adj.zig ⟩
    f                                                     ∎

  L-adjunct-is-equiv : ∀ {a b} → is-equiv (L-adjunct {a} {b})
  L-adjunct-is-equiv = is-iso→is-equiv
    (iso R-adjunct L-R-adjunct R-L-adjunct)

  R-adjunct-is-equiv : ∀ {a b} → is-equiv (R-adjunct {a} {b})
  R-adjunct-is-equiv = is-iso→is-equiv
    (iso L-adjunct R-L-adjunct L-R-adjunct)
```

<!--
```agda
module _ {L : Functor C D} {R : Functor D C} (adj : L ⊣ R) where
  private
    module L = Functor L
    module R = Functor R
    module C = Cat.Reasoning C
    module D = Cat.Reasoning D
    module adj = _⊣_ adj

  open _⊣_
  open _=>_

  opposite-adjunction : R.op ⊣ L.op
  opposite-adjunction .unit .η _ = adj.counit.ε _
  opposite-adjunction .unit .is-natural x y f = sym (adj.counit.is-natural _ _ _)
  opposite-adjunction .counit .η _ = adj.unit.η _
  opposite-adjunction .counit .is-natural x y f = sym (adj.unit.is-natural _ _ _)
  opposite-adjunction .zig = adj.zag
  opposite-adjunction .zag = adj.zig
```
-->
