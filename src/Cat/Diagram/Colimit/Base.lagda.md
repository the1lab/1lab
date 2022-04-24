```agda
open import Cat.Diagram.Initial
open import Cat.Prelude

import Cat.Functor.Reasoning as Func
import Cat.Morphism

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

# Construction

Every concrete colimit ([coproducts], [coequalisers], [initial objects])
we have seen so far consists of roughly the same data. We begin with
some collection of objects and morphisms, and then state that the
colimit of that collection is some object with a universal property
relating all of those objects and morphisms.

[coproducts]: Cat.Diagra.Coproduct
[coequalisers]: Cat.Diagra.Coequaliser
[initial objects]: Cat.Diagra.Initial

It would be convienent to be able to talk about _all_ of these
situations at once, as opposed to on a case-by-case basis. To do this,
we need to introduce a bit of categorical machinery: the Cocone.

The first step is to generalize the "collection of objects and
morphisms" involved. Luckily, this step involves no new ideas, just
a change in perspective. We already have a way of describing a
collection of objects and morphisms: it's a category! As an example,
the starting data of a coproduct is a pair of objects, which can
be thought of as a very simple category, with only identity morphisms.

~~~{.quiver .short-2}
\[\begin{tikzcd}
A & B
\end{tikzcd}\]
~~~

The next step also involves nothing more than a change in perspective.
Let's denote our "diagram" category from earlier as $J$. Then, a means
of picking out a $J$ shaped figure in $C$ is... a functor $F : J \to C$!
Going back to the coproduct example, a functor from our 2 object
category into $C$ selects 2 (not necessarily distinct!) objects in $C$.
We this pair of category and functor a _diagram_ in $C$.

```agda
module _ {J : Precategory o ℓ} {C : Precategory o′ ℓ′} (F : Functor J C) where
  private
    import Cat.Reasoning J as J
    import Cat.Reasoning C as C
    module F = Functor F

  record Cocone : Type (o ⊔ ℓ ⊔ o′ ⊔ ℓ′) where
    no-eta-equality
    constructor cocone
```

Now, for the actual machinery! If we want to capture the essence of
all of our concrete examples of colimits, we a notion of an object
equipped with maps _from_ every object in our diagram. We call this
designated object the "coapex" of the cocone.


```agda
    field
      coapex : C.Ob
      ψ      : (x : J.Ob) → C.Hom (F.₀ x) coapex
```

If our diagram consisted of only objects, we would be done! However,
some diagrams contan non-identity morphisms, so we need to take those
into account as well. This bit is best understood through the lens of
the coequaliser: in order to describe the commuting condition there,
we want every injection map from the codomain of a morphism to
factor through that morphism.

```agda
      commutes : ∀ {x y} (f : J.Hom x y) → ψ y C.∘ F.₁ f ≡ ψ x
```

As per usual, we define a helper lemma charaterizing the path space
of cones:

```agda
  open Cocone

  Cocone-path : {x y : Cocone}
              → (p : coapex x ≡ coapex y)
              → (∀ o → PathP (λ i → C.Hom (F.₀ o) (p i)) (ψ x o) (ψ y o))
              → x ≡ y
  Cocone-path p q i .coapex = p i
  Cocone-path p q i .ψ o = q o i
  Cocone-path {x = x} {y = y} p q i .commutes {x = a} {y = b} f =
    is-prop→pathp (λ i → C.Hom-set _ _ (q b i C.∘ F.₁ f) (q a i))
      (x .commutes f) (y .commutes f) i
```

## Cocone Maps

Now that we've defined cocones, we need a way to figure out how to
express universal properties. Like most things categorical, we begin
by considering a "cocone morphism", which will give us a category
that we can work within. The idea here is that a morphism of cocones
is a morphism in $C$ between the coapicies, such that all of the
injection maps commute.

```agda
  record Cocone-hom (x y : Cocone) : Type (o ⊔ ℓ′) where
    no-eta-equality
    constructor cocone-hom
    field
      hom : C.Hom (x .coapex) (y .coapex)
      commutes : ∀ o → hom C.∘ x .ψ o ≡ y .ψ o
```

<!--
```agda
  private unquoteDecl eqv = declare-record-iso eqv (quote Cocone-hom)
```
-->

We define yet another helper lemma that describes the path space
of cocone morphisms.

```agda
  open Cocone-hom

  Cocone-hom-path : ∀ {x y} {f g : Cocone-hom x y} → f .hom ≡ g .hom → f ≡ g
  Cocone-hom-path p i .hom = p i
  Cocone-hom-path {x = x} {y = y} {f = f} {g = g} p i .commutes o j =
    is-set→squarep (λ i j → C.Hom-set _ _)
      (λ j → p j C.∘ x .ψ o) (f .commutes o) (g .commutes o) refl i j
```

Now, we can define the category of cocones over a given diagram:

```agda
  Cocones : Precategory _ _
  Cocones = cat where
    open Precategory

    compose : ∀ {x y z} → Cocone-hom y z → Cocone-hom x y → Cocone-hom x z
    compose K L .hom = K .hom C.∘ L .hom
    compose {x = x} {y = y} {z = z} K L .commutes o =
      (K .hom C.∘ L .hom) C.∘ x .ψ o ≡⟨ C.pullr (L .commutes o) ⟩
      K .hom C.∘ y .ψ o              ≡⟨ K .commutes o ⟩
      z .ψ o                         ∎

    cat : Precategory _ _
    cat .Ob = Cocone
    cat .Hom = Cocone-hom
    cat .id = cocone-hom C.id (λ _ → C.idl _)
    cat ._∘_ = compose
    cat .idr f = Cocone-hom-path (C.idr (f .hom))
    cat .idl f = Cocone-hom-path (C.idl (f .hom))
    cat .assoc f g h = Cocone-hom-path (C.assoc (f .hom) (g .hom) (h .hom))

```

<!--
```agda
    cat .Hom-set x y = is-hlevel≃ 2 (Iso→Equiv eqv e⁻¹) (hlevel 2)
      where open C.HLevel-instance
```
-->

## Colimits

We now have all of the machinery in place! What remains is the
universal property, which expresses that a _particular_ cocone
is universal, in the sense that it has a _unique_ map to any other
cocone. However, we already have something that captures this idea,
it's the initial object! This leads to the following terse definition:
A colimit over a diagram is an initial object in the category of
cocones over that diagram.
```
  is-colimit : Cocone → Type _
  is-colimit K = is-initial Cocones K

  Colimit : Type _
  Colimit = Initial Cocones

  Colimit-apex : Colimit → C.Ob
  Colimit-apex x = coapex (Initial.bot x)
```


<!--
```agda
module _ {o₁ h₁ o₂ h₂ o₃ h₃ : _}
         {J : Precategory o₁ h₁}
         {C : Precategory o₂ h₂}
         {D : Precategory o₃ h₃}
         {Dia : Functor J C}
         (F : Functor C D)
  where

  private
    module D = Precategory D
    module C = Precategory C
    module J = Precategory J
    module F = Func F

  open Functor
```
-->

# Preservation of Colimits

Because a cocone is a commutative diagram, any given functor $F : \ca{C}
\to \ca{D}$ takes cocones in $\ca{C}$ to cocones in $\ca{D}$, as
functors preserve commutative diagrams.

```agda
  F-map-cocone : Cocone Dia → Cocone (F F∘ Dia)
  F-map-cocone x .Cocone.coapex = F.₀ (Cocone.coapex x)
  F-map-cocone x .Cocone.ψ f = F.₁ (Cocone.ψ x f)
  F-map-cocone x .Cocone.commutes {y = y} f =
    F.₁ (Cocone.ψ x y) D.∘ F .F₁ _ ≡⟨ F.collapse (Cocone.commutes x _) ⟩
    F.₁ (Cocone.ψ x _)             ∎
```

Though functors must take cocones to cocones, they may not necessarily
take colimiting cocones to colimiting cocones! When a functor does, we
say that it _preserves_ colimits.

```agda
  Preserves-colimit : Cocone Dia → Type _
  Preserves-colimit K = is-colimit Dia K → is-colimit (F F∘ Dia) (F-map-cocone K)
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
