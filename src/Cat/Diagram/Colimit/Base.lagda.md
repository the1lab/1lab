```agda
open import Cat.Diagram.Initial
open import Cat.Prelude

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

  Cocone≡ : {x y : Cocone}
              → (p : coapex x ≡ coapex y)
              → (∀ o → PathP (λ i → C.Hom (F.₀ o) (p i)) (ψ x o) (ψ y o))
              → x ≡ y
  Cocone≡ p q i .coapex = p i
  Cocone≡ p q i .ψ o = q o i
  Cocone≡ {x = x} {y = y} p q i .commutes {x = a} {y = b} f =
    isProp→PathP (λ i → C.Hom-set _ _ (q b i C.∘ F.₁ f) (q a i))
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
  record CoconeHom (x y : Cocone) : Type (o ⊔ ℓ′) where
    no-eta-equality
    constructor cocone-hom
    field
      hom : C.Hom (x .coapex) (y .coapex)
      commutes : ∀ {o} → hom C.∘ x .ψ o ≡ y .ψ o
```

We define yet another helper lemma that describes the path space
of cocone morphisms.

```agda
  open CoconeHom

  CoconeHom≡ : ∀ {x y} {f g : CoconeHom x y} → f .hom ≡ g .hom → f ≡ g
  CoconeHom≡ p i .hom = p i
  CoconeHom≡ {x = x} {y = y} {f = f} {g = g} p i .commutes {o} j =
    isSet→SquareP (λ i j → C.Hom-set _ _)
      (λ j → p j C.∘ x .ψ o) (f .commutes) (g .commutes) refl i j
```

Now, we can define the category of cocones over a given diagram:

```agda
  Cocones : Precategory _ _
  Cocones = cat where
    open Precategory

    compose : ∀ {x y z} → CoconeHom y z → CoconeHom x y → CoconeHom x z
    compose K L .hom = K .hom C.∘ L .hom
    compose {x = x} {y = y} {z = z} K L .commutes {o} =
      (K .hom C.∘ L .hom) C.∘ x .ψ o ≡⟨ C.pullr (L .commutes) ⟩
      K .hom C.∘ y .ψ o              ≡⟨ K .commutes ⟩
      z .ψ o                         ∎

    cat : Precategory _ _
    cat .Ob = Cocone
    cat .Hom = CoconeHom
    cat .id = cocone-hom C.id (C.idl _)
    cat ._∘_ = compose
    cat .idr f = CoconeHom≡ (C.idr (f .hom))
    cat .idl f = CoconeHom≡ (C.idl (f .hom))
    cat .assoc f g h = CoconeHom≡ (C.assoc (f .hom) (g .hom) (h .hom))

```

<!--
```agda
    cat .Hom-set x y = isHLevel-retract 2 pack unpack pack∘unpack hl
      where abstract
        T : Type (o ⊔ ℓ′)
        T = Σ[ hom ∈ C.Hom (x .coapex) (y .coapex) ]
            (∀ o → hom C.∘ x .ψ o ≡ y .ψ o)

        pack : T → CoconeHom x y
        pack x = cocone-hom (x .fst) (x .snd _)

        unpack : CoconeHom x y → T
        unpack r = r .hom , λ _ → r .commutes

        pack∘unpack : isLeftInverse pack unpack
        pack∘unpack x i .hom = x .hom
        pack∘unpack x i .commutes = x .commutes

        hl : isSet T
        hl = isHLevelΣ 2 (C.Hom-set _ _) 
              (λ _ → isHLevelΠ 2 λ _ → isProp→isSet (C.Hom-set _ _ _ _))
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
  Colimit : Type _
  Colimit = Initial Cocones

  Colimit-apex : Colimit → C.Ob
  Colimit-apex x = coapex (Initial.bot x)
```
