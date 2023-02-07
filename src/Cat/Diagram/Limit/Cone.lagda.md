```agda
open import Cat.Instances.Shape.Terminal
open import Cat.Diagram.Limit.Base
open import Cat.Instances.Functor
open import Cat.Diagram.Terminal
open import Cat.Functor.Kan.Base
open import Cat.Prelude

import Cat.Functor.Reasoning as Func
import Cat.Reasoning

module Cat.Diagram.Limit.Cone where
```

# Limits via Cones

As noted in the main page on [limits], most introductory material defines
limits via a mathematical widget called a **cone**.

[limits]: Cat.Diagram.Limit.Base.html

<!--
```agda
private variable
  o₁ o₂ h₁ h₂ : Level
```
-->

```agda
module _ {J : Precategory o₁ h₁} {C : Precategory o₂ h₂} (F : Functor J C) where
  private
    import Cat.Reasoning J as J
    import Cat.Reasoning C as C
    module F = Functor F

  record Cone : Type (o₁ ⊔ o₂ ⊔ h₁ ⊔ h₂) where
    no-eta-equality
    constructor cone
```

A `Cone`{.Agda} over $F$ is given by an object (the `apex`{.agda})
together with a family of maps `ψ`{.Agda} --- one for each object in the
indexing category `J`{.Agda} --- such that "everything in sight
commutes".

```agda
    field
      apex     : C.Ob
      ψ        : (x : J.Ob) → C.Hom apex (F.₀ x)
```

For every map $f : x \to y$ in the indexing category, we require that
the diagram below commutes. This encompasses "everything" since the only
non-trivial composites that can be formed with the data at hand are of
the form $F(f) \circ \psi_x$.

```agda
      commutes : ∀ {x y} (f : J.Hom x y) → F.₁ f C.∘ ψ x ≡ ψ y
```

These non-trivial composites consist of following the left leg of the
diagram below, followed by the bottom leg. For it to commute, that path
has to be the same as following the right leg.

~~~{.quiver .short-05}
\[\begin{tikzcd}
  & {\operatorname{apex}} \\
  {F(x)} && {F(y)}
  \arrow["{F(f)}"', from=2-1, to=2-3]
  \arrow["{\psi_x}"', from=1-2, to=2-1]
  \arrow["{\psi_y}", from=1-2, to=2-3]
\end{tikzcd}\]
~~~

Since paths in Hom-spaces `are propositions`{.Agda ident=Hom-set}, to
test equality of cones, it suffices for the apices to be equal, and for
their $\psi$s to assign equal morphisms for every object in the shape
category.

```agda
  Cone-path : {x y : Cone}
        → (p : Cone.apex x ≡ Cone.apex y)
        → (∀ o → PathP (λ i → C.Hom (p i) (F.₀ o)) (Cone.ψ x o) (Cone.ψ y o))
        → x ≡ y
  Cone-path p q i .Cone.apex = p i
  Cone-path p q i .Cone.ψ o = q o i
  Cone-path {x = x} {y} p q i .Cone.commutes {x = a} {y = b} f =
    is-prop→pathp (λ i → C.Hom-set _ _ (F.₁ f C.∘ q a i) (q b i))
      (x .commutes f) (y .commutes f) i
    where open Cone
```

## Cone maps

```agda
  record Cone-hom (x y : Cone) : Type (o₁ ⊔ h₂) where
    no-eta-equality
    constructor cone-hom
```

A `Cone homomorphism`{.Agda ident="Cone-hom"} is -- like the introduction
says -- a map `hom`{.Agda} in the ambient category between the apices,
such that "everything in sight `commutes`{.Agda ident="Cone-hom.commutes"}".
Specifically, for any choice of object $o$ in the index category, the
composition of `hom`{.Agda} with the domain cone's `ψ`{.Agda} (at that
object) must be equal to the codomain's `ψ`{.Agda}.


```agda
    field
      hom      : C.Hom (Cone.apex x) (Cone.apex y)
      commutes : ∀ o → Cone.ψ y o C.∘ hom ≡ Cone.ψ x o
```

<!--
```agda
  private unquoteDecl eqv = declare-record-iso eqv (quote Cone-hom)

  Cone-hom-path : ∀ {x y} {f g : Cone-hom x y} → Cone-hom.hom f ≡ Cone-hom.hom g → f ≡ g
  Cone-hom-path p i .Cone-hom.hom = p i
  Cone-hom-path {x = x} {y} {f} {g} p i .Cone-hom.commutes o j =
    is-set→squarep (λ i j → C.Hom-set _ _)
      (λ j → Cone.ψ y o C.∘ p j) (f .Cone-hom.commutes o) (g .Cone-hom.commutes o) refl i j
```
-->

Since cone homomorphisms are morphisms in the underlying category with
extra properties, we can lift the laws from the underlying category to
the category of `Cones`{.Agda}. The definition of `compose`{.Agda} is the
enlightening part, since we have to prove that two cone homomorphisms
again preserve _all_ the commutativities.

```agda
  Cones : Precategory _ _
  Cones = cat where
    open Precategory

    compose : {x y z : _} → Cone-hom y z → Cone-hom x y → Cone-hom x z
    compose {x} {y} {z} F G = r where
      open Cone-hom
      r : Cone-hom x z
      r .hom = hom F C.∘ hom G
      r .commutes o =
        Cone.ψ z o C.∘ hom F C.∘ hom G ≡⟨ C.pulll (commutes F o) ⟩
        Cone.ψ y o C.∘ hom G           ≡⟨ commutes G o ⟩
        Cone.ψ x o                     ∎

    cat : Precategory _ _
    cat .Ob = Cone
    cat .Hom = Cone-hom
    cat .id = record { hom = C.id ; commutes = λ _ → C.idr _ }
    cat ._∘_ = compose
    cat .idr f = Cone-hom-path (C.idr _)
    cat .idl f = Cone-hom-path (C.idl _)
    cat .assoc f g h = Cone-hom-path (C.assoc _ _ _)
```

<!--
```agda
    cat .Hom-set x y = Iso→is-hlevel 2 eqv hlevel!

  open _=>_
```
-->

## Terminal Cones as Limits

Note that cones over some diagram $F$ contain the exact same data as
natural transformations from a constant functor to $F$.
To obtain a limit, all we need is a way of stating that a given cone is
universal. In particular, the [terminal object] in the category of cones
over a diagram $F$ (if it exists!) is the limit of $F$.

[terminal object]: Cat.Diagram.Terminal.html

The proof here is just shuffling data around: this is not totally
surprising, as both constructions contain the same data, just organized
differently.

```agda
  Cone→cone : (K : Cone) → Const (Cone.apex K) => F
  Cone→cone K .η = K .Cone.ψ
  Cone→cone K .is-natural x y f = C.idr _ ∙ sym (K .Cone.commutes f)

  cone→Cone : ∀ {x} → Const x => F → Cone
  cone→Cone {x = x} σ .Cone.apex = x
  cone→Cone σ .Cone.ψ = σ .η
  cone→Cone σ .Cone.commutes f = sym (σ .is-natural _ _ f) ∙ C.idr _

  is-terminal-cone→is-limit
    : ∀ {K : Cone}
    → is-terminal Cones K
    → is-limit F (Cone.apex K) (Cone→cone K)
  is-terminal-cone→is-limit {K = K} term = to-is-limitp isl refl where
    open Cone-hom
    open make-is-limit
    open is-terminal Cones term
    open Cone

    isl : make-is-limit F (Cone.apex K)
    isl .ψ = K .ψ
    isl .commutes = K .commutes
    isl .universal eta p = ! {x = cone _ eta p} .hom
    isl .factors eta p = ! {x = cone _ eta p} .commutes _
    isl .unique eta p other q = ap hom (!-unique (cone-hom other q))
```

The inverse direction of this equivalence also consists of packing and
unpacking data.

```agda
  is-limit→is-terminal-cone
    : ∀ {x} {eps : Const x => F}
    → (L : is-limit F x eps)
    → is-terminal Cones (cone→Cone eps)
  is-limit→is-terminal-cone {x = x} {eps = eps} L = to-is-terminal Cones term where
    module L = is-limit L
    open make-is-terminal
    open Cone
    open Cone-hom

    term : make-is-terminal Cones (cone→Cone eps)
    term .! {K} .hom =
      L.universal (K .ψ) (K .commutes)
    term .! {K} .commutes _ =
      L.factors (K .ψ) (K .commutes)
    term .!-unique {K} f =
      Cone-hom-path (L.unique (K .ψ) (K .commutes) (f .hom) (f .commutes))
```

<!--
```agda
  open Ran

  Terminal-cone→Limit : Terminal Cones → Limit F
  Terminal-cone→Limit K =
    to-limit $ is-terminal-cone→is-limit $ Terminal.has-is-terminal Cones K

  Limit→Terminal-cone : Limit F → Terminal Cones
  Limit→Terminal-cone L =
    to-limit $ is-limit→is-terminal-cone $ Limit.has-limit L
```
-->
