```agda
open import Cat.Instances.Functor
open import Cat.Diagram.Colimit.Base
open import Cat.Diagram.Initial
open import Cat.Prelude

import Cat.Functor.Reasoning as Func
import Cat.Reasoning

module Cat.Diagram.Colimit.Cocone where
```

<!--
```agda
private variable
  o ℓ o′ ℓ′ : Level
```
-->

# Colimits via Cocones

As noted in the main page on [colimits], most introductory texts opt
to define colimits via a categorical gadget called a **cocone**.

[colimits]: Cat.Diagram.Colimit.Base.html

A `Cocone`{.Agda} over $F$ is given by an object (the `coapex`{.agda})
together with a family of maps `ψ`{.Agda} --- one for each object in the
indexing category `J`{.Agda} --- such that "everything in sight
commutes".

```agda
module _ {J : Precategory o ℓ} {C : Precategory o′ ℓ′} (F : Functor J C) where
  private
    import Cat.Reasoning J as J
    import Cat.Reasoning C as C
    module F = Functor F

  record Cocone : Type (o ⊔ ℓ ⊔ o′ ⊔ ℓ′) where
    no-eta-equality
    constructor cocone
    field
      coapex : C.Ob
      ψ      : (x : J.Ob) → C.Hom (F.₀ x) coapex
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
    cat .Hom-set x y = Iso→is-hlevel 2 eqv hlevel!
```
-->


## Initial Cocones as Colimits

A cocone over some diagram $F$ contains the same data as natural
transformations from $F$ to a constant functor. This means that they
contain all of the data of a colimit; the only other bit we need is
the universal property. This can be obtained by defining a colimit to
be the [initial] object in the category of cocones over $F$.

[initial object]: Cat.Diagram.Initial.html

The proof mostly is an exercise in shuffling about data.

```agda
  is-initial-cocone→is-colimit
    : ∀ {K : Cocone}
    → is-initial Cocones K
    → is-colimit F (Cocone.coapex K)
  is-initial-cocone→is-colimit {K = K} init = to-is-colimit colim where
    open make-is-colimit
    open Cocone
    open Cocone-hom

    colim : make-is-colimit F (Cocone.coapex K)
    colim .ψ = K .ψ
    colim .commutes = K .commutes
    colim .universal eta p = init (cocone _ eta p) .centre .hom
    colim .factors eta p = init (cocone _ eta p) .centre .commutes _
    colim .unique eta p other q =
      ap hom (sym (init (cocone _ eta p) .paths (cocone-hom other q)))
```

The inverse direction of this equivalences also consists of moving
data around.

```agda
  is-colimit→is-initial-cocone
    : ∀ {x}
    → (L : is-colimit F x)
    → is-initial Cocones (cocone x (is-colimit.ψ L) (is-colimit.commutes L))
  is-colimit→is-initial-cocone {x  = x} L K = init where
    module L = is-colimit L
    module K = Cocone K
    open Cocone-hom

    init : is-contr (Cocone-hom (cocone x L.ψ L.commutes) K)
    init .centre .hom =
      L.universal K.ψ K.commutes
    init .centre .commutes _ =
      L.factors K.ψ K.commutes
    init .paths f =
      Cocone-hom-path (sym (L.unique K.ψ K.commutes (f .hom) (f .commutes)))
```

