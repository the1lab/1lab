<!--
```agda
open import Cat.Diagram.Colimit.Base
open import Cat.Functor.Constant
open import Cat.Functor.Kan.Base
open import Cat.Diagram.Initial
open import Cat.Prelude

import Cat.Functor.Reasoning as Func
import Cat.Reasoning
```
-->

```agda
module Cat.Diagram.Colimit.Cocone where
```

<!--
```agda
private variable
  o ℓ o' ℓ' : Level

open _=>_
```
-->

# Colimits via cocones {defines="cocone"}

As noted in the main page on [[colimits]], most introductory texts opt
to define colimits via categorical gadgets called **cocones**. A
`Cocone`{.Agda} over $F$ is given by an object (the `coapex`{.agda})
together with a family of maps `ψ`{.Agda} --- one for each object in the
indexing category `J`{.Agda} --- such that "everything in sight
commutes".

<!--
```agda
module _ {J : Precategory o ℓ} {C : Precategory o' ℓ'} (F : Functor J C) where
  private
    module C = Cat.Reasoning C
    module J = Precategory J
    module F = Functor F
```
-->

```agda
  record Cocone : Type (o ⊔ ℓ ⊔ o' ⊔ ℓ') where
    no-eta-equality
    constructor cocone
    field
      coapex : C.Ob
      ψ      : (x : J.Ob) → C.Hom (F.₀ x) coapex
      commutes : ∀ {x y} (f : J.Hom x y) → ψ y C.∘ F.₁ f ≡ ψ x
```

<!--
```agda
  open Cocone

  Cocone-path : {x y : Cocone}
              → (p : x .coapex ≡ y .coapex)
              → (∀ o → PathP (λ i → C.Hom (F.₀ o) (p i)) (ψ x o) (ψ y o))
              → x ≡ y
  Cocone-path p q i .coapex = p i
  Cocone-path p q i .ψ o = q o i
  Cocone-path {x = x} {y = y} p q i .commutes {x = a} {y = b} f =
    is-prop→pathp (λ i → C.Hom-set _ _ (q b i C.∘ F.₁ f) (q a i))
      (x .commutes f) (y .commutes f) i
```
-->

## Cocone maps

To express the universal property of a colimit in terms of cocones, we
now have to define the notion of **cocone homomorphism**. We define a
cocone homomorphism to be a map between the coapices which commutes with
the family $\psi$.

```agda
  record Cocone-hom (x y : Cocone) : Type (o ⊔ ℓ') where
    no-eta-equality
    constructor cocone-hom
    field
      map : C.Hom (x .coapex) (y .coapex)
      com : ∀ o → map C.∘ x .ψ o ≡ y .ψ o
```

<!--
```agda
  private unquoteDecl eqv = declare-record-iso eqv (quote Cocone-hom)

  open Cocone-hom

  Cocone-hom-path : ∀ {x y} {f g : Cocone-hom x y} → f .map ≡ g .map → f ≡ g
  Cocone-hom-path p i .map = p i
  Cocone-hom-path {x = x} {y = y} {f = f} {g = g} p i .com o j =
    is-set→squarep (λ i j → C.Hom-set _ _)
      (λ j → p j C.∘ x .ψ o) (f .com o) (g .com o) refl i j
```
-->

Since cocone homomorphisms are closed under composition in the base
category, it's immediate that they form a category.

```agda
  Cocones : Precategory _ _
  Cocones = cat where
    open Precategory

    compose : ∀ {x y z} → Cocone-hom y z → Cocone-hom x y → Cocone-hom x z
    compose K L .map = K .map C.∘ L .map
    compose {x = x} {y = y} {z = z} K L .com o =
      (K .map C.∘ L .map) C.∘ x .ψ o ≡⟨ C.pullr (L .com o) ⟩
      K .map C.∘ y .ψ o              ≡⟨ K .com o ⟩
      z .ψ o                         ∎
```

<!--
```agda
    cat : Precategory _ _
    cat .Ob = Cocone
    cat .Hom = Cocone-hom
    cat .id = cocone-hom C.id (λ _ → C.idl _)
    cat ._∘_ = compose
    cat .idr f = Cocone-hom-path (C.idr (f .map))
    cat .idl f = Cocone-hom-path (C.idl (f .map))
    cat .assoc f g h = Cocone-hom-path (C.assoc (f .map) (g .map) (h .map))
    cat .Hom-set x y = Iso→is-hlevel! 2 eqv
```
-->


## Initial cocones as colimits

A cocone over some diagram $F$ contains the same data as natural
transformation from $F$ to a constant functor. Since we have defined a
colimit to consist of (a functor equipped with) a natural transformation
into a constant functor, there is an equivalence between the cocones
defined here and those considered in the definition of colimit.

```agda
  Cocone→cocone : (K : Cocone) → F => Const (Cocone.coapex K)
  Cocone→cocone K .η = K .Cocone.ψ
  Cocone→cocone K .is-natural x y f = K .Cocone.commutes f ∙ sym (C.idl _)

  cocone→Cocone : ∀ {coapex} (K : F => Const coapex) → Cocone
  cocone→Cocone {coapex} K .coapex = coapex
  cocone→Cocone K .ψ j = K .η j
  cocone→Cocone K .commutes f = K .is-natural _ _ f ∙ C.idl _

  Cocone≃cocone : Cocone ≃ (Σ[ coapex ∈ C.Ob ] F => Const coapex)
  Cocone≃cocone .fst K = K .coapex , Cocone→cocone K
  Cocone≃cocone .snd = is-iso→is-equiv λ where
    .is-iso.from (coapex , K) → cocone→Cocone K
    .is-iso.rinv (coapex , K) → refl ,ₚ ext λ _ → refl
    .is-iso.linv K → Cocone-path refl (λ _ → refl)
```

We can then rephrase the universality from the definition of [[left Kan
extension]] by asking that a particular cocone be [[initial]] in the
category we have just constructed.

```agda
  is-initial-cocone→is-colimit
    : ∀ {K : Cocone}
    → is-initial Cocones K
    → is-colimit F (Cocone.coapex K) (Cocone→cocone K)
  is-initial-cocone→is-colimit {K = K} init = to-is-colimitp colim refl where
    open make-is-colimit
    open Cocone
    open Cocone-hom

    colim : make-is-colimit F (Cocone.coapex K)
    colim .ψ = K .ψ
    colim .commutes = K .commutes
    colim .universal eta p = init (cocone _ eta p) .centre .map
    colim .factors eta p = init (cocone _ eta p) .centre .com _
    colim .unique eta p other q =
      ap map (sym (init (cocone _ eta p) .paths (cocone-hom other q)))
```

To finish concretising the correspondence, note that this process is
invertible: From a colimit, we can extract an initial cocone.

```agda
  is-colimit→is-initial-cocone
    : ∀ {x} {eta : F => Const x}
    → (L : is-colimit F x eta)
    → is-initial Cocones (cocone→Cocone eta)
```

<details>
<summary>The proof consists of more data shuffling, so we omit it.
</summary>

```agda
  is-colimit→is-initial-cocone {x = x} {eta} L K = init where
    module L = is-colimit L
    module K = Cocone K
    open Cocone-hom

    init : is-contr (Cocone-hom (cocone→Cocone eta) K)
    init .centre .map   = L.universal K.ψ K.commutes
    init .centre .com _ = L.factors K.ψ K.commutes
    init .paths f =
      Cocone-hom-path (sym (L.unique K.ψ K.commutes (f .map) (f .com)))
```
</details>

<!--
```agda
  is-colimit≃is-initial-cocone
    : is-initial Cocones ≃[ Cocone≃cocone ] uncurry (is-colimit F)
  is-colimit≃is-initial-cocone = prop-over-ext! Cocone≃cocone
    (λ _ → is-initial-cocone→is-colimit)
    (λ _ → is-colimit→is-initial-cocone)

  Initial-cocone→Colimit : Initial Cocones → Colimit F
  Initial-cocone→Colimit x = to-colimit (is-initial-cocone→is-colimit (x .Initial.has⊥))

  Colimit→Initial-cocone : Colimit F → Initial Cocones
  Colimit→Initial-cocone x .Initial.bot = _
  Colimit→Initial-cocone x .Initial.has⊥ = is-colimit→is-initial-cocone (Colimit.has-colimit x)

module _ {J : Precategory o ℓ} {C : Precategory o' ℓ'} {F : Functor J C} where
  private module C = Cat.Reasoning C
  open Cocone

  instance
    Extensional-Cocone-hom
      : ∀ {ℓr x y}
      → ⦃ e : Extensional (C.Hom (x .coapex) (y .coapex)) ℓr ⦄
      → Extensional (Cocone-hom F x y) ℓr
    Extensional-Cocone-hom ⦃ e ⦄ = injection→extensional! (Cocone-hom-path F) e
```
-->
