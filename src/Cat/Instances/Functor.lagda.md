```agda
open import Cat.Prelude

open Precategory
open Functor
open _=>_

module Cat.Instances.Functor where

private variable
  o h : Level
  C D : Precategory o h
  F G : Functor C D
```

# Functor (pre)categories

The identity natural transformation sends any functor to itself:

```agda
idnt : {F : Functor C D} → F => F
idnt {C = C} {D = D} .η x = D .id
idnt {C = C} {D = D} .is-natural x y f = D .idl _ ∙ sym (D .idr _)
```

Natural transformations compose:

```agda
_∘nt_ : {F G H : Functor C D} → G => H → F => G → F => H
```

<!--
```
_∘nt_ {C = C} {D = D} {F} {G} {H} f g = nat where
  module C = Precategory C
  module D = Precategory D
  module F = Functor F
  module G = Functor G
  module H = Functor H

  nat : F => H
  nat .η x = f .η _ D.∘ g .η _
  nat .is-natural x y h =
    (f .η y D.∘ g .η y) D.∘ F.₁ h    ≡⟨ sym (D.assoc _ _ _) ⟩
    f .η y D.∘ (g .η y D.∘ F.₁ h)    ≡⟨ ap (D._∘_ (f .η y)) (g .is-natural _ _ _) ⟩
    f .η y D.∘ (G.₁ h D.∘ g .η x)    ≡⟨ D.assoc _ _ _ ⟩
    (f .η y D.∘ G.₁ h) D.∘ (g .η x)  ≡⟨ ap (λ e → e D.∘ (g .η x)) (f .is-natural _ _ _) ⟩
    (H.₁ h D.∘ f .η x) D.∘ (g .η x)  ≡⟨ sym (D.assoc _ _ _) ⟩
    H.₁ h D.∘  f .η _ D.∘ g .η  _    ∎
```
-->

It is not very hard to show that these definitions assemble into a
category where the objects are functors $F, G : C \to D$, and the
morphisms are natural transformations $F \Rightarrow G$. This is because
natural transformations inherit the identity and associativity laws from
the codomain category $D$, and since hom-sets are sets,
`is-natural`{.Agda} does not matter.

```agda
module _ {o₁ h₁ o₂ h₂} (C : Precategory o₁ h₁) (D : Precategory o₂ h₂) where
  open Precategory

  FunctorCat : Precategory (o₁ ⊔ o₂ ⊔ h₁ ⊔ h₂) (o₁ ⊔ h₁ ⊔ h₂)
  FunctorCat .Ob = Functor C D
  FunctorCat .Hom F G = F => G
  FunctorCat .id = idnt
  FunctorCat ._∘_ = _∘nt_
```

All of the properties that make up a `Precategory`{.Agda} follow from
the characterisation of equalities in natural transformations: They `are
a set`{.Agda ident=isSet-Nat}, and equality of the components
`determines`{.Agda ident=Nat-path} equality of the transformation.

```agda
  FunctorCat .Hom-set F G = isSet-Nat
  FunctorCat .idr f = Nat-path λ x → D .idr _
  FunctorCat .idl f = Nat-path λ x → D .idl _
  FunctorCat .assoc f g h = Nat-path λ x → D .assoc _ _ _
```
