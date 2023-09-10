---
description: |
  A correspondence is established between concretely-defined coproduct
  diagrams and general colimits of discrete diagrams.
---

<!--
```agda
open import Cat.Diagram.Coproduct.Indexed
open import Cat.Instances.Shape.Terminal
open import Cat.Diagram.Colimit.Base
open import Cat.Instances.Shape.Two
open import Cat.Instances.Discrete
open import Cat.Diagram.Coproduct
open import Cat.Functor.Kan.Base
open import Cat.Prelude

open is-coproduct
open Coproduct
open Functor
open _=>_
```
-->

```agda
module Cat.Diagram.Colimit.Coproduct {o h} (C : Precategory o h) where
```

<!--
```agda
open import Cat.Reasoning C

private variable
  o' ℓ' : Level
```
-->

# Coproducts are colimits

We first establish the correspondence between binary coproducts $A + B$ and
colimits over the functor out of $\rm{Disc}(\{0,1\})$ which maps $0$
to $A$ and $1$ to $B$, dualising [[products as limits]].

```agda
is-coproduct→is-colimit
  : ∀ {x} {F : Functor 2-object-category C} {eta : F => Const x}
  → is-coproduct C (eta .η true) (eta .η false)
  → is-colimit {C = C} F x eta
is-coproduct→is-colimit {x = x} {F} {eta} coprod =
  to-is-colimitp mc λ where
    {true} → refl
    {false} → refl
  where
    module coprod = is-coproduct coprod
    open make-is-colimit

    mc : make-is-colimit F x
    mc .ψ j = eta .η j
    mc .commutes f = eta .is-natural _ _ _ ∙ idl _
    mc .universal eta _ = coprod.[ eta true , eta false ]
    mc .factors {true} eta _ = coprod.in₀∘factor
    mc .factors {false} eta _ = coprod.in₁∘factor
    mc .unique eta p other q = coprod.unique other (q true) (q false)

is-colimit→is-coproduct
  : ∀ {a b} {K : Functor ⊤Cat C}
  → {eta : 2-object-diagram a b => K F∘ !F}
  → is-lan !F (2-object-diagram a b) K eta
  → is-coproduct C (eta .η true) (eta .η false)
is-colimit→is-coproduct {a} {b} {K} {eta} colim = coprod where
  module colim = is-colimit colim

  D : Functor 2-object-category C
  D = 2-object-diagram a b

  copair
    : ∀ {y} → Hom a y → Hom b y
    → ∀ (j : Bool) → Hom (D .F₀ j) y
  copair p1 p2 true = p1
  copair p1 p2 false = p2

  copair-commutes
    : ∀ {y} {p1 : Hom a y} {p2 : Hom b y}
    → {i j : Bool}
    → (p : i ≡ j)
    → copair p1 p2 j ∘ D .F₁ p ≡ copair p1 p2 i
  copair-commutes {p1 = p1} {p2 = p2} =
      J (λ _ p → copair p1 p2 _ ∘ D .F₁ p ≡ copair p1 p2 _)
        (elimr (D .F-id))

  coprod : is-coproduct C (eta .η true) (eta .η false)
  coprod .[_,_] f g = colim.universal (copair f g) copair-commutes
  coprod .in₀∘factor {_} {p1'} {p2'} = colim.factors (copair p1' p2') copair-commutes
  coprod .in₁∘factor {_} {p1'} {p2'} = colim.factors (copair p1' p2') copair-commutes
  coprod .unique other p q = colim.unique _ _ other λ where
    true → p
    false → q

Coproduct→Colimit : ∀ {F : Functor 2-object-category C} → Coproduct C (F # true) (F # false) → Colimit F
Coproduct→Colimit coprod = to-colimit (is-coproduct→is-colimit {eta = 2-object-nat-trans _ _} (has-is-coproduct coprod))

Colimit→Coproduct : ∀ {a b} → Colimit (2-object-diagram a b) → Coproduct C a b
Colimit→Coproduct colim .coapex = Colimit.coapex colim
Colimit→Coproduct colim .in₀ = Colimit.cocone colim .η true
Colimit→Coproduct colim .in₁ = Colimit.cocone colim .η false
Colimit→Coproduct colim .has-is-coproduct =
  is-colimit→is-coproduct (Colimit.has-colimit colim)
```

## Indexed coproducts as colimits

Similarly to the product case, when $I$ is a groupoid, indexed
coproducts correspond to colimits of discrete diagrams of shape $I$.

```agda
module _ {I : Type ℓ'} (i-is-grpd : is-groupoid I) (F : I → Ob) where
  open _=>_

  Inj→Cocone : ∀ {x} → (∀ i → Hom (F i) x)
             → Disc-adjunct {C = C} {iss = i-is-grpd} F => Const x
  Inj→Cocone inj .η i = inj i
  Inj→Cocone inj .is-natural i j p =
    J (λ j p → inj j ∘ subst (Hom (F i) ⊙ F) p id ≡ id ∘ inj i)
      (elimr (transport-refl id) ∙ sym (idl _)) p

  is-indexed-coproduct→is-colimit
    : ∀ {x} {inj : ∀ i → Hom (F i) x}
    → is-indexed-coproduct C F inj
    → is-colimit (Disc-adjunct F) x (Inj→Cocone inj)
  is-indexed-coproduct→is-colimit {x = x} {inj} ic =
    to-is-colimitp mc refl
    where
      module ic = is-indexed-coproduct ic
      open make-is-colimit

      mc : make-is-colimit (Disc-adjunct F) x
      mc .ψ i = inj i
      mc .commutes {i} {j} p =
        J (λ j p → inj j ∘ subst (Hom (F i) ⊙ F) p id ≡ inj i)
          (elimr (transport-refl id))
          p
      mc .universal eta p = ic.match eta
      mc .factors eta p = ic.commute
      mc .unique eta p other q = ic.unique eta q

  is-colimit→is-indexed-coprduct
    : ∀ {K : Functor ⊤Cat C}
    → {eta : Disc-adjunct {iss = i-is-grpd} F => K F∘ !F}
    → is-lan !F (Disc-adjunct F) K eta
    → is-indexed-coproduct C F (eta .η)
  is-colimit→is-indexed-coprduct {K = K} {eta} colim = ic where
    module colim = is-colimit colim
    open is-indexed-coproduct hiding (eta)

    ic : is-indexed-coproduct C F (eta .η)
    ic .match k =
      colim.universal k
        (J (λ j p → k j ∘ subst (Hom (F _) ⊙ F) p id ≡ k _)
           (elimr (transport-refl _)))
    ic .commute =
      colim.factors _ _
    ic .unique k comm =
      colim.unique _ _ _ comm

  IC→Colimit
    : Indexed-coproduct C F
    → Colimit {C = C} (Disc-adjunct {iss = i-is-grpd} F)
  IC→Colimit ic =
    to-colimit (is-indexed-coproduct→is-colimit has-is-ic)
    where open Indexed-coproduct ic

  Colimit→IC
    : Colimit {C = C} (Disc-adjunct {iss = i-is-grpd} F)
    → Indexed-coproduct C F
  Colimit→IC colim .Indexed-coproduct.ΣF = _
  Colimit→IC colim .Indexed-coproduct.ι = _
  Colimit→IC colim .Indexed-coproduct.has-is-ic =
    is-colimit→is-indexed-coprduct (Colimit.has-colimit colim)
```
