```agda
open import Cat.Displayed.Cartesian
open import Cat.Instances.Discrete
open import Cat.Instances.Functor
open import Cat.Displayed.Base
open import Cat.Prelude

module Cat.Displayed.Instances.Family {o h} (C : Precategory o h) where
```

<!--
```
open import Cat.Reasoning C
open Displayed
open Functor
open _=>_
```
-->

# The family fibration

We can canonically treat any `Precategory`{.Agda} $\mathcal{C}$ as being
displayed over `Sets`{.Agda}, regardless of the size of the object- and
Hom-spaces of $\mathcal{C}$. 

The collection of displayed object over $S$ is given by the space of
functors $[\mathrm{Disc}(S),C]$, regarding $S$ as a discrete category.
This is essentially an $S$-indexed family of objects of $C$, hence the
name "family fibration".

```agda
Family : ∀ {ℓ} → Displayed (Sets ℓ) _ _
Family .Ob[_] S = Functor (Disc′ S) C
```

Given a map $f : A \to B$ in `Sets`{.Agda}, and functors $F : [A,C]$ and
$G : [B,C]$, we define the collection of displayed maps to be the set of
all natural transformations $F \To f*G$, where $f*G$ is the
precomposition of $f$ `regarded as a functor`{.Agda ident=liftDisc}
between discrete categories. Since `natural transformations form a
Set`{.Agda ident=isSet-Nat}, we're clear to take this as the definition.

```agda
Family .Hom[_] {_ , aset} {_ , bset} f F G = 
  F => (G F∘ liftDisc f)
Family .Hom[_]-set f x y = isSet-Nat
```

The identity and composition operations are given by the identity and
composite natural transformations; However, we can not reuse the
existing implementations because $\mathrm{id}*F$ is not the same term as
$F$.

```agda
Family .id′ = NT (λ x → id) λ x y f → id-comm-sym
Family ._∘′_ {a = A} {x = X} {Y} {Z} {F} {G} f g = NT (λ x → η f _ ∘ η g _) comm
  where abstract
    comm : ∀ x y (h : x ≡ y) 
         → (f .η _ ∘ g .η y) ∘ F₁ X h 
         ≡ F₁ (Z F∘ liftDisc {A = A} _) h ∘ f .η _ ∘ g .η  _
    comm x y h =
      (f .η _ ∘ g .η y) ∘ F₁ X h                          ≡⟨ extendr (g .is-natural _ _ _) ⟩
      (f .η _ ∘ F₁ (Y F∘ liftDisc {A = A} _) h) ∘ g .η x  ≡˘⟨ pulll (sym (f .is-natural _ _ _)) ⟩
      F₁ (Z F∘ liftDisc {A = A} _) h ∘ f .η _ ∘ g .η  _   ∎

Family .idr′ _ = Nat-path λ x → idr _
Family .idl′ _ = Nat-path λ x → idl _
Family .assoc′ _ _ _ = Nat-path λ x → assoc _ _ _
```

The family fibration is `a Cartesian fibration`{.Agda}. This is because
giving a Cartesian lift for a natural transformation $u \To
m*f*y'$ entails giving a natural transformation $u \To (f\circ
m)*y'$; But this is exactly the natural transformation we started with!

```agda
open CartesianFibration
open CartesianLift
open Cartesian

isCartesian-Family : ∀ {ℓ} → CartesianFibration (Family {ℓ = ℓ})
isCartesian-Family = iscart where
  cart : ∀ {x y : Set _} (f : x .fst → y .fst) 
           (y′ : Functor (Disc′ y) C)
       → Cartesian Family f idnt
  cart f y′ .universal m nt = NT (η nt) (is-natural nt)
  cart f y′ .commutes m h′ = Nat-path λ x → idl _
  cart f y′ .unique m′ p = Nat-path λ x → sym (idl _) ∙ ap (λ e → η e x) p

  iscart : CartesianFibration Family
  iscart .has-lift f y′ .x′ = y′ F∘ liftDisc f
  iscart .has-lift f y′ .lifting = idnt
  iscart .has-lift {x = x} {y} f y′ .cartesian = cart {x = x} {y} f y′
```
