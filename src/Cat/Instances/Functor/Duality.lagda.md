<!--
```agda
open import Cat.Functor.Equivalence
open import Cat.Functor.Equivalence.Path
open import Cat.Instances.Functor
open import Cat.Prelude

import Cat.Reasoning
```
-->

```agda
module Cat.Instances.Functor.Duality where
```

# Duality of functor categories

The duality involution $\cC\op$ on categories extends to a "duality
involution" $F\op$ on _functors_. However, since this changes the type
of the functor --- the dual of $F : \cC \to \cD$ is $F\op : \cC
\to \cD$ --- it does not represent an involution on functor
categories; Rather, it is an equivalence $(-)\op : [\cC,\cD]\op
\cong [\cC\op,\cD\op]$.

<!--
```agda
private variable
  o ℓ : Level
  C D : Precategory o ℓ

open Functor
open _=>_
```
-->

```agda
op-functor→ : Functor (Cat[ C , D ] ^op) Cat[ C ^op , D ^op ]
op-functor→ .F₀ = Functor.op
op-functor→ .F₁ nt .η = nt .η
op-functor→ .F₁ nt .is-natural x y f = sym (nt .is-natural y x f)
op-functor→ .F-id    = ext λ i → refl
op-functor→ .F-∘ f g = ext λ i → refl

op-functor-is-iso : is-precat-iso (op-functor→ {C = C} {D = D})
op-functor-is-iso = isom where
  open is-precat-iso
  open is-iso

  isom : is-precat-iso _
  isom .has-is-ff = is-iso→is-equiv ff where
    ff : is-iso (F₁ op-functor→)
    ff .from nt .η = nt .η
    ff .from nt .is-natural x y f = sym (nt .is-natural y x f)
    ff .rinv x = ext λ _ → refl
    ff .linv x = ext λ _ → refl
  isom .has-is-iso = is-iso→is-equiv $ iso unopF
    (λ x → Functor-path (λ x → refl) (λ x → refl))
    (λ x → Functor-path (λ x → refl) (λ x → refl))
```

This induces a [[path between precategories]]

```agda
op-functor-path : Cat[ C , D ] ^op ≡ Cat[ C ^op , D ^op ]
op-functor-path = Precategory-path op-functor→ op-functor-is-iso
```

and an [[equivalence of precategories]]

```agda
op-functor-is-equiv : is-equivalence (op-functor→ {C = C} {D = D})
op-functor-is-equiv = is-precat-iso→is-equivalence op-functor-is-iso

op-functor← : Functor Cat[ C ^op , D ^op ] (Cat[ C , D ] ^op)
op-functor← = is-equivalence.F⁻¹ op-functor-is-equiv

op-functor←→ : op-functor← {C = C} {D = D} F∘ op-functor→ ≡ Id
op-functor←→ {C = C} {D = D} = Functor-path (λ _ → Functor-path (λ _ → refl) (λ _ → refl)) λ f →
  Nat-pathp _ _ λ x →
    let
      module D = Cat.Reasoning D
    in Regularity.precise! ((D.id D.∘ f .η x) D.∘ D.id ≡⟨ cat! D ⟩ f .η x ∎)
```

As an equivalence of _endofunctor categories_ $[\cC,\cC]\op \cong
[\cC\op,\cC\op]$ this maps the identity functor `Id`.{.Agda} on $\cC$ to
the corresponding one on $\cC\op$.

```agda
op[Id]≡Id : Functor.op (Id {C = C}) ≡ Id
op[Id]≡Id {C = C} = Functor-path (λ _ → refl) (λ _ → refl)
```