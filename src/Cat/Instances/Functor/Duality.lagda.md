<!--
```agda
open import Cat.Functor.Equivalence
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
op-functor→ .F-id = trivial!
op-functor→ .F-∘ f g = trivial!

op-functor-is-iso : is-precat-iso (op-functor→ {C = C} {D = D})
op-functor-is-iso = isom where
  open is-precat-iso
  open is-iso

  isom : is-precat-iso _
  isom .has-is-ff = is-iso→is-equiv ff where
    ff : is-iso (F₁ op-functor→)
    ff .inv nt .η = nt .η
    ff .inv nt .is-natural x y f = sym (nt .is-natural y x f)
    ff .rinv x = trivial!
    ff .linv x = trivial!
  isom .has-is-iso = is-iso→is-equiv (iso Functor.op
    (λ x → Functor-path (λ x → refl) (λ x → refl)) (λ x → F^op^op≡F))
```

This means, in particular, that it is an adjoint equivalence:

```agda
op-functor-is-equiv : is-equivalence (op-functor→ {C = C} {D = D})
op-functor-is-equiv = is-precat-iso→is-equivalence op-functor-is-iso

op-functor← : Functor Cat[ C ^op , D ^op ] (Cat[ C , D ] ^op)
op-functor← = is-equivalence.F⁻¹ op-functor-is-equiv

op-functor←→ : op-functor← {C = C} {D = D} F∘ op-functor→ ≡ Id
op-functor←→ {C = C} {D = D} = Functor-path (λ _ → refl) λ f → ext λ x →
  Regularity.precise! ((D.id D.∘ f .η x) D.∘ D.id ≡⟨ cat! D ⟩ f .η x ∎)
  where
    module D = Cat.Reasoning D
```
