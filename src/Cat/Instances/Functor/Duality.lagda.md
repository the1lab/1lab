```agda
open import Cat.Functor.Equivalence
open import Cat.Instances.Functor
open import Cat.Functor.Base
open import Cat.Prelude

import Cat.Reasoning

module Cat.Instances.Functor.Duality where
```

# Duality of functor categories

The duality involution $\ca{C}\op$ on categories extends to a "duality
involution" $F\op$ on _functors_. However, since this changes the type
of the functor --- the dual of $F : \ca{C} \to \ca{D}$ is $F^op : \ca{C}
\to \ca{D}$ --- it does not represent an involution on functor
categories; Rather, it is an equivalence $(-)\op : [\ca{C},\ca{D}]\op
\cong [\ca{C}\op,\ca{D}\op]$.

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
op-functor→ .F-id = Nat-path (λ x → refl)
op-functor→ .F-∘ f g = Nat-path λ x → refl

op-functor-is-iso : is-precat-iso (op-functor→ {C = C} {D = D})
op-functor-is-iso = isom where
  open is-precat-iso
  open is-iso

  isom : is-precat-iso _
  isom .has-is-ff = is-iso→is-equiv ff where
    ff : is-iso (F₁ op-functor→)
    ff .inv nt .η = nt .η
    ff .inv nt .is-natural x y f = sym (nt .is-natural y x f)
    ff .rinv x = Nat-path λ x → refl
    ff .linv x = Nat-path λ x → refl
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
op-functor←→ {C = C} {D = D} = Functor-path (λ x → refl) λ {X} {Y} f → Nat-path λ x →
  (_ D.∘ f .η x) D.∘ _ ≡⟨ D.elimr (lemma {Y = Y}) ⟩
  _ D.∘ f .η x         ≡⟨ D.eliml (lemma {Y = X}) ⟩
  f .η x               ∎
  where
    module D = Cat.Reasoning D
    module C = Cat.Reasoning C

    lemma : ∀ {Y : Functor C D} {x}
      → coe0→1 (λ i → D.Hom (F₀ Y (transp (λ j → C.Ob) i x)) (F₀ Y (transp (λ j → C.Ob) i x))) D.id
      ≡ D.id
    lemma {Y} {x} =
      from-pathp {A = λ i → D.Hom (F₀ Y (transp (λ j → C.Ob) i x)) (F₀ Y (transp (λ j → C.Ob) i x))}
        λ i →
          hcomp (λ { j (i = i0) → D.id
                   ; j (i = i1) → transport-filler (λ j → D.Hom (F₀ Y x) (F₀ Y x)) D.id (~ j)
                   })
          (coe0→i (λ j → D.Hom (F₀ Y (transp (λ j → C.Ob) (i ∨ j) x)) (F₀ Y (transp (λ j → C.Ob) (i ∨ j) x))) i D.id)

module _ {o ℓ o′ ℓ′} {C : Precategory o ℓ} {D : Precategory o′ ℓ′} {F G : Functor C D} where
  private
    module CD = Cat.Reasoning Cat[ C , D ]
    module CopDop = Cat.Reasoning Cat[ C ^op , D ^op ]

  op-natural-iso : F CD.≅ G → (Functor.op F) CopDop.≅ (Functor.op G)
  op-natural-iso isom = CopDop.make-iso (_=>_.op isom.from) (_=>_.op isom.to)
    (Nat-path (λ x → ap (λ e → e .η x) isom.invl))
    (Nat-path λ x → ap (λ e → e .η x) isom.invr)
    where module isom = CD._≅_ isom
```
