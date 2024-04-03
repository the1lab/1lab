<!--
```agda
open import Cat.Diagram.Limit.Base
open import Cat.Functor.Hom.Yoneda
open import Cat.Diagram.Sieve
open import Cat.Functor.Base
open import Cat.Functor.Hom
open import Cat.Site.Base
open import Cat.Prelude

import Cat.Functor.Reasoning.Presheaf as PSh
import Cat.Reasoning as Cat

open Functor
open _=>_
```
-->

```agda
module Cat.Instances.Sheaves.Limits where
```

# Limits of sheaves {defines="limits-of-sheaves"}

This module proves that [[sheaves]] are closed under arbitrary
[[limits]], without regard for the size of the indexing category,
independently of whether we are talking about sheaves *on a site* or
functors that satisfy the sheaf condition for individual sieves.

This is a simultaneous specialisation and generalisation of the proof
that [[monadic functors create limits|limits in categories of
algebras]]. It's a specialisation in the sense that the same strategy
there works here; but it's a generalisation in the sense that sheaves
*for an individual sieve* are not the algebras for any monad.

Regardless, if we are talking about the [[topos of sheaves]], we can
obtain an abstract proof of its completeness through monadicity, without
having to do the componentwise work here.

```agda
is-sheaf₁-limit
  : ∀ {o ℓ o' ℓ'} {C : Precategory o ℓ} {D : Precategory o' ℓ'}
  → ∀ (F : Functor D (PSh ℓ C)) L ψ
  → is-limit F L ψ
  → ∀ {U} (R : Sieve C U)
  → (∀ d → is-sheaf₁ (F # d) R)
  → is-sheaf₁ L R
is-sheaf₁-limit {C = C} {D} F L ψ lim {U} R F-sheaf ps = from-is-separated₁ L sep sec where
  open Precategory C

  module lim = is-limit lim
  module F x = PSh (F .F₀ x)
  module L = PSh L

  abstract
    sep : is-separated₁ L R
    sep {x} {y} loc = unyo-path $ lim.unique₂ {x = よ₀ C U} _
      (λ f → yo-natl (sym (ψ .is-natural _ _ _ ηₚ _ $ₚ _))) (λ j → yo-natl refl)
      (λ j → yo-natl (is-sheaf₁→is-separated₁ _ _ (F-sheaf j) λ f hf →
        F.₁ j f (ψ .η j .η U y) ≡˘⟨ ψ .η j .is-natural _ _ _ $ₚ _ ⟩
        ψ .η j .η _ (L.₁ f y)   ≡˘⟨ ap (ψ .η j .η _) (loc f hf) ⟩
        ψ .η j .η _ (L.₁ f x)   ≡⟨ ψ .η j .is-natural _ _ _ $ₚ _ ⟩
        F.₁ j f (ψ .η j .η U x) ∎))

  ps' : ∀ j → Section (F # j) (map-patch (ψ .η j) ps)
  ps' j = F-sheaf j (map-patch (ψ .η j) ps) .centre

  elts : ∀ j → よ₀ C U => F .F₀ j
  elts j = yo (F .F₀ j) (ps' j .part)

  abstract
    elts-nat : ∀ {x y} (f : D .Precategory.Hom x y) → F .F₁ f ∘nt elts x ≡ elts y
    elts-nat {x} {y} f = yo-natl $ is-sheaf₁→is-separated₁ _ _ (F-sheaf y) λ g hg → sym $
      F.₁ y g (ps' y .part)                       ≡⟨ ps' y .patch g hg ⟩
      ψ .η y .η _ (ps .part g hg)                 ≡⟨ ψ .is-natural x y f ηₚ _ $ₚ ps .part g hg ⟩
      F .F₁ f .η _ (ψ .η x .η _ (ps .part g hg))  ≡˘⟨ ap (F .F₁ f .η _) (ps' x .patch g hg) ⟩
      F .F₁ f .η _ (F.₁ x g (ps' x .part))        ≡⟨ F .F₁ f .is-natural _ _ _ $ₚ _ ⟩
      F.₁ y g (F .F₁ f .η _ (ps' x .part))        ∎

  sec : Section L ps
  sec .part = unyo _ (lim.universal elts elts-nat)
  sec .patch {V} f hf =
    L ⟪ f ⟫ sec .part                         ≡˘⟨ lim.universal _ _ .is-natural _ _ _ $ₚ _ ⟩
    lim.universal elts elts-nat .η V (id ∘ f) ≡⟨ ap (lim.universal _ _ .η _) (Cat.id-comm-sym C) ⟩
    lim.universal elts elts-nat .η V (f ∘ id) ≡⟨ unext it _ id ⟩
    L ⟪ id ⟫ (ps .part f hf)                  ≡⟨ L.F-id ⟩
    ps .part f hf                             ∎
    where
      it = lim.unique₂ {x = よ₀ C V} _
        (λ f → Cat.pulll (PSh _ C) (elts-nat f))
        (λ j → Cat.pulll (PSh _ C) (lim.factors elts elts-nat))
        (λ j → yo-natl (sym (ps' j .patch f hf)) ∙ sym (yo-natr refl))
```

<!--
```agda
is-sheaf-limit
  : ∀ {o ℓ o' ℓ' ℓj} {C : Precategory o ℓ} {J : Coverage C ℓj} {D : Precategory o' ℓ'}
      {F : Functor D (PSh ℓ C)} {L} {ψ}
  → is-limit F L ψ
  → ((d : ⌞ D ⌟) → is-sheaf J (F # d))
  → is-sheaf J L
is-sheaf-limit lim dshf = from-is-sheaf₁ λ c → is-sheaf₁-limit _ _ _ lim _ λ d → to-is-sheaf₁ (dshf d) _
```
-->
