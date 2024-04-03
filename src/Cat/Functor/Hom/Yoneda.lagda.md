<!--
```agda
open import Cat.Functor.Base
open import Cat.Functor.Hom
open import Cat.Prelude

import Cat.Functor.Reasoning.Presheaf as PSh

open Functor
open _=>_
```
-->

```agda
module Cat.Functor.Hom.Yoneda where
```

# The Yoneda lemma

<!--
```agda
module _ {o ℓ} {C : Precategory o ℓ} (A : Functor (C ^op) (Sets ℓ)) where
  private module A = PSh A using (expand ; elim)
  open Precategory C
```
-->

```agda
  yo : ∀ {U} → A ʻ U → よ₀ C U => A
  yo a .η i h = A ⟪ h ⟫ a
  yo a .is-natural x y f = ext λ h → A.expand refl

  unyo : ∀ {U} → よ₀ C U => A → A ʻ U
  unyo h = h .η _ id

  yo-is-equiv : ∀ {U} → is-equiv (yo {U})
  yo-is-equiv = is-iso→is-equiv λ where
    .is-iso.inv  n → unyo n
    .is-iso.rinv x → ext λ i h →
      yo (unyo x) .η i h ≡˘⟨ x .is-natural _ _ _ # _ ⟩
      x .η i (id ∘ h)    ≡⟨ ap (x .η i) (idl h) ⟩
      x .η i h           ∎
    .is-iso.linv x → A.elim refl
```

<!--
```agda
module _ {o ℓ} {C : Precategory o ℓ} {A : Functor (C ^op) (Sets ℓ)} where
  private module A = PSh A
  open Precategory C
```
-->

```agda
  unyo-path : ∀ {U : ⌞ C ⌟} {x y : A ʻ U} → yo {C = C} A x ≡ yo A y → x ≡ y
  unyo-path {x = x} {y} p =
    x          ≡⟨ A.intro refl ⟩
    A ⟪ id ⟫ x ≡⟨ unext p _ id ⟩
    A ⟪ id ⟫ y ≡⟨ A.elim refl ⟩
    y          ∎

  yo-natr
    : ∀ {U V} {x : A ʻ U} {h : Hom V U} {y}
    → A ⟪ h ⟫ x ≡ y
    → yo A x ∘nt よ₁ C h ≡ yo A y
  yo-natr p = ext λ i f → A.expand refl ∙ A.ap p

  yo-natl
    : ∀ {B : Functor (C ^op) (Sets ℓ)} {U} {x : A ʻ U} {y : B ʻ U} {h : A => B}
    → h .η U x ≡ y → h ∘nt yo {C = C} A x ≡ yo B y
  yo-natl {B = B} {h = h} p = ext λ i f → h .is-natural _ _ _ # _ ∙ PSh.ap B p
```
