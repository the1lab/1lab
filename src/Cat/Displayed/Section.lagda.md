<!--
```agda
open import Cat.Displayed.Instances.Identity
open import Cat.Displayed.Functor
open import Cat.Displayed.Base
open import Cat.Prelude

import Cat.Displayed.Reasoning as Disp
import Cat.Reasoning as Cat
```
-->

```agda
module Cat.Displayed.Section where
```

# Sections of a displayed category

<!--
```agda
module _ {o ℓ o' ℓ'} {B : Precategory o ℓ} (E : Displayed B o' ℓ') where
  private
    module B = Precategory B
    module E = Displayed E
```
-->

:::{.definition #section-of-a-displayed-category}
A **section** of a [[displayed category]] $\cE \liesover \cB$ consists
of a functorial assignment of objects $S_0(X) \liesover X$ and morphisms
$S_1(f) : S_0(X) \to_f S_0(Y)$.
:::

In other words, a section of a displayed category is a [[vertical
functor]] from the [[identity bifibration]] of $\cB$ to $\cD$. We
restate the definition in elementary terms to drop the additional unit
arguments.

```agda
  record Section : Type (o ⊔ ℓ ⊔ o' ⊔ ℓ') where
    no-eta-equality
    field
      S₀ : ∀ x → E ʻ x
      S₁ : ∀ {x y} (f : B.Hom x y) → E.Hom[ f ] (S₀ x) (S₀ y)

      S-id : ∀ {x} → S₁ {x} {x} B.id ≡ E.id'
      S-∘
        : ∀ {x y z} (f : B.Hom y z) (g : B.Hom x y)
        → S₁ (f B.∘ g) ≡ S₁ f E.∘' S₁ g
```

<details>
<summary>The equivalence with vertical functors from the identity
bifibration is a trivial matter of data repackaging.</summary>

```agda
  open Section
  open Displayed-functor

  unquoteDecl Section-path = declare-record-path Section-path (quote Section)

  section→vertical-functor : Section → Vertical-functor (IdD B) E
  section→vertical-functor s .F₀' _ = s .S₀ _
  section→vertical-functor s .F₁' _ = s .S₁ _
  section→vertical-functor s .F-id' = s .S-id
  section→vertical-functor s .F-∘' = s .S-∘ _ _

  section≃vertical-functor : Section ≃ Vertical-functor (IdD B) E
  section≃vertical-functor .fst = section→vertical-functor
  section≃vertical-functor .snd = is-iso→is-equiv is where
    is : is-iso section→vertical-functor
    is .is-iso.from f .S₀ _ = f .F₀' _
    is .is-iso.from f .S₁ _ = f .F₁' _
    is .is-iso.from f .S-id = f .F-id'
    is .is-iso.from f .S-∘ _ _ = f .F-∘'
    is .is-iso.rinv f = Displayed-functor-pathp refl (λ _ → refl) λ _ → refl
    is .is-iso.linv s = Section-path refl refl
```
</details>

<!--
```agda
module _ {o ℓ o' ℓ'} {B : Precategory o ℓ} {E : Displayed B o' ℓ'} where
  private
    module E = Displayed E
    module B = Cat B

  instance
    Funlike-Section : Funlike (Section E) B.Ob λ x → E.Ob[ x ]
    Funlike-Section = record { _·_ = λ S e → S .Section.S₀ e }
```
-->

We can also specialise the notion of [[vertical natural transformation]]
to work with sections instead.

```agda
  record _=>s_ (P Q : Section E) : Type (o ⊔ ℓ ⊔ ℓ') where
    no-eta-equality

    private
      module P = Section P
      module Q = Section Q

    field
      map : ∀ x → E.Hom[ B.id ] (P · x) (Q · x)
      com : ∀ x y (f : B.Hom x y)
          → map y E.∘' P.S₁ f E.≡[ B.id-comm-sym ] Q.S₁ f E.∘' map x
```

<!--
```agda
  {-# INLINE _=>s_.constructor #-}

  private unquoteDecl eqv = declare-record-iso eqv (quote _=>s_)

  instance
    H-Level-Natₛ : ∀ {P Q n} → H-Level (P =>s Q) (2 + n)
    H-Level-Natₛ = basic-instance 2 (Iso→is-hlevel 2 eqv (hlevel 2))

    Extensional-Natₛ
      : ∀ {P Q ℓr} ⦃ _ : Extensional (∀ x → E.Hom[ B.id ] (P · x) (Q · x)) ℓr ⦄
      → Extensional (P =>s Q) ℓr
    Extensional-Natₛ = injection→extensional! (λ p → Iso.injective eqv (p ,ₚ prop!)) auto

module _ {o ℓ o' ℓ'} {B : Precategory o ℓ} (E : Displayed B o' ℓ') where
  open Disp E
  private
    module B = Cat B

  open Precategory
  open Section
  open _=>s_

  Sections : Precategory (o ⊔ o' ⊔ ℓ ⊔ ℓ') (o ⊔ ℓ ⊔ ℓ')
  Sections .Ob          = Section E
  Sections .Hom         = _=>s_
  Sections .Hom-set X Y = hlevel 2
  Sections .id      = record { map = λ x → id' ; com = λ x y f → to-pathp[] id-comm[] }
  Sections ._∘_ {S} {T} {U} f g = record
    { map = λ x     → hom[ B.idl B.id ] (f .map x ∘' g .map x)
    ; com = λ x y h → begin[]
      hom[] (f .map y ∘' g .map y) ∘' S .S₁ h ≡[]⟨ unwrap _ ⟩∘'⟨refl ⟩
      (f .map y ∘' g .map y) ∘' S .S₁ h       ≡[]⟨ pullr[]   _ (g .com x y h) ⟩
      f .map y ∘' T .S₁ h ∘' g .map x         ≡[]⟨ extendl[] _ (f .com x y h) ⟩
      U .S₁ h ∘' f .map x ∘' g .map x         ≡[]⟨ refl⟩∘'⟨ wrap _ ⟩
      U .S₁ h ∘' hom[] (f .map x ∘' g .map x) ∎[]
    }
  Sections .idr f       = ext λ x → idr[]
  Sections .idl f       = ext λ x → idl[]
  Sections .assoc f g h = ext λ x → smashr _ _
    ∙ ap hom[] (from-pathp⁻ (assoc' _ _ _))
    ∙ sym (smashl _ _ ∙ sym (weave _ _ _ (to-pathp⁻ refl)))
```
-->
