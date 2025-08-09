<!--
```agda
open import Cat.Displayed.Instances.Identity
open import Cat.Displayed.Functor
open import Cat.Displayed.Base
open import Cat.Prelude
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
    field
      S₀ : (x : ⌞ B ⌟) → E ʻ x
      S₁ : {x y : ⌞ B ⌟} (f : B.Hom x y) → E.Hom[ f ] (S₀ x) (S₀ y)

      S-id : {x : ⌞ B ⌟} → S₁ {x} {x} B.id ≡ E.id'
      S-∘  : {x y z : ⌞ B ⌟} (f : B.Hom y z) (g : B.Hom x y) → S₁ (f B.∘ g) ≡ S₁ f E.∘' S₁ g
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
