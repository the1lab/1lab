<!--
```agda
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
