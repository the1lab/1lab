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


```agda
  record Section : Type (o ⊔ ℓ ⊔ o' ⊔ ℓ') where
    field
      S₀ : (x : ⌞ B ⌟) → E ʻ x
      S₁ : {x y : ⌞ B ⌟} (f : B.Hom x y) → E.Hom[ f ] (S₀ x) (S₀ y)

      S-id : {x : ⌞ B ⌟} → S₁ {x} {x} B.id ≡ E.id'
      S-∘  : {x y z : ⌞ B ⌟} (f : B.Hom y z) (g : B.Hom x y) → S₁ (f B.∘ g) ≡ S₁ f E.∘' S₁ g
```
