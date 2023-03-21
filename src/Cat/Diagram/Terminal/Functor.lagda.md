```agda
open import Cat.Diagram.Terminal
open import Cat.Prelude

import Cat.Reasoning
import Cat.Functor.Reasoning as Func

module Cat.Diagram.Terminal.Functor where
```

# Terminal object preserving functors

A functor $F : \cC \to \cD$ **preserves terminal objects** if, for every
terminal object $\top$ in $\cC$, $F \top$ is also a terminal object in
$\cD$.

<!--
```agda
module _ {o ℓ o' ℓ'} {C : Precategory o ℓ} {D : Precategory o' ℓ'} where
  private
    module C = Cat.Reasoning C
    module D = Cat.Reasoning D
    open Functor
```
-->

```agda
  preserves-terminal : Functor C D → Type _
  preserves-terminal F =
    ∀ {x} → is-terminal C x → is-terminal D (F .F₀ x)
```

## Preservation of chosen terminal objects

If $\cC$ and $\cD$ are both equipped with chosen terminal objects, and
$F$ preserves these chosen objects, then $F$ preserves terminal objects.

```agda
  module _ (C-term : Terminal C) (D-term : Terminal D) (F : Functor C D) where
    private
      module C-term = Terminal C-term
      module D-term = Terminal D-term

    preserves-chosen-terminal→preserves-terminal
      : D.is-invertible (D-term.! {F .F₀ C-term.top})
      → preserves-terminal F
```

<details>
<summary>The proof is not every interesting, so we omit it.
</summary>

```agda
    preserves-chosen-terminal→preserves-terminal apex-iso {t} term = preserved where
      module term = is-terminal C term
      module apex-iso = D.is-invertible apex-iso

      preserved : is-terminal D (F .F₀ t)
      preserved x .centre =
        F .F₁ term.! D.∘ apex-iso.inv D.∘ D-term.!
      preserved x .paths f =
        F .F₁ term.! D.∘ apex-iso.inv D.∘ D-term.! ≡⟨ ap₂ D._∘_ refl (D.pushr (D-term.!-unique (D-term.! D.∘ F .F₁ C-term.! D.∘ f)) ∙ D.eliml apex-iso.invr) ⟩
        F .F₁ term.! D.∘ F .F₁ C-term.! D.∘ f      ≡⟨ D.cancell (Func.annihilate F (term.!-unique₂ _ _)) ⟩
        f ∎
```
</details>
