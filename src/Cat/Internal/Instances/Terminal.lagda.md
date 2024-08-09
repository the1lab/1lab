---
description: |
  The terminal internal category.
---
<!--
```agda
open import Cat.Diagram.Terminal
open import Cat.Prelude

open import Cat.Internal.Instances.Discrete

import Cat.Internal.Base
import Cat.Reasoning
```
-->
```agda
module Cat.Internal.Instances.Terminal
  {o ℓ} (C : Precategory o ℓ)
  (term : Terminal C)
  where
```

<!--
```agda
open Cat.Reasoning C
open Cat.Internal.Base C
open Terminal term
open Internal-hom
open Internal-functor
```
-->

# The terminal internal category {defines="terminal-internal-category"}

If $\cC$ has a [[terminal object]] $\top$, then we can define an internal
analog to the [[terminal category]] as the [[discrete internal category]]
on $\top$.

```agda
⊤Cati : Internal-cat
⊤Cati = Disci C top

module ⊤Cati = Internal-cat ⊤Cati
```

Like its external counterpart, there exists a unique internal functor
from any internal category to $\top$.

```agda
module _ {ℂ : Internal-cat} where
  private module ℂ = Internal-cat ℂ

  !Fi : Internal-functor ℂ ⊤Cati
  !Fi .Fi₀ _ = !
  !Fi .Fi₁ _ .ihom = !
  !Fi .Fi₁ _ .has-src = idl _
  !Fi .Fi₁ _ .has-tgt = idl _
  !Fi .Fi-id = trivial!
  !Fi .Fi-∘ f g = trivial!
  !Fi .Fi₀-nat x σ = sym (!-unique _)
  !Fi .Fi₁-nat f σ =
    Internal-hom-pathp _ _ (sym (!-unique _))

  !Fi-unique : ∀ {F : Internal-functor ℂ ⊤Cati} → F ≡ !Fi
  !Fi-unique =
    Internal-functor-path
      (λ _ → sym (!-unique _))
      (λ f → Internal-hom-pathp _ _ (sym (!-unique _)))
```

Conversely, functors out of the terminal internal category are determined
by their behaviour on a single global element.

```agda
  !Consti : Hom top ℂ.C₀ → Internal-functor ⊤Cati ℂ
  !Consti x = Consti (x ∘ !) λ σ → pullr (sym (!-unique (! ∘ σ)))

  !Consti-η
    : ∀ (F G : Internal-functor ⊤Cati ℂ)
    → (∀ {Γ} → F .Fi₀ (! {Γ}) ≡ G .Fi₀ (! {Γ}))
    → F ≡ G
  !Consti-η F G p =
    Internal-functor-path
      (λ x → ap (F .Fi₀) (sym (!-unique x)) ∙ p ∙ ap (G .Fi₀) (!-unique x))
      (λ {_} {x} {y} f → ℂ.begini
        F .Fi₁ f             ℂ.≡i⟨ apd (λ i f → F .Fi₁ {x = !-unique x (~ i)} {y = !-unique y (~ i)} f) (Internal-hom-pathp _ _ (sym (!-unique (f .ihom)))) ⟩
        F .Fi₁ (⊤Cati.idi !) ℂ.≡i⟨ F .Fi-id ⟩
        ℂ.idi (F .Fi₀ !)     ℂ.≡i⟨ (λ i → ℂ.idi (p i)) ⟩
        ℂ.idi (G .Fi₀ !)     ℂ.≡i˘⟨ G .Fi-id ⟩
        G .Fi₁ (⊤Cati.idi !) ℂ.≡i˘⟨ apd (λ i f → G .Fi₁ {x = !-unique x (~ i)} {y = !-unique y (~ i)} f) (Internal-hom-pathp _ _ (sym (!-unique (f .ihom)))) ⟩
        G .Fi₁ f             ∎)
```
