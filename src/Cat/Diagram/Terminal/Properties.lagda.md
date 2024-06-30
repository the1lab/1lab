---
description: |
  Properties of terminal objects.
---
<!--
```agda
open import Cat.Instances.Shape.Terminal
open import Cat.Diagram.Terminal
open import Cat.Functor.Adjoint
open import Cat.Prelude

import Cat.Functor.Reasoning
import Cat.Reasoning
```
-->
```agda
module Cat.Diagram.Terminal.Properties where
```

# Properties of terminal objects

<!--
```agda
module _ {o ℓ} (C : Precategory o ℓ) where
  open Cat.Reasoning C
```
-->

## As adjoints

A category $\cC$ has a terminal object if and only if the unique functor
$! : \cC \to \top$ into the [[terminal category]] has a [[right adjoint]].

We will start with the forward direction. Suppose that there is some
$R$ that is right adjoint to $! : \cC \to \top$.

```agda
  Adjoint→Terminal
    : ∀ {R : Functor ⊤Cat C}
    → !F ⊣ R
    → Terminal C
  Adjoint→Terminal {R = R} adj = terminal where
    module R = Cat.Functor.Reasoning R
    open _⊣_ adj
```

Note that $R$ picks out a single object $R(tt)$ in $\cC$, and that the
unit of the adjunction gives a map $\cC(X, R(tt))$ for any arbitrary
$X : \cC$.

```agda
    terminal : Terminal C
    terminal .Terminal.top = R.₀ tt
    terminal .Terminal.has⊤ X .centre = η _
```

Moreover, this map is unique: this follows from a quick bit of algebra,
combined with the fact that the terminal category only has a single map.

```agda
    terminal .Terminal.has⊤ X .paths f =
      η X                           ≡⟨ introl R.F-id ⟩
      (R.₁ tt ∘ η X)                ≡⟨ R.shuffler (sym (unit.is-natural _ _ _)) ⟩
      (R.₁ (ε tt) ∘ η (R.₀ tt)) ∘ f ≡⟨ eliml zag ⟩
      f                             ∎
```

On to the reverse direction. Suppose that $\cC$ has a terminal object.
We shall show that the constant functor $\Delta_{\top}$ is a right
adjoint to $!$.

```agda
  Terminal→Adjoint
    : (terminal : Terminal C)
    → (!F {A = C}) ⊣ const! (Terminal.top terminal)
  Terminal→Adjoint terminal = adj where
    open Terminal terminal
```

The unit of the adjunction is simply the unique map into the terminal
object, and the counit is the unique map in the terminal category!

```agda
    adj : !F ⊣ const! top
    adj ._⊣_.unit = NT (λ _ → !) (λ _ _ _ → !-unique₂ _ _)
    adj ._⊣_.counit = NT (λ _ → tt) (λ _ _ _ → refl)
    adj ._⊣_.zig = refl
    adj ._⊣_.zag = !-unique₂ _ _
```
