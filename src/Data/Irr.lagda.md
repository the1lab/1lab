<!--
```agda
open import 1Lab.HLevel.Closure
open import 1Lab.Path
open import 1Lab.Type

open import Meta.Idiom
```
-->

```agda
module Data.Irr where
```

# Strict propositional truncations

<!--
```agda
private variable
  ℓ : Level
  A : Type ℓ
```
-->

In Agda, it's possible to turn any type into one that *definitionally*
has at most one inhabitant. We do this using a record containing an
irrelevant field.

```agda
record Irr {ℓ} (A : Type ℓ) : Type ℓ where
  constructor forget
  field
    .lower : A
```

The most important property of this type is that, given any $x, y$ in
$\operatorname{Irr}(A)$, the constant path `refl`{.Agda} checks at type
$x \is y$.

```agda
instance
  H-Level-Irr : ∀ {n} → H-Level (Irr A) (suc n)
  H-Level-Irr {n} = prop-instance λ _ _ → refl
```

<!--
```agda
instance
  make-irr : ∀ {ℓ} {A : Type ℓ} ⦃ _ : A ⦄ → Irr A
  make-irr ⦃ x ⦄ = forget x
  {-# INCOHERENT make-irr #-}

  Map-Irr : Map (eff Irr)
  Map-Irr = record { map = λ where f (forget x) → forget (f x) }

  Idiom-Irr : Idiom (eff Irr)
  Idiom-Irr = record { pure = λ x → forget x ; _<*>_ = λ where (forget f) (forget x) → forget (f x) }
```
-->
