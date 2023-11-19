<!--
```agda
open import 1Lab.Type
```
-->

```agda
module Meta.Brackets where
```

```agda
record ⟦⟧-notation {ℓ} (A : Type ℓ) : Typeω where
  constructor brackets
  field
    {lvl} : Level
    Sem : Type lvl
    ⟦_⟧ : A → Sem

open ⟦⟧-notation ⦃...⦄ public
{-# DISPLAY ⟦⟧-notation.⟦_⟧ f x = ⟦ x ⟧ #-}
```
