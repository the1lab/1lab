<!--
```agda
open import 1Lab.Type
```
-->

```agda
module Meta.Brackets where
```

# Brackets notation

```agda
record ⟦-⟧-notation {ℓ} (Syn : Type ℓ) : Typeω where
  constructor has-⟦-⟧
  no-eta-equality
  field
    {lvl} : Level
    Sem : Type lvl
    interpret : Syn → Sem

open ⟦-⟧-notation

⟦_⟧ : ∀ {ℓ} {Syn : Type ℓ} ⦃ not : ⟦-⟧-notation Syn ⦄ → Syn → not .Sem
⟦_⟧ ⦃ not ⦄ = not .interpret
```
