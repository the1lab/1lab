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
record ⟦-⟧-notation (Syn : Typeω) : Typeω where
  constructor has-⟦-⟧
  no-eta-equality
  field
    {lvl} : Level
    Sem : Type lvl
    interpret : Syn → Sem

open ⟦-⟧-notation

⟦_⟧ : ∀ {Syn : Typeω} ⦃ not : ⟦-⟧-notation Syn ⦄ → Syn → not .Sem
⟦_⟧ ⦃ not ⦄ = not .interpret
```
