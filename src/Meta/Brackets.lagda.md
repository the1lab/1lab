<!--
```agda
open import 1Lab.Type
```
-->

```agda
module Meta.Brackets where
```

# Semantic bracket notation

In many of our developments (primarily, but not limited to, those in
logic), we have a notion of a type $T$ being a *syntactic presentation*
for some other, *semantic*, type $S$. In keeping with convention, we
want to overload the notation $\sem{e}$ to mean "the semantic value of
$e$." This can be achieved with a simple notation class:

```agda
record ⟦⟧-notation {ℓ} (A : Type ℓ) : Typeω where
  constructor brackets
  field
    {lvl} : Level
    Sem : Type lvl
    ⟦_⟧ : A → Sem

open ⟦⟧-notation ⦃...⦄ using (⟦_⟧) public
{-# DISPLAY ⟦⟧-notation.⟦_⟧ _ x = ⟦ x ⟧ #-}
```
