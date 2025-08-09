<!--
```agda
open import Cat.Diagram.Terminal
open import Cat.Displayed.Base
open import Cat.Prelude

import Cat.Displayed.Reasoning
```
-->

```agda
module Cat.Displayed.Diagram.Total.Terminal
  {o ℓ o' ℓ'} {B : Precategory o ℓ} (E : Displayed B o' ℓ')
  where
```

<!--
```agda
private
  module E = Cat.Displayed.Reasoning E
  module B = Precategory B
```
-->

# Total terminal objects

:::{.definition #total-terminal-object}
If $\cD \liesover \cB$ is a [[displayed category]] over a base $\cB$
admitting a [[terminal object]] $\top$ we say that an object $\top'
\liesover \top$ is a **total terminal object**, if, for every $X'
\liesover X$, there exists a unique morphism $!' : X' \to_! \top'$
displayed over $!$.
:::

```agda
record is-terminal-over {top} (term : is-terminal B top) (top' : E ʻ top) : Type (o ⊔ o' ⊔ ℓ') where
  open Terminal {C = B} record{ has⊤ = term } hiding (top)
  field
    !'        : {y : ⌞ B ⌟} {y' : E ʻ y} → E.Hom[ ! ] y' top'
    !-unique' : {y : ⌞ B ⌟} {y' : E ʻ y} (h : E.Hom[ ! ] y' top') → !' ≡ h

  opaque
    !ₚ : ∀ {y} {m : B.Hom y top} {y' : E ʻ y} → E.Hom[ m ] y' top'
    !ₚ {m = m} = E.hom[ !-unique m ] !'

    abstract
      !ₚ-unique : ∀ {y} {m : B.Hom y top} {y' : E ʻ y} (h : E.Hom[ m ] y' top') → !ₚ ≡ h
      !ₚ-unique {m = m} {y'} = J
        (λ m p → (h : E.Hom[ m ] y' top') → E.hom[ p ] !' ≡ h)
        (λ h → from-pathp (!-unique' h))
        (!-unique m)

  abstract
    !'-unique₂
      : ∀ {y} {m m' : B.Hom y top} {y' : E ʻ y} {h : E.Hom[ m ] y' top'} {h' : E.Hom[ m' ] y' top'}
      → {p : m ≡ m'}
      → h E.≡[ p ] h'
    !'-unique₂ {h = h} {h' = h'} = to-pathp (sym (!ₚ-unique _) ∙ !ₚ-unique _)

record TerminalP (t : Terminal B) : Type (o ⊔ o' ⊔ ℓ') where
  open Terminal t
  field
    top'  : E ʻ top
    has⊤' : is-terminal-over has⊤ top'
  open is-terminal-over has⊤' public
```
