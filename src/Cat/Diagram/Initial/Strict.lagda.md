<!--
```agda
open import Cat.Diagram.Subterminal
open import Cat.Diagram.Initial
open import Cat.Prelude

import Cat.Reasoning
```
-->

```agda
module Cat.Diagram.Initial.Strict where
```

<!--
```agda
module _ {o h} (C : Precategory o h) where
  open Cat.Reasoning C
  open Initial
```
-->

# Strict initial objects {defines="strict-initial-object strict-initial"}

An [[initial object]] is said to be *[strict]* if every morphism into it is an *iso*morphism.
This is a categorical generalization of the fact that if one can write a function $X \to \bot$ then $X$ must itself be empty.

This is an instance of the more general notion of [van Kampen colimits].

[strict]: https://ncatlab.org/nlab/show/strict+initial+object
[van Kampen colimits]: https://ncatlab.org/nlab/show/van+Kampen+colimit


```agda
  is-strict-initial : Initial C → Type _
  is-strict-initial i = ∀ x → (f : Hom x (i .bot)) → is-invertible f

  record Strict-initial : Type (o ⊔ h) where
    field
      initial : Initial C
      has-is-strict : is-strict-initial initial
```

Strictness is a property of, not structure on, an initial object.

```agda
  is-strict-initial-is-prop : ∀ i → is-prop (is-strict-initial i)
  is-strict-initial-is-prop i = hlevel 1
```

As maps out of initial objects are unique, it suffices to show that
every map $\text{!`} \circ f = \id$ for every $f : X \to \bot$ to establish that $\bot$ is a
strict initial object.

```agda
  make-is-strict-initial
    : (i : Initial C)
    → (∀ x → (f : Hom x (i .bot)) → (¡ i) ∘ f ≡ id)
    → is-strict-initial i
  make-is-strict-initial i p x f =
    make-invertible (¡ i) (¡-unique₂ i (f ∘ ¡ i) id) (p x f)
```

Strict initial objects are [[subterminal objects]]: given two maps
$f, g : X \to \bot$, it suffices to prove that $f \circ g\inv =
\id_\bot$; but those are maps out of $\bot$, so they are equal.

```agda
  strict-initial→subterminal
    : ∀ {i : Initial C}
    → is-strict-initial i
    → is-subterminal C (i .bot)
  strict-initial→subterminal {i} s X f g =
    pre-invr.to (s _ g) (¡-unique₂ i _ id) ∙ idl _
```
