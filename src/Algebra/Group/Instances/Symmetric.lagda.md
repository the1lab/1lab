<!--
```agda
open import 1Lab.Prelude

open import Algebra.Group.Cat.Base
open import Algebra.Group

open import Data.Fin
```
-->

```agda
module Algebra.Group.Instances.Symmetric where
```

# Symmetric groups {defines="symmetric-group"}

If $X$ is a set, then the type of all bijections $X \simeq X$ is also a
set, and it forms the carrier for a [[group]]: The _symmetric group_ on $X$.

```agda
Sym : ∀ {ℓ} (X : Set ℓ) → Group-on (∣ X ∣ ≃ ∣ X ∣)
Sym X = to-group-on group-str where
  open make-group
  group-str : make-group (∣ X ∣ ≃ ∣ X ∣)
  group-str .mul g f = f ∙e g
```

The group operation is `composition of equivalences`{.Agda ident=∙e};
The identity element is `the identity equivalence`{.Agda ident=id-equiv}.

```agda
  group-str .unit = id , id-equiv
```

This type is a set because $X \to X$ is a set (because $X$ is a set by
assumption), and `being an equivalence is a proposition`{.Agdaa
ident=is-equiv-is-prop}.

```agda
  group-str .group-is-set = hlevel 2
```

The associativity and identity laws hold definitionally.

```agda
  group-str .assoc _ _ _ = trivial!
  group-str .idl _ = trivial!
```

The inverse is given by `the inverse equivalence`{.Agda ident=_e⁻¹}, and
the inverse equations hold by the fact that the inverse of an
equivalence is both a section and a retraction.

```agda
  group-str .inv = _e⁻¹
  group-str .invl (f , eqv) = ext (equiv→unit eqv)
```

We write $S_n$ for the symmetric group on the [[standard finite set]]
with $n$ elements.

```agda
S : Nat → Group lzero
S n = el! (Fin n ≃ Fin n) , Sym (el! (Fin n))
```
