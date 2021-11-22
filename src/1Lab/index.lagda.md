```
module 1Lab.index where
```

# Type theory

This module presents the modules under the `1Lab` namespace in a
recommended order for reading as a first introduction to Cubical Agda.
Familiarity with base Agda is assumed throughout. As a quick reminder,
the moduel names in the code blocks below are all clickable.

**Paths**. The first thing to read about is the main idea of cubical
type theory. Read this module up until the end of the [substitution]
header, then come back here.

[substitution]: 1Lab.Path.html#substitution

```
open import 1Lab.Path -- Don't read past "Transitivity"
```

After reading about paths, you need an idea of **partial elements**
to understand how the composition operation is defined in cubical type
theory. This module can be read bottom-to-top after understanding the
basics of paths.

```
open import 1Lab.Path.Partial
```

Knowing about partial elements, you can now understand the definition of
the **composition** operation. Go back and read the rest of the
`1Lab.Path`{.Agda} module.

```
open import 1Lab.Path -- From "Transitivity" to the end
```

After reading about paths, the definition of **h-level** should be
accessible. The most important h-levels to understand are the
**contractible types** and the **propositions**, so focus on
understanding those first.

```
open import 1Lab.HLevel
```

The notion of contractible type is used directly in the definition of
**equivalence**, and equivalences are one of the central concepts in
Homotopy Type Theory. They're in the module `1Lab.Equiv`{.Agda}.

```
open import 1Lab.Equiv
```

Equivalences are used to define **glueing** and prove **univalence**:
Paths in the universe are the same thing as equivalences of types. This
module also has an example of a proof by **equivalence induction**.

```
open import 1Lab.Univalence
open import 1Lab.Type -- if you need a refresher on universes
```

From here, you should be good to read any of the other modules! Here are
some of interest:

- The type of **booleans** and a characterisation of its type of
automorphisms: `(Bool ≡ Bool) ≡ Bool`.

  ```
open import 1Lab.Data.Bool
  ```

- Families of **fibrewise equivalences** are logically equivalent as
equivalences of **total spaces**. This is used in proving e.g. [Rijke's
theorem](agda://1Lab.HLevel.Sets#Rijke-isSet).

  ```
open import 1Lab.Equiv.Fibrewise
  ```

- Characterisations of the **h-sets**, which are the types of h-level 2.
The sets are the types in HoTT that behave like the types in Agda w/ K.
This is quite literal: "Satisfies K" is an equivalent characterisation
of "is of h-level 2".

  ```
open import 1Lab.HLevel.Sets
  ```