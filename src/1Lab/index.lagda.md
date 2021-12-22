```agda
module 1Lab.index where
```

# Type theory

This module presents the modules under the `1Lab` namespace in a
recommended order for reading as a first introduction to Cubical Agda.
Familiarity with base Agda is assumed throughout. As a quick reminder,
the moduel names in the code blocks below are all clickable.

**Paths**. The first thing to read about is the main idea of cubical
type theory, which can be summed up as "representing equalities as maps
out of an interval". For engineering reasons (Agda won't let us have
cyclic dependencies), the `1Lab.Path`{.Agda} module is _massive_. It
contains explanations of all the fundamental concepts of cubical type
theory:

* The interval type, and its De Morgan structure; How to use this De
Morgan structure to extend paths to higher dimensions, and how to invert
paths;

* Paths in more generality;

* The transport operation, and how it computes;

* Deriving path induction from the transport operation and the De Morgan
operations on the interval;

* The functorial action of functions $A \to B$ on paths $x ≡ y$;

* Partial elements, extensibility, and the composition operation.

```agda
open import 1Lab.Path -- Don't read past "Composition"
```

After reading about paths, the definition of **h-level** should be
accessible. The most important h-levels to understand are the
**contractible types** and the **propositions**, so focus on
understanding those first.

```agda
open import 1Lab.HLevel
```

The notion of contractible type is used directly in the definition of
**equivalence**, and equivalences are one of the central concepts in
Homotopy Type Theory. They're in the module `1Lab.Equiv`{.Agda}.

```agda
open import 1Lab.Equiv
```

Equivalences are used to define **glueing** and prove **univalence**:
Paths in the universe are the same thing as equivalences of types. This
module also has an example of a proof by **equivalence induction**.

```agda
open import 1Lab.Univalence
open import 1Lab.Type -- if you need a refresher on universes
```

From here, you should be good to read any of the other modules! Here are
some of interest:

- The type of **booleans** and a characterisation of its type of
automorphisms: `(Bool ≡ Bool) ≡ Bool`.

  ```agda
open import Data.Bool
  ```

- Families of **fibrewise equivalences** are logically equivalent as
equivalences of **total spaces**. This is used in proving e.g. [Rijke's
theorem](agda://1Lab.HLevel.Sets#Rijke-isSet).

  ```agda
open import 1Lab.Equiv.Fibrewise
  ```

- Characterisations of the **h-sets**, which are the types of h-level 2.
The sets are the types in HoTT that behave like the types in Agda w/ K.
This is quite literal: "Satisfies K" is an equivalent characterisation
of "is of h-level 2".

  ```agda
open import 1Lab.HLevel.Sets
  ```
