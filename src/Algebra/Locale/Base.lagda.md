```agda
open import Algebra.Frame

open import Cat.Diagram.Terminal
open import Cat.Displayed.Total
open import Cat.Prelude

import Cat.Reasoning

module Algebra.Locale.Base where
```

# Locales

Locales are a constructive interpretation of the notion of space, where
we define a space following the idea of _measurement_, or (more
precisely) the idea of _observable_. A locale is to be thought of as a
collection of _observations_, equipped with a partial order specifying
when an observation _refines_ another (for example, measuring $9 \le g
\le 9.8 m/s^2$ _refines_ measuring $9 \le g \le 10 m/s^2$), such that
observations are closed under binary meets ("intersections",
"conjunctions") and _arbitrary_ joins ("unions", "disjunctions").

The asymmetry in these conditions comes from the intuition of
observations we could actually perform in the real world: in finite
time, we can only perform finitely many measurements, and they are all
necessary to establish a meet --- so locales are closed under finite
meets; But even if we want to test the disjunction of infinitely many
observations, only one of them is necessary to establish the overall
experiment, so locales are closed under arbitrary joins.

In reality, a locale $X$ is nothing more than a [frame], a kind of
complete lattice; But locales relate to eachother in a manner dual to
how frames do^[Put another way, the category of locales is the opposite
of the category of frames.]. To emphasize this duality, we will use
different notation --- and different types --- for a locale and its
"underlying" frame; writing $X$ for the locale and $\mathcal{O}X$ for
its **frame of opens**.

[frame]: Algebra.Frame.html

```agda
record Locale (ℓ : Level) : Type (lsuc ℓ) where
  field Ω[_] : Frames.Ob ℓ
  open Frame-on (Ω[_] .snd)

open Locale public
open Precategory

Locales : ∀ ℓ → Precategory (lsuc ℓ) (lsuc ℓ)
Locales ℓ .Ob          = Locale ℓ
Locales ℓ .Hom X Y     = Frames.Hom ℓ Ω[ Y ] Ω[ X ]
Locales ℓ .Hom-set _ _ = Frames.Hom-set ℓ _ _
Locales ℓ .id          = Frames.id ℓ
Locales ℓ ._∘_ f g     = Frames._∘_ ℓ g f
Locales ℓ .idr f       = Frames.idl _ f
Locales ℓ .idl f       = Frames.idr _ f
Locales ℓ .assoc f g h = sym $ Frames.assoc _ h g f

module Locales {ℓ} = Cat.Reasoning (Locales ℓ)
```

A particularly important locale is the **point** (the _terminal_
locale), which we write `⊤ₗ`{.Agda}, whose frame of opens is the
[subobject classifier] $\Omega$.^[Equivalently, its frame of opens is
the power set of the unit type.]

[subobject classifier]: 1Lab.Resizing.html
