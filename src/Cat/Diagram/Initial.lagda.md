```agda
open import Cat.Diagram.Colimit.Base
open import Cat.Functor.Kan.Base
open import Cat.Instances.Shape.Initial
open import Cat.Prelude

module Cat.Diagram.Initial {o ℓ} (C : Precategory o ℓ) where
```

<!--
```agda
open import Cat.Reasoning C
```
-->

# Initial objects

An object $\bot$ of a category $\mathcal{C}$ is said to be **initial**
if there exists a _unique_ map to any other object. We can define this
concisely as the [colimit] of the [empty diagram].

[colimit]: Cat.Diagram.Colimit.Base.html
[empty diagram]: Cat.Instances.Shape.Initial.html

```agda
is-initial : Ob → Type _
is-initial x = is-colimit {C = C} ¡F x ¡nt

Initial : Type _
Initial = Colimit {C = C} ¡F
```

## Concretely

We use this definition as it is abstract: it allows us to use general
theorems about limits when working with initial objects! However,
it is also abstract, which means that working with a _specific_ initial
object becomes a lot more difficult. To work around this, we provide
an auxiliary record `make-is-initial` that describes initial objects
more concretely.

```agda
record make-is-initial (t : Ob) : Type (o ⊔ ℓ) where
  no-eta-equality
  field
    ¡ : ∀ {x} → Hom t x
    ¡-unique : ∀ {x} → (f : Hom t x) → f ≡ ¡

  ¡-unique₂ : ∀ {x} {f g : Hom t x} → f ≡ g
  ¡-unique₂ = ¡-unique _ ∙ sym (¡-unique _)

  ⊥-id : ∀ (f : Hom t t) → f ≡ id
  ⊥-id _ = ¡-unique₂

  ¡-contr : ∀ {x} → is-contr (Hom t x)
  ¡-contr = contr ¡ λ f → sym (¡-unique f)
```

If we have this data, then we can make a value of `is-initial{.Agda}.

```agda
to-is-initial : ∀ {t} → make-is-initial t → is-initial t
to-is-initial {t = t} mkinit = isc where
  open make-is-initial mkinit
  open is-lan
  open _=>_

  isc : is-colimit ¡F t ¡nt
  isc .σ _ .η _ = ¡
  isc .σ _ .is-natural _ _ _ = ¡-unique₂
  isc .σ-comm = Nat-path (λ ())
  isc .σ-uniq _ = Nat-path λ _ → sym $ ¡-unique _
```

To use the data of `is-initial we provide a function for *un*making
an initial object.

```agda
unmake-is-initial : ∀ {t} → is-initial t → make-is-initial t
unmake-is-initial {t = t} colim = init module unmake-initial where
  open make-is-initial
  module colim = is-colimit colim

  init : make-is-initial t
  init .¡ = colim.universal (λ ()) (λ ())
  init .¡-unique f = colim.unique (λ ()) (λ ()) f λ ()
```

<!--
```agda
module is-initial {t} (term : is-initial t) where
  open make-is-initial (unmake-is-initial term) public
```
-->

```agda
record make-initial : Type (o ⊔ ℓ) where
  no-eta-equality
  field
    bot : Ob
    has-is-initial : make-is-initial bot

  open make-is-initial public
```

<!--
```agda
to-initial : make-initial → Initial
to-initial mi = to-colimit (to-is-initial has-is-initial)
  where open make-initial mi

module Initial (i : Initial) where

  open Colimit i
  open is-lan
  open Functor
  open _=>_

  bot : Ob
  bot = coapex

  has-is-initial : is-initial bot
  has-is-initial =
    to-is-colimitp (unmake-colimit has-colimit) (λ { {()} })

  open is-initial has-is-initial public

open Initial
```
-->


We do a similar construction for the bundled form of initial objects.

## Intuition

The intuition here is that we ought to think about an initial object as
having "the least amount of structure possible", insofar that it can be
mapped _into_ any other object. For the category of `Sets`{.Agda}, this
is the empty set; there is no required structure beyond "being a set",
so the empty set sufficies.

<!--
[TODO: Reed M, 15/02/2022] Link to the categories in question
(once the exist!)
-->

In more structured categories, the situation becomes a bit more
interesting. Once our category has enough structure that we can't build
maps from a totally trivial thing, the initial object begins to behave
like a notion of **Syntax** for our category.  The idea here is that we
have a _unique_ means of interpreting our syntax into any other object,
which is exhibited by the universal map `¡`{.Agda}

## Uniqueness

One important fact about initial objects is that they are **unique** up
to isomorphism:

```agda
⊥-unique : (i i′ : Initial) → bot i ≅ bot i′
⊥-unique i i′ =
  colimits-unique
    (has-is-initial i′)
    (has-is-initial i)
```

Additionally, if $C$ is a category, then the space of initial objects is
a proposition:

```agda
Initial-is-prop : is-category C → is-prop Initial
Initial-is-prop = Colimit-is-prop
```
