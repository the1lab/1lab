---
talk: yes
slide-level: 2
---

# Cubical types for the working formaliser

:::{#author}
Amélia Liao
:::

<!--
```agda
{-# OPTIONS --allow-unsolved-metas #-}
open import 1Lab.Path.Reasoning
open import 1Lab.Prelude hiding (funext ; Extensional ; ext ; uncurry ; id ; _∘_ ; _==_)

open import Algebra.Group.Ab.Tensor
open import Algebra.Group.Cat.Base
open import Algebra.Group.Ab
open import Algebra.Group

open import Data.Nat.Base hiding (_==_)
open import Data.Int.Base
open import Data.Sum

open import Algebra.Group.Concrete.Abelian

open import Homotopy.Space.Circle

module Talks.Topos2024 where

private variable
  ℓ ℓr : Level
  A B C : Type ℓ
  w x y z : A
  n k : Nat
  P : A → Type ℓ
  Q : (x : A) → P x → Type ℓ

open is-iso

module _ where
```
-->

## The 1Lab

Open source combination wiki (à la nLab) + Agda library.

. . .

* Reimplementations of everything we need, e.g.

```agda
  open import 1Lab.Path
```

contains basic results about identity.

. . .

* Lots of category theory (see [Elephant](Elephant.html),
  [Borceux](Borceux.html) index pages)

* Very basic results in algebra + synthetic homotopy theory (see [HoTT ch. 8](HoTT.html#chapter-8-homotopy-theory))

. . .

This talk is a module on the 1Lab!

## Outline

<!--
```agda
_ = uaβ
```
-->

* HoTT simplifies Martin-Löf type theory by giving universes a nice
  universal property ([[univalence]])

* Cubical type theory *complicates* type theory to make this compute
  (`uaβ`{.Agda})

Lots of work has gone into usability of traditional proof assistants;
but what about *higher dimensional* proof assistants?

. . .

* Extensional equality
* Dealing with coherences
* Structure identity

# Extensional equality

When are functions $f, g : A \to B$ identical?

:::incremental
* Expected answer: whenever $f(x) \is g(x)$ for all $x$;
* Actual answer: 🤷‍♀️!

  Extensionality *independent of* MLTT. E.g. [antifunext](https://github.com/AndrasKovacs/antifunext)
:::

. . .

Our solution: [the interval](1Lab.Path.html), [[paths]].

---

<!--
```
_ = I
_ = i0
_ = i1
```
-->

A type `I`{.Agda}, with *endpoints* `i0`{.Agda}, `i1`{.Agda}, which
(co)represents identifications.

An identification $p : x \is_A y$ is an element $i : \bI, p(i) : A$ that
satisfies $p(i0) = x$ and $p(i1) = y$.

In Agda: path lambdas and path application.

```agda
_ : {A : Type} (x : A) → x ≡ x
_ = λ x i → x
```

---

<!--
```agda
module _ where private
```
-->

```agda
  funext : (f g : A → B) (h : ∀ x → f x ≡ g x) → f ≡ g
  funext f g h = {!   !}
  -- Goal: f ≡ g
  -- Context:
  --   f, g : A → B
  --   h : (x : A) → f x ≡ g x
```

---

<!--
```agda
module _ where private
```
-->

We can introduce a path with another abstraction:

```agda
  funext : (f g : A → B) (h : ∀ x → f x ≡ g x) → f ≡ g
  funext f g h i = {!   !}
  -- Goal: A → B
  -- Context: [as before], i : I
```

Not any `A → B` will do!

```agda
  -- Boundary:
  --   i = i0 ⊢ λ x → f x
  --   i = i1 ⊢ λ x → g x
```

---

<!--
```agda
module _ where private
```
-->

Goal is a function type, so we can abstract *another* argument:

```agda
  funext : (f g : A → B) (h : ∀ x → f x ≡ g x) → f ≡ g
  funext f g h i x = {!   !}
  -- Goal: B
  -- Context: [as before], x : A
  -- Boundary:
  --   i = i0 ⊢ f x
  --   i = i1 ⊢ g x
```

---

<!--
```agda
module _ where private
```
-->

Because paths restrict to their endpoints, we're done!

```agda
  funext : {f g : A → B} (h : ∀ x → f x ≡ g x) → f ≡ g
  funext {f} {g} h i x = h x i
```

. . .

<br>

```agda
  _ : {f : A → B} → funext {f = f} (λ x → refl) ≡ refl
  _ = refl

  _ : {f g : A → B} {h : ∀ x → f x ≡ g x}
    → funext (λ x → sym (h x)) ≡ sym (funext h)
  _ = refl

  _ : {f g h : A → B} {α : ∀ x → f x ≡ g x} {β : ∀ x → g x ≡ h x}
    → funext (λ x → α x ∙ β x) ≡ funext α ∙ funext β
  _ = refl
```

---

Introducing path abstractions does a number on inference:

<!--
```agda
module _ where private
```
-->

```agda
  what : ((x y : A) → x ≡ y) → (x y : A) → x ≡ y
  what h x y i = h _ _ i
```

Agda generates constraints:

<pre class=Agda>
  <span class="UnsolvedMeta">_x</span> h x y (i = <span class="InductiveConstructor">i0</span>) = x
  <span class="UnsolvedMeta">_y</span> h x y (i = <span class="InductiveConstructor">i1</span>) = y
</pre>

Neither of these is fully determined! <br>
Both metas go unsolved.

. . .

Need a nice *interface* for extensional equality.

# A nice interface

Ideally: the type $x \is_A y$ *computes* to something simpler based on $A$.

* Observational type theory with strict propositions...

    + Pro: computed identity type is basically always right;
    + Con: doesn't scale to homotopy.

* Higher observational type theory...

    + Pro: scales to homotopy;
    + Con: computed identity system will in many cases be overcomplicated.

Key example: group homomorphisms $f, g : G \to H$. These are pairs, so
$f \is g$ computes to a pair type. <br>
But the second component --- the proof that $f$ is a homomorphism --- is
irrelevant!

. . .

Without a sort of strict propositions, the system can't "see" this. <br>
So "primitive higher-OTT" will still need a helper, to fill in the
trivial second component. <br>

---

The idea is old: type classes! Essentially:

<!--
```agda
open 1Lab.Prelude using (funext)

module _ where private
```
-->

```agda
  record Extensional (A : Type) : Type (lsuc lzero) where
    field
      _≈_     : A → A → Type
      to-path : ∀ {x y : A} → x ≈ y → x ≡ y
```

<!--
```agda
  open Extensional ⦃ ... ⦄ renaming (to-path to ext) using ()
  open Extensional
```
-->

. . .

We have an instance for each type former we want to compute:

```agda
  instance
    ext-fun : ⦃ Extensional B ⦄ → Extensional (A → B)
    ext-fun ⦃ e ⦄ = record
      { _≈_     = λ f g → ∀ x → e ._≈_ (f x) (g x)
      ; to-path = λ h → funext λ x → e .to-path (h x)
      }
```

. . .

And an *overlappable* instance for the base case:

```agda
    ext-base : Extensional A
    ext-base = record { to-path = λ x → x }
    {-# OVERLAPPABLE ext-base #-}
```

---

We can test that this works by asking Agda to check `ext`{.Agda} at
various types:

```agda
  _ : {A B : Type} {f g : A → B} → (∀ x → f x ≡ g x) → f ≡ g
  _ = ext

  _ : {A B C : Type} {f g : A → B → C} → (∀ x y → f x y ≡ g x y) → f ≡ g
  _ = ext

  _ : {A : Type} {x y : A} → x ≡ y → x ≡ y
  _ = ext
```

. . .

A benefit: type class solving *isn't a real function*. Can be unstable
under substitution!

```agda
  instance
    ext-uncurry : ⦃ Extensional (A → B → C) ⦄ → Extensional (A × B → C)
    ext-uncurry ⦃ e ⦄ = record
      { _≈_     = λ f g → e ._≈_ (curry f) (curry g)
      ; to-path = λ h i (x , y) → e .to-path h i x y
      }
    {-# OVERLAPPING ext-uncurry #-}
```

The resulting relation has three arguments, rather than two:

```agda
  _ : {A B C D : Type} {f g : A × B → C → D}
    → (∀ a b c → f (a , b) c ≡ g (a , b) c)
    → f ≡ g
  _ = ext
```

---

<!--
```agda
open 1Lab.Prelude using (ext)

module _ where private
```
-->

The real implementation handles maps of algebraic structures, e.g.
groups,

```agda
  _ : {G H : Group lzero} {f g : Groups.Hom G H}
    → ((x : ⌞ G ⌟) → f # x ≡ g # x) → f ≡ g
  _ = ext
```

maps *from* certain higher inductive types, e.g. generic set-quotients,
or abelian group homomorphisms from a tensor product,

```agda
  _ : {A B C : Abelian-group lzero} {f g : Ab.Hom (A ⊗ B) C}
    → ((x : ⌞ A ⌟) (y : ⌞ B ⌟) → f # (x , y) ≡ g # (x , y))
    → f ≡ g
  _ = ext
```

and also: natural transformations, maps in slice categories, in comma
categories, in categories of elements, in wide and full subcategories,
in categories of monad algebras, type-theoretic equivalences and
embeddings, monotone maps, &c., &c.
