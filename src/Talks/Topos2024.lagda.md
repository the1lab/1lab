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
open import Algebra.Group.Cat.Base hiding (Displayed)
open import Algebra.Group.Ab
open import Algebra.Group

open import Data.Nat.Base hiding (_==_)
open import Data.Int.Base
open import Data.Sum

open import Cat.Base

open import Algebra.Group.Concrete.Abelian

open import Homotopy.Space.Circle

import Cat.Reasoning as Cat

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

This talk is a module in the 1Lab!

## The 1Lab as a library

* Constructive but *im*predicative (propositional resizing); homotopical
  features used freely

* Type classes for automation, but only of *properties*; equipping a
  type with *structure* (e.g. algebraic) is always explicit

* Playground for new Agda features, e.g. `opaque`{.kw}, `OVERLAPPING`{.kw} instances

## This talk

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

We'll talk about:

* Extensional equality
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

# Structure identity

Same setup: when are types $A, B : \ty$ identical? <br>
Ideal answer: when they are *indistinguishable*. <br>
What distinguishes types?

Take e.g. $\bN \times \mathtt{String}$ vs. $\mathtt{String} \times \bN$:

::: incremental

* In base MLTT (or even e.g. Lean): no proof that they're distinct

* ... because if you give me any property that holds of one, I can
  modify your proof to show it holds of the other (by hand)

* ... so these types should be identical!

:::

. . .

The actual answer: 🤷‍♀️ <br>
Univalence says they're the same; (set-level) OTT says they're
different; everyone else is undecided

---

Univalence says $(A \is B)$ equivalent to $(A \simeq B)$:

* Just as much control over $p : A \is B$ as we would have over $f : A \simeq B$;

  + E.g. *exactly* two inhabitants $\ua(\id)$, $\ua(\operatorname{not})$ in $\{0, 1\} \is \{0, 1\}$

* Not often interested in arbitrary types. More often: types with *structure*.

  Example: monoids.

. . .

A monoid $M$ is a tuple $(M, *, 1, ...)$ consisting of

* The *stuff* drawn from $M$;
* The *structure* of the multiplication and identity;
* The *property*: proofs of identity on the left & right and associativity;

When are two monoids the same? <br>

---

Let's make it a bit more formal: we define the property, parametrised
over the stuff and the structure;

```agda
is-monoid : (M : Type) → (M → M → M) → M → Type
is-monoid M m u =
  is-set M            -- required so is-monoid is a property
  × (∀ x → m u x ≡ x) -- left identity
  × (∀ x → m x u ≡ x) -- right identity
  × (∀ x y z → m x (m y z) ≡ m (m x y) z) -- associativity
```

We'll need that it's an actual property:

```agda
is-monoid-is-prop : ∀ M m u → is-prop (is-monoid M m u)
```

<!--
```agda
is-monoid-is-prop _ _ _ = Σ-is-hlevel 1 (is-hlevel-is-prop 2) λ mset →
  let instance _ = hlevel-instance {n = 2} mset in hlevel 1
```
-->

Then we sum it all:

```agda
Monoid : Type₁
Monoid =
  Σ[ M ∈ Type ]                   -- stuff
  Σ[ m ∈ (M → M → M) ] Σ[ u ∈ M ] -- structure
    (is-monoid M m u)             -- property
```

Completely formally, a `Monoid`{.Agda} has 7 fields, but we've shown
that 4 don't matter.

---

Then we can compute the identity type: If we have monoids $M = (M_0, m, u,
\alpha)$ and $N = (N_0, n, v, \beta)$, what is $M \is N$?

```agda
module _ (M@(M₀ , m , u , α) N@(N₀ , n , v , β) : Monoid) where
```

<br>

. . .

Step 1: an identity of tuples is a tuple of identities, and identity in
`is-monoid`{.Agda} is trivial;

```agda
  Step₁ : Type₁
  Step₁ = Σ[ p ∈ M₀ ≡ N₀ ]
    ( PathP (λ i → p i → p i → p i) m n
    × PathP (λ i → p i) u v
    )

  step₁ : Step₁ → M ≡ N
  step₁ (p , q , r) i = p i , q i , r i ,
    is-prop→pathp (λ i → is-monoid-is-prop (p i) (q i) (r i)) α β i
```

---

Step 2: we can simplify the `PathP`{.Agda}s to talk about transport instead:

```agda
  Step₂ : Type₁
  Step₂ = Σ[ p ∈ M₀ ≡ N₀ ]
    ( (∀ x y → transport p (m x y) ≡ n (transport p x) (transport p y))
    × transport p u ≡ v
    )

  step₂ : Step₂ → Step₁
  step₂ (p , q , r) = p , q' , to-pathp r where
    -- q' actually pretty complicated...
    q' = funext-dep λ α → funext-dep λ β →
      to-pathp (q _ _ ∙ ap₂ n (from-pathp α) (from-pathp β))
```

---

Step 3: we know what identity of types is!

```agda
  Step₃ : Type
  Step₃ = Σ[ p ∈ M₀ ≃ N₀ ] -- equivalence!
    ( (∀ x y → p .fst (m x y) ≡ n (p .fst x) (p .fst y))
    × p .fst u ≡ v
    )
```

Takes a bit of massaging...

```agda
  step₃ : Step₃ → Step₂
  step₃ (p , q , r) = ua p , q' , r' where
    r' = transport (ua p) u ≡⟨ uaβ p u ⟩
         p .fst u           ≡⟨ r ⟩
         v                  ∎

    q' : ∀ x y → _
    q' x y =
      transport (ua p) (m x y)                    ≡⟨ uaβ p (m x y) ⟩
      p .fst (m x y)                              ≡⟨ q x y ⟩
      n (p .fst x) (p .fst y)                     ≡⟨ ap₂ n (sym (uaβ p x)) (sym (uaβ p y)) ⟩
      n (transport (ua p) x) (transport (ua p) y) ∎
```

The conclusion: identity in the type `Monoid`{.Agda} is *exactly¹*
monoid isomorphism!

# Designing for structure identity

While it's great that the theory works, the proofs are pretty annoying. <br>
But they're very mechanical --- incremental! <br>

Our solution: put together categories of structures *in layers*. <br>
Displayed categories!

A category over $\cC$ is an alternative presentation of the data of a
category $\cD$ and a functor $\pi : \cD \to \cC$; just more "native" to
type theory.

<!--
```agda
private module _ {o ℓ : Level} (C : Precategory o ℓ) where
  open Precategory C
```
-->

---

The idea: turn fibers into families.

```agda
  record Displayed o' ℓ' : Type (o ⊔ ℓ ⊔ lsuc (o' ⊔ ℓ')) where
    field
      Ob[_]  : ⌞ C ⌟ → Type o'
      Hom[_] : (f : Hom x y) → Ob[ x ] → Ob[ y ] → Type ℓ'
```

. . .

Stuff over stuff, structure over structure:

```agda
      id'  : {x' : Ob[ x ]} → Hom[ id ] x' x'
      _∘'_
        : {x' : Ob[ x ]} {y' : Ob[ y ]} {z' : Ob[ z ]}
        → {f : Hom y z} (f' : Hom[ f ] y' z')
        → {g : Hom x y} (g' : Hom[ g ] x' y')
        → Hom[ f ∘ g ] x' z'
```

... also need property over property; check the formalisation.

---

If we start with a functor, then $\operatorname{Ob}[x]$ is the type
$\sum_{y : \cD} \pi(y) \cong x$; the "fibre" of $\pi$ over $x$.

<!--
```agda
private module _ {o ℓ o' ℓ' : Level} {C : Precategory o ℓ} {D : Precategory o' ℓ'} (π : Functor D C) where private
  private
    module C = Cat C
    module D = Cat D
    module π = Functor π
    open C using (_∘_ ; id ; _≅_)

    open C._≅_
  open Displayed
```
-->

```agda
  Street : Displayed C _ _
  Street .Ob[_] x = Σ[ y ∈ D ] (π.₀ y ≅ x)
```

The maps over are more complicated:

```agda
  Street .Hom[_] f (x' , i) (y' , j) = Σ[ g ∈ D.Hom x' y' ]
    (π.₁ g ≡ j .from ∘ f ∘ i .to)
```

Accordingly, the structure is pretty annoying:

```agda
  Street .id' {x} {x' , i} = record { snd =
    π.₁ D.id               ≡⟨ π.F-id ⟩
    id                     ≡˘⟨ i .invr ⟩
    i .from ∘ i .to        ≡˘⟨ ap₂ _∘_ refl (C.idl _) ⟩
    i .from ∘ id C.∘ i .to ∎ }
  Street ._∘'_ = _ -- even worse!
```

---

If we start with a displayed category $\cE \liesover \cC$, we can
put together a category with objects $\sum_{x : \cC}
\operatorname{Ob}[x]$ --- the [[total category]] $\int \cE$.

Similarly, each $x : \cC$ gives a category $\cE^*(x)$ with objects
$\operatorname{Ob}[x]$ and maps $\operatorname{Hom}[f](-,-)$

Properties of the functor $\pi : \int \cE \to \cC$ map very nicely to
properties of $\cE$!

+--------------------+------------------------------------------------------------------------------+
| $\pi$ is...        | $\cE$ satisfies...                                                           |
+====================+==============================================================================+
| [[faithful]]       | each $\operatorname{Hom}[-](-,-)$ is a [[proposition]]                       |
+--------------------+------------------------------------------------------------------------------+
| [[full]]           | each $\operatorname{Hom}[-](-,-)$ is [[inhabited\|propositional truncation]] |
+--------------------+------------------------------------------------------------------------------+
| [[fully faithful]] | each $\operatorname{Hom}[-](-,-)$ is [[contractible]]                        |
+--------------------+------------------------------------------------------------------------------+
| [[amnestic]]       | each $\cE^*(x)$ univalent, and so is $\cC$                                   |
+--------------------+------------------------------------------------------------------------------+

That last row is important!

---

We can present a concrete, univalent category as a displayed category.

* Concrete: the base is $\Sets$ and each $\operatorname{Hom}[-](-,-)$ is a proposition.
* Univalent: each $\cE^*(x)$ is a partial order.

. . .

These data amount to:

1. A type family of *structures* $F : \ty \to \ty$;
2. A proposition $\operatorname{Hom}[f](S, T)$, given $f : A \to B$, $S : F(A)$, $T : F(B)$;<br>
  Type encoding "$f$ is a structure-preserving map from $S$ to $T$";
3. Proofs that (2) contains the identities and is closed under composition;
4. For univalence: a proof that if $\id$ is a structure preserving map
   $S \to T$ (and also $T \to S$), then $S = T$.

# Concrete example

We start by defining the property, parametrised by the structure:

```agda
record is-semigroup {A : Type ℓ} (_⋆_ : A → A → A) : Type ℓ where
  field
    has-is-set : is-set A
    assoc      : ∀ {x y z} → x ⋆ (y ⋆ z) ≡ (x ⋆ y) ⋆ z
```

. . .

We can derive that this *is* a property pretty mechanically:

```agda
module _ where
  private unquoteDecl eqv = declare-record-iso eqv (quote is-semigroup)

  is-semigroup-is-prop : {A : Type ℓ} {s : A → A → A} → is-prop (is-semigroup s)
  is-semigroup-is-prop = Iso→is-hlevel 1 eqv $ Σ-is-hlevel 1 (hlevel 1) λ x →
    let instance _ = hlevel-instance {n = 2} x in hlevel 1
```

---

Then we define the structure:

```agda
record Semigroup-on (A : Type ℓ) : Type ℓ where
  field
    _⋆_              : A → A → A
    has-is-semigroup : is-semigroup _⋆_
  open is-semigroup has-is-semigroup public
```

... and what it means for functions to preserve it:

```agda
record is-semigroup-hom (f : A → B) (S : Semigroup-on A) (T : Semigroup-on B)
  : Type (level-of A ⊔ level-of B) where

  private
    module S = Semigroup-on S
    module T = Semigroup-on T

  field
    pres-⋆ : ∀ x y → f (x S.⋆ y) ≡ f x T.⋆ f y
```

<!--
```agda
private
  unquoteDecl eqv = declare-record-iso eqv (quote Semigroup-on)
  unquoteDecl eqv' = declare-record-iso eqv' (quote is-semigroup-hom)

instance
  H-Level-is-semigroup : ∀ {n} {s : A → A → A} → H-Level (is-semigroup s) (suc n)
  H-Level-is-semigroup = prop-instance is-semigroup-is-prop

  H-Level-is-semigroup-hom
    : ∀ {n} {f : A → B} {S : Semigroup-on A} {T : Semigroup-on B}
    → H-Level (is-semigroup-hom f S T) (suc n)
  H-Level-is-semigroup-hom {T = T} = prop-instance (Iso→is-hlevel 1 eqv' (hlevel 1))
    where instance _ = hlevel-instance {n = 2} (T .Semigroup-on.has-is-set)

open is-semigroup-hom
```
-->

---

We can then fill in the four bullet points. $F$ is
`Semigroup-on`{.Agda}, $\operatorname{Hom}[-](-,-)$ is
`is-semigroup-hom`{.Agda},

```agda
Semigroup-structure : ∀ {ℓ} → Thin-structure ℓ Semigroup-on
Semigroup-structure .is-hom f S T = el! (is-semigroup-hom f S T)
```

... identities and composites are respected ...

```agda
Semigroup-structure .id-is-hom .pres-⋆ x y = refl
Semigroup-structure .∘-is-hom f g α β .pres-⋆ x y =
  ap f (β .pres-⋆ x y) ∙ α .pres-⋆ _ _
```

and, finally, the univalence condition:

```agda
Semigroup-structure .id-hom-unique p q = Iso.injective eqv $ Σ-prop-path! $
  ext λ a b → p .pres-⋆ a b
```
