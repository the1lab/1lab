```agda
open import Cat.Diagram.Limit.Base
open import Cat.Instances.Shape.Parallel
open import Cat.Prelude

import Cat.Reasoning

module Cat.Diagram.Equaliser {o ℓ} (C : Precategory o ℓ) where
```

<!--
```agda
open Cat.Reasoning C

private variable
  e a b : Ob
  f g h : Hom a b

open Functor
open _=>_
```
-->

# Equalisers

The **equaliser** of two maps $f, g : A \to B$, when it exists,
represents the largest subobject of $A$ where $f$ and $g$ agree. In this
sense, the equaliser is the categorical generalisation of a _solution
set_: The solution set of an equation in one variable is largest subset
of the domain (i.e. what the variable ranges over) where the left- and
right-hand-sides agree.

We can define equalisers as [limits] of a the [parallel arrows diagram].

[parallel arrows diagram]: Cat.Instances.Shape.Parallel.html

```agda
is-equaliser : {f g : Hom a b} {equ : Hom e a} → (f ∘ equ ≡ g ∘ equ) → Type _
is-equaliser {e = e} {f = f} {g = g} {equ = equ} equal =
  is-limit {C = C} (Fork f g) e (fork equal)

Equaliser : (f g : Hom a b) → Type _
Equaliser f g = Limit {C = C} (Fork f g)
```

## Concretely

This compact definition allows us to apply general theorems easily, but
makes working with a specific equaliser difficult. To alleviate this,
we define an auxillary record `make-is-equaliser`{.Agda} that presents a
more unfolded view of the data.

```agda
record make-is-equaliser {e a b} (f g : Hom a b) (equ : Hom e a) : Type (o ⊔ ℓ) where
  no-eta-equality
  field
    equal     : f ∘ equ ≡ g ∘ equ
    universal : ∀ {x} {e′ : Hom x a} → f ∘ e′ ≡ g ∘ e′ → Hom x e
    factors   : ∀ {x} {e′ : Hom x a} → (p : f ∘ e′ ≡ g ∘ e′) → equ ∘ universal p ≡ e′
    unique
      : ∀ {x} {e′ : Hom x a} {p : f ∘ e′ ≡ g ∘ e′} {other : Hom x e}
      → equ ∘ other ≡ e′
      → other ≡ universal p

  unique₂
    : ∀ {x} {e′ : Hom x a} {p : f ∘ e′ ≡ g ∘ e′} {o1 o2 : Hom x e}
    → equ ∘ o1 ≡ e′
    → equ ∘ o2 ≡ e′
    → o1 ≡ o2
  unique₂ {p = p} q1 q2 = unique {p = p} q1 ∙ sym (unique q2)
```

We can visualise the situation using the commutative diagram below:

~~~{.quiver}
\[\begin{tikzcd}
  E & A & B \\
  F
  \arrow["f", shift left=1, from=1-2, to=1-3]
  \arrow["g"', shift right=1, from=1-2, to=1-3]
  \arrow["{\rm{equ}}", hook, from=1-1, to=1-2]
  \arrow["{\exists!}", dashed, from=2-1, to=1-1]
  \arrow["e\prime"', from=2-1, to=1-2]
\end{tikzcd}\]
~~~

If we have an element of `make-is-equaliser`{.Agda}, then we can
construct an element of `is-equaliser`{.Agda}.

```agda
to-is-equaliser
  : ∀ {e a b} {f g : Hom a b} {equ : Hom e a}
  → (mk-eq : make-is-equaliser f g equ)
  → is-equaliser (make-is-equaliser.equal mk-eq)
to-is-equaliser {e = e} {a} {b} {f} {g} {equ} mkeq =
  to-is-limitp ml λ where
    {true} → refl
    {false} → refl
  where
    module mkeq =  make-is-equaliser mkeq
    open make-is-limit

    ml : make-is-limit (Fork f g) e
    ml .ψ true = f ∘ equ
    ml .ψ false = equ
    ml .commutes {true} {true} tt = idl _
    ml .commutes {false} {true} true = sym mkeq.equal
    ml .commutes {false} {true} false = refl
    ml .commutes {false} {false} tt = idl _
    ml .universal eta p =
      mkeq.universal (p {false} {true} false ∙ sym (p {false} {true} true))
    ml .factors {true} eta p =
      pullr (mkeq.factors _) ∙ p {false} {true} false
    ml .factors {false} eta p =
      mkeq.factors _
    ml .unique eta p other q =
      mkeq.unique (q false)
```

To use the data of `is-equaliser`{.Agda}, we provide a function for
*un*making an equaliser.

```agda
unmake-is-equaliser
  : ∀ {e a b} {f g : Hom a b} {equ : Hom e a} {equal : f ∘ equ ≡ g ∘ equ}
  → is-equaliser equal
  → make-is-equaliser f g equ
unmake-is-equaliser {e} {a} {b} {f} {g} {equ} {comm} lim = equaliser
  module unmake-equaliser where
    open make-is-equaliser
    module lim = is-limit lim

    parallel : ∀ {x} → Hom x a → (j : Bool) → Hom x (Fork {C = C} f g .F₀ j)
    parallel e′ true = f ∘ e′
    parallel e′ false = e′

    equaliser : make-is-equaliser f g equ
    equaliser .equal = comm
    equaliser .universal {e′ = e′} p =
      lim.universal (parallel e′) λ where
        {true} {true} tt → idl _
        {false} {true} true → sym p
        {false} {true} false → refl
        {false} {false} tt → idl _
    equaliser .factors p =
      lim.factors {j = false} _ _
    equaliser .unique p =
      lim.unique _ _ _ λ where
        true → pullr p
        false → p
```

<!--
```agda
module is-equaliser
  {e a b} {f g : Hom a b} {equ : Hom e a} {equal : f ∘ equ ≡ g ∘ equ}
  (equaliser : is-equaliser equal)
  where

  open make-is-equaliser (unmake-is-equaliser equaliser) public
```
-->

We perform a similar construction for the bundled form of equalisers.

```agda
record make-equaliser {a b} (f g : Hom a b) : Type (o ⊔ ℓ) where
  no-eta-equality
  field
    apex : Ob
    equ  : Hom apex a
    has-is-equaliser : make-is-equaliser f g equ

  open make-is-equaliser public
```

<!--
```agda
to-equaliser : make-equaliser f g → Equaliser f g
to-equaliser me = to-limit (to-is-equaliser has-is-equaliser)
  where open make-equaliser me

module Equaliser {f g : Hom a b} (equaliser : Equaliser f g) where
  open Limit equaliser renaming (apex to L-apex)

  apex : Ob
  apex = L-apex

  equ : Hom apex a
  equ = ψ false

  equal : f ∘ equ ≡ g ∘ equ
  equal = commutes {y = true} false ∙ sym (commutes {y = true} true)

  has-is-equaliser : is-equaliser equal
  has-is-equaliser =
    to-is-limitp (unmake-limit has-limit) λ where
      {true} → sym (commutes false)
      {false} → refl
```
-->

## Uniqueness

<!--
```agda
module _ where
  open Equaliser
```
-->

Equalisers, when the exist, are unique. This follows from [uniqueness of
limits].

[uniqueness of limits]: Cat.Diagram.Limit.Base#uniqueness

```agda
  equalisers-unique : ∀ (e1 e2 : Equaliser f g) → apex e1 ≅ apex e2
  equalisers-unique e1 e2 =
    limits-unique (has-is-equaliser e2) (has-is-equaliser e1)
```

## Equalisers are Monos

As a small initial application, we prove that equaliser arrows are
always [monic]:

[monic]: Cat.Morphism.html#monos

```agda
is-equaliser→is-monic
  : {f g : Hom a b} {equ : Hom e a} {equal : f ∘ equ ≡ g ∘ equ}
  → is-equaliser equal
  → is-monic equ
is-equaliser→is-monic {equal = equal} equalises h₁ h₂ p =
  is-equaliser.unique₂ equalises {p = extendl equal} p refl
```
