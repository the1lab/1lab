```agda
module 1Lab.Type where
```

# Universes {defines="universe"}

A **universe** is a type whose inhabitants are types. In our type
theory, the most common universe is `Type`{.Agda}, the
[[univalent|univalence]] universe of [[fibrant]] types.

```agda
open import Prim.Type public
```

Since `Type`{.Agda} is itself a fibrant type (with composition given by
[[glueing]]), we might want for it to also live in a universe. However,
a universe closed under `Σ`{.Agda} and [[W-types]], which `Type`{.Agda}
is, can not code for itself: this is [[Russell's paradox]]. Instead,
`Type`{.Agda} is parametrised by a _`Level`{.Agda}_, a technical gadget
which serves to stratify a **hierarchy** of universes to prevent any
given universe for belonging to itself. In particular, the type
`Type`{.Agda} belongs to a *successor* universe `Type₁`{.Agda}, and, in
general, the $\ell$-th universe lives in the $(\ell + 1)$st universe.

```agda
_ : Type₁
_ = Type

_ : (ℓ : Level) → Type (lsuc ℓ)
_ = λ ℓ → Type ℓ
```

Every fibrant type lives in exactly one universe, so we can recover by
unification the `Level`{.Agda} of a given type.

```agda
level-of : {ℓ : Level} → Type ℓ → Level
level-of {ℓ} _ = ℓ
```

The built-in universes are furthermore all **predicative**, which in
this context means that the *domain* of a family of types also
influences the universe level at which the product of that family lives.
To express this, `Level`{.Agda}s are closed under a binary "max"
operator `_⊔_`{.Agda}.

```agda
_ : ∀ {ℓ ℓ'} (A : Type ℓ) → (A → Type ℓ') → Type (ℓ ⊔ ℓ')
_ = λ A B → ((x : A) → B x)
```

## Lifting

We have mentioned that every fibrant type lives in exactly one universe.
This is to say that our universes are not **cumulative**. Instead, we
can define (as a `record`{.Agda} type) a map which `Lift`{.Agda}s a type
to a higher universe. Considered as a function between universes,
`Lift`{.Agda} is an [[embedding]]. Moreover, the `Lift`{.Agda} of a type
is *definitionally isomorphic* to that type.

```agda
record Lift {a} ℓ (A : Type a) : Type (a ⊔ ℓ) where
  constructor lift
  field
    lower : A
```

<!--
```agda
open Lift public

instance
  Lift-instance : ∀ {ℓ ℓ'} {A : Type ℓ} → ⦃ A ⦄ → Lift ℓ' A
  Lift-instance ⦃ x ⦄ = lift x
```
-->

## Built-in type formers

The `Type`{.Agda} universes are closed under `Σ`{.Agda}, and the lowest
universe contains both the [[natural numbers]] `Nat`{.Agda} and the
[[booleans]] `Bool`{.Agda}.

<!--
```agda
open import Prim.Data.Sigma public
open import Prim.Data.Bool public
open import Prim.Data.Nat hiding (_<_; _≤_) public

_ = Bool
_ = Nat
```
-->

```agda
_ : ∀ {ℓ ℓ'} (A : Type ℓ) → (A → Type ℓ') → Type (ℓ ⊔ ℓ')
_ = Σ
```

:::{.definition #product-type}
The non-dependent **product type** `_×_`{.Agda} can be defined in terms
of the dependent sum type, `Σ`{.Agda}.
:::

```agda
_×_ : ∀ {a b} → Type a → Type b → Type _
A × B = Σ[ _ ∈ A ] B

infixr 5 _×_
```

# Auxilliary universes

Our type theory has a couple more families of universes that serve to
support the formalisation. Above, we wrote down a function type where
the *universe* at which the codomain lives depends on the input value.
These "large" products are classified in `Typeω`. These "limit"
universes are themselves organised into a hierarchy, but, unlike
`Type`{.Agda}, the indexing of this hierarchy is *external*: the
subscript in `Typeω₁`{.Agda} is a literal number, and not shorthand for
a value of some type.

```agda
_ : Typeω
_ = (ℓ : Level) → Type (lsuc ℓ)

_ : Typeω₁
_ = Typeω
```

The `Type`{.Agda} universes also code for universes of **strict**
[[propositions]], that is, types which have at most one inhabitant *up
to definitional equality*. We write these universes as `SProp`{.Agda}.
As with `Type`{.Agda}, these are *predicative*, in that, while the
product of a `SProp`{.Agda}-valued family will again live in *a*
`SProp`{.Agda}, the level of the result depends on both the domain and
codomain.

```agda
_ : ∀ {ℓ} → Type (lsuc ℓ)
_ = SProp _
```

## Some strict propositions

We populate the smallest `SProp`{.Agda} universe with analogues of the
unit and empty types. These enjoy the property that any of their
inhabitants, even hypothetical, are definitionally equal.

```agda
record ⊤ˢ : SProp where
  instance constructor ttˢ

data ⊥ˢ : SProp where
```

The empty `Type`{.Agda}, `⊥`{.Agda}, is defined by lifting the empty
`SProp`{.Agda}. Since `⊥`{.Agda} is an `eta-equality record`{.Agda}
type, it "inherits" definitional irrelevance from `⊥ˢ`{.Agda}.

```agda
record ⊥ : Type where
  constructor liftˢ
  field lowerˢ : ⊥ˢ
```

Even defined like this, the empty type has an elimination principle into
arbitrary types. We define an eliminator `absurd`{.Agda} valued in small
fibrant types. To demonstrate that the codomain can be arbitrary, we can
also define `absurdω`{.Agda}.

```agda
absurd : ∀ {ℓ} {A : Type ℓ} → ⊥ → A
absurd ()

absurdω : {A : Typeω} → ⊥ → A
absurdω ()
```

The **negation** of a type $A$ is, as usual, the type of functions $A
\to \bot$. With our setup, the negation of an arbitrary type is
definitionally proof-irrelevant.

```agda
¬_ : ∀ {ℓ} → Type ℓ → Type ℓ
¬ A = A → ⊥
infix 6 ¬_
```

<!--
```agda
```
-->


# Basic syntactic niceties

We close out this module with the definition of a couple helpers which
do not depend on anything other than quantification over types. First,
we have (dependent) function composition `_∘_`{.Agda}, and the identity
function `id`{.Agda}.

```agda
_∘_
  : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Type ℓ₁} {B : A → Type ℓ₂} {C : (x : A) → B x → Type ℓ₃}
  → (f : ∀ {x} → (y : B x) → C x y) (g : ∀ x → B x)
  → ∀ x → C x (g x)
(f ∘ g) z = f (g z)

id : ∀ {ℓ} {A : Type ℓ} → A → A
id x = x
```

We also define two helpers for function application. The first,
`_$_`{.Agda}, is familiar from Haskell, and serves simply to adjust
precedence: one can write `f $ g x` instead of `f (g x)`.

```agda
infixr -1 _$_

_$_ : ∀ {a b} {A : Type a} {B : A → Type b} → ((x : A) → B x) → ((x : A) → B x)
f $ x = f x
```

The second, `case_of_`{.Agda}, is a mixfix operator which constraints
its function argument to be nondependent, which enables type inference.
When given a pattern-matching lambda as its second argument,
`case_of_`{.Agda} can be used to scrutinise a value in an expression
context.

```agda
case_of_ : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → A → (A → B) → B
case x of f = f x

_ : Bool → Bool
_ = λ x → case x of λ where
  true  → false
  false → true
```

Finally, the 1Lab makes extensive use of instance arguments for
automation. A convenient entry point to this automation is the
`auto`{.Agda} function, which can be used to call instance search where
a visible argument is expected.

```agda
auto : ∀ {ℓ} {A : Type ℓ} → ⦃ A ⦄ → A
auto ⦃ a ⦄ = a
```

<!--
```agda
{-# INLINE id #-}
{-# INLINE _$_ #-}

infixr 40 _∘_
infixr -1 _$ₛ_

_$ₛ_ : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : A → SSet ℓ₂} → ((x : A) → B x) → ((x : A) → B x)
f $ₛ x = f x
{-# INLINE _$ₛ_ #-}
```
-->

<!--
```agda
open import Prim.Literals public

∘-closed
  : (∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → (A → B) → Type (ℓ ⊔ ℓ')) → Typeω
∘-closed P =
  ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''}
    {f : B → C} {g : A → B}
  → P f → P g → P (f ∘ g)

caseω_of_ : ∀ {ℓ'} {A : Typeω} {B : Type ℓ'} → A → (A → B) → B
caseω x of f = f x

case_return_of_ : ∀ {ℓ ℓ'} {A : Type ℓ} (x : A) (B : A → Type ℓ') (f : (x : A) → B x) → B x
case x return P of f = f x

{-# INLINE case_of_        #-}
{-# INLINE case_return_of_ #-}

instance
  Number-Lift : ∀ {ℓ ℓ'} {A : Type ℓ} → ⦃ Number A ⦄ → Number (Lift ℓ' A)
  Number-Lift {ℓ' = ℓ'} ⦃ a ⦄ .Number.Constraint n = Lift ℓ' (a .Number.Constraint n)
  Number-Lift ⦃ a ⦄ .Number.fromNat n ⦃ lift c ⦄ = lift (a .Number.fromNat n ⦃ c ⦄)

infixr -1 primForce
primitive
  primForce : ∀ {a b} {A : Type a} {B : A → Type b} (x : A) (f : ∀ x → B x) → B x

syntax primForce x f = f $! x
```
-->
