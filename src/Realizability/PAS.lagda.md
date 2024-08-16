---
description: |
  Partial applicative systems.
---
<!--
```agda
open import Order.Base

open import 1Lab.Prelude

open import Data.Vec.Base
open import Data.Fin
```
-->
```agda
module Realizability.PAS where
```

# Partial applicative structures

When we do any sort of mathematics that touches on ideas involving
computation, we first need to pin down exactly what computation *is*.
This involves picking a particular model of computation (Turing machines,
Post systems, lambda calculus, etc). If we are just interested in
computability itself, then we want to pick the simplest model of computation
possible that is still reasonable to work with.

Automaton-based models can be ruled out almost immediately: writing programs
is extremely tedious, and we would spend most of our time wallowing in
a Turing tarpit. Lambda calculi are more promising, but are still a bit
difficult to work with formally: variable binding and substitution is
complicated!

We can avoid these difficulties by eschewing the use of variables altogether:
this leads directly to combinatory models of computation. Like lambda calculi,
these models are fundamentally about application and equations. However,
they differ in their treatment of functions: lambdas are replaced with
distinguished elements with associated equations. If we are clever enough
with our choices of equations, then we can interpret any lambda term!

Moreover, we can take an algebraic view of combinator calculi: instead
of working against some sort of term model, we can consider sets that
have a sort of "application" operation, along with elements that stand
in for combinators in the term model.

Traditionally, this structure is encoded as a set $A$ equipped with a
partial[^1] binary operation $\star : A \times A \rightharpoonup A$. Unfortunately,
this is quite difficult to work with in a proof assistant. If we use
the [[partiality monad]], then we will constantly have to reason about
the algebraic structure of the monad on top of any combinator algebra,
which adds an unacceptable layer of overhead[^2]. Conversely, using a partial
functional relations means that we no longer can work with functions: this
also grinds any formalization effort to a halt.

[^1]: We need partiality to be able to model turing-complete models
of computation.
[^2]: This becomes particularly bad when we need to worry about the
order in which we perform binds. In essence, this approach is like doing
small-step semantics, but we do not want nor need this level of granularity!

With these problems in mind, we opt for a third approach: instead of working
with functions into the partial map classifier, we tack on a predicate
$\downarrow : A \to \Omega$ that is meant to denote that an element
is defined. Moreover, we require that all functions *reflect* definedness.
This may seem somewhat odd at first glance, but it is the correct behavior
for a strict model of computation: if $f(a)$ is defined, then $a$ must
also have been defined! This leads us to the following definition.

:::{.definition #partial-applicative-structure alias="pas"}
A **partial applicative structure** or **PAS** is a set $A$ equipped
with a predicate $\downarrow : A \to \Omega$ and a binary operation $\star : A \to A \to A$
that satisifies the following conditions:

- Strictness: For all $a, b : A$, $(a \star b) \downarrow \to a \downarrow \times b \downarrow$
- Non-triviality: There merely exists some $a : A$ with $a \downarrow$
- Kleene extensionality: For all $a, b : A$, if $a \downarrow \simeq b \downarrow$ and $a \downarrow \to b \downarrow \to a = b$,
  then $a = b$.
:::


<!--
```agda
private variable
  ℓ ℓ' ℓ'' : Level
  A : Type ℓ
  k n : Nat
```
-->

```agda
record is-pas {A : Type ℓ} (_⋆_ : A → A → A) (_↓ : A → Ω) : Type ℓ where
  field
    ⋆-defl : ∀ {a b} → ∣ (a ⋆ b) ↓ ∣ → ∣ a ↓ ∣
    ⋆-defr : ∀ {a b} → ∣ (a ⋆ b) ↓ ∣ → ∣ b ↓ ∣
    kleene-ext : ∀ {a b} → ∣ a ↓ ∣ ≃ ∣ b ↓ ∣ → (∣ a ↓ ∣ → ∣ b ↓ ∣ → a ≡ b) → a ≡ b
    nonempty : ∃[ a ∈ A ] ∣ a ↓ ∣
    has-is-set : is-set A
```

The final axiom gives a useful extensionality principle for $A$.

```agda
  def-ext : ∀ {a b} → (P : Type ℓ') → (∣ a ↓ ∣ → P) → (∣ b ↓ ∣ → P) → (P → a ≡ b) → a ≡ b
  def-ext P l r h =
    kleene-ext (prop-ext!
         (λ a↓ → subst (λ b → ∣ b ↓ ∣) (h (l a↓)) a↓)
         (λ b↓ → subst (λ a → ∣ a ↓ ∣) (sym (h (r b↓))) b↓))
       (λ a↓ b↓ → h (l a↓))
```

<!--
```agda
is-pas-is-prop
  : {_⋆_ : A → A → A} {_↓ : A → Ω}
  → is-prop (is-pas _⋆_ _↓)
is-pas-is-prop {A = A} {_⋆_ = _⋆_} {_↓ = _↓} pas pas' =
  Iso→is-hlevel 1 eqv (hlevel 1) pas pas'
  where
    unquoteDecl eqv = declare-record-iso eqv (quote is-pas)
    instance
      HLevel-pas : ∀ {n : Nat} → H-Level A (2 + n)
      HLevel-pas = basic-instance 2 (is-pas.has-is-set pas)

```
-->

## Refinement {defines="refinement-order"}

Every partial applicative structure comes equipped with a canonical partial
order given by $a \leq b := a \downarrow \to b \downarrow \times a = b$.
This order is known as the **refinement order** on a PAS, and is the
algebraic analog of the ordering on the type of partial elements.

```agda
module PAS {A : Type ℓ} {_⋆_ : A → A → A} {_↓ : A → Ω} (has-pas : is-pas _⋆_ _↓) where
  open is-pas has-pas public

  _⊑_ : A → A → Type ℓ
  x ⊑ y = ∣ x ↓ ∣ → ∣ y ↓ ∣ × (x ≡ y)
```

Proving that this relation is a preorder is a straightforward exercise.

```agda
  ⊑-refl : ∀ {x : A} → x ⊑ x
  ⊑-refl x↓ = x↓ , refl

  ⊑-thin : ∀ {x y} → is-prop (x ⊑ y)
  ⊑-thin = Π-is-hlevel 1 (λ _ → ×-is-hlevel 1 (hlevel 1) (has-is-set _ _))

  ⊑-trans : ∀ {x y z} → x ⊑ y → y ⊑ z → x ⊑ z
  ⊑-trans p q x↓ = (q (p x↓ .fst) .fst) , p x↓ .snd ∙ q (p x↓ .fst) .snd
```

However, antisymmetry is a bit more surprising! This is where the somewhat
mysterious extensionality axiom gets used. In fact, antisymmetry of the
refinement order is equivalent to the final PAS axiom. In this light,
we can consider Kleene extensionality as a sort of univalence condition
on a PAS.

```agda
  ⊑-antisym : ∀ {x y} → x ⊑ y → y ⊑ x → x ≡ y
  ⊑-antisym {x = x} {y = y} x⊑y y⊑x =
    def-ext (∣ x ↓ ∣ × ∣ y ↓ ∣)
      (λ x↓ → x↓ , x⊑y x↓ .fst)
      (λ y↓ → y⊑x y↓ .fst , y↓)
      (λ (x↓ , y↓) → x⊑y x↓ .snd)
```

<!--
```agda
  Refinement : Poset ℓ ℓ
  Refinement .Poset.Ob = A
  Refinement .Poset._≤_ = _⊑_
  Refinement .Poset.≤-thin = ⊑-thin
  Refinement .Poset.≤-refl = ⊑-refl
  Refinement .Poset.≤-trans = ⊑-trans
  Refinement .Poset.≤-antisym = ⊑-antisym
```
-->

## Defined elements

A **value** in a partial applicative structure $A$ is an element
$a : A$ with $a \downarrow$.

```agda
  record Val : Type ℓ where
    constructor value
    field
      elt : A
      def : ∣ elt ↓ ∣

  open Val public
```

We also define a small typeclass so that we can automate away some
definedness obligations.

```agda
  record Defined (a : A) : Typeω where
    constructor defined-instance
    field
      defined : ∣ a ↓ ∣

  open Defined ⦃...⦄ public

  val : (a : A) → ⦃ Defined a ⦄ → Val
  val a .elt = a
  val a .def = defined
```

<!--
```agda
  Val-is-set : is-set Val
  Val-is-set = Iso→is-hlevel 2 eqv (Σ-is-hlevel 2 has-is-set λ _ → hlevel 2)
    where unquoteDecl eqv = declare-record-iso eqv (quote Val)

  instance
    H-Level-Val : ∀ {n : Nat} → H-Level Val (2 + n)
    H-Level-Val = basic-instance 2 Val-is-set

    Extensional-Val
      : ∀ {ℓr : Level} ⦃ e : Extensional A ℓr ⦄
      → Extensional Val ℓr
    Extensional-Val ⦃ e ⦄ =
      injection→extensional has-is-set val-ext e
      where
         val-ext : ∀ {v₁ v₂ : Val} → v₁ .elt ≡ v₂ .elt → v₁ ≡ v₂
         val-ext {v₁ = v₁} {v₂ = v₂} p i .elt = p i
         val-ext {v₁ = v₁} {v₂ = v₂} p i .def =
           is-prop→pathp (λ i → ((p i) ↓) .is-tr) (v₁ .def) (v₂ .def) i
```
-->

## Diverging elements

Conversely, an element $a : A$ is **divergent** if it is not defined.

```agda
  _↑ : A → Ω
  a ↑ = ¬Ω (a ↓)
```

Application preserves divergent elements.

```agda
  ⋆-divl : ∀ {a} → ∣ a ↑ ∣ → (b : A) → ∣ (a ⋆ b) ↑ ∣
  ⋆-divl a↑ b ab↓ = a↑ (⋆-defl ab↓)

  ⋆-divr : ∀ {b} → (a : A) → ∣ b ↑ ∣ → ∣ (a ⋆ b) ↑ ∣
  ⋆-divr a b↑ ab↓ = b↑ (⋆-defr ab↓)
```

More interestingly, all divergent elements are equal! This is yet
another consequence of Kleene extensionality.

```agda
  diverge-is-prop : ∀ {a b} → ∣ a ↑ ∣ → ∣ b ↑ ∣ → a ≡ b
  diverge-is-prop {a = a} {b = b} a↑ b↑ =
    kleene-ext
      (prop-ext! (λ a↓ → absurd (a↑ a↓)) (λ b↓ → absurd (b↑ b↓)))
      (λ a↓ b↓ → absurd (a↑ a↓))
```

## Terms

A **term** in a PAS consists of a binary tree of values and variables.
We opt to use an intrinsically scoped representation to avoid unnecessary
partiality.

```agda
  data Term : Nat → Type ℓ where
    var : ∀ {n} → Fin n → Term n
    const : ∀ {n} → Val → Term n
    op : ∀ {n} → Term n → Term n → Term n
```

We can interpret terms as functions from vectors of values to elements
of $A$.

```agda
  eval : Term n → Vec Val n → A
  eval (var x) ρ = lookup ρ x .elt
  eval (const v) ρ = v .elt
  eval (op e₁ e₂) ρ = eval e₁ ρ ⋆ eval e₂ ρ

  term : Term 0 → A
  term e = eval e []
```

We also define weakening on terms.

```agda
  shift : Term n → Term (1 + n)
  shift (var x) = var (fsuc x)
  shift (const x) = var fzero
  shift (op e₁ e₂) = op (shift e₁) (shift e₂)
```

Finally, we provide a small DSL for constructing terms that handles
insertion of weakenings automatically.

```agda
  record Splice (A : Type ℓ) {E : Type ℓ'} (e : E) (n : Nat) : Typeω where
    field
      splice : Term n

  instance
    Splice-Const : {a : A} → ⦃ a↓ : Defined a ⦄ → Splice A a n
    Splice-Const {a = a} = record { splice = const (value a defined) }

    Splice-Val : {n : Nat} {v : Val} → Splice A v n
    Splice-Val {v = v} = record { splice = const v }

    Splice-Term : {n : Nat} {e : Term n} → Splice A e n
    Splice-Term {e = e} = record { splice = e }

    Splice-Shift : {n k : Nat} {e : Term n} → ⦃ Splice A e k ⦄ → Splice A e (1 + k)
    Splice-Shift ⦃ s ⦄ = record { splice = shift (Splice.splice s) }

  “_” : {E : Type ℓ'} → (e : E) → ⦃ s : Splice A e n ⦄ → Term n
  “_” e ⦃ s ⦄ = Splice.splice s

  _“⋆”_ : {E₁ : Type ℓ'} {E₂ : Type ℓ''} → (e₁ : E₁) → ⦃ Splice A e₁ n ⦄ → (e₂ : E₂) → ⦃ Splice A e₂ n ⦄ → Term n
  e₁ “⋆” e₂ = op (“ e₁ ”) (“ e₂ ”)

  infixl 6 _“⋆”_
```
