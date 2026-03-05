<!--
```agda
open import 1Lab.Prelude

open import Data.Partial.Total
open import Data.Partial.Base
open import Data.Fin.Base hiding (_<_ ; _≤_)
open import Data.Nat.Base
open import Data.Vec.Base

open import Realisability.PCA
```
-->

```agda
module Realisability.PCA.Sugar {ℓ} (𝔸 : PCA ℓ) where
```

<!--
```agda
private variable
  ℓ' ℓ'' : Level

open PCA 𝔸 public
```
-->

# Sugar for programming in PCAs {defines="syntax-sugar-for-pcas"}

This module defines useful *meta*programs for writing [[values and
programs|values in a pca]] in a [[partial combinatory algebra]] $\bA$.
It is thus primarily interesting to the reader who cares about the
details of the formalisation, rather than its extensional mathematical
content.

We start by defining an overloaded version of the application operator
on $\bA$ which supports any argument that can be coerced to a partial
element of $\bA$--- so we can write things like $x \star y$ even when $x
: \bA$ is a literal element, or $y : \zap^+ \bA$ is a [[total partial
element]] of $\bA$.

```agda
_⋆_
  : ∀ {X : Type ℓ'} {Y : Type ℓ''} ⦃ _ : To-part X ⌞ 𝔸 ⌟ ⦄ ⦃ _ : To-part Y ⌞ 𝔸 ⌟ ⦄
  → X → Y → ↯ ⌞ 𝔸 ⌟
f ⋆ x = to-part f % to-part x where open To-part ⦃ ... ⦄
```

## Parametric higher-order abstract syntax

To conveniently use the abstraction elimination on $\bA$, we will define
a **parametric higher-order abstract syntax** for terms in $\bA$. PHOAS
is an approach to representing syntax with binding which parametrises
over a type $V$ of variables, and represents object-level binders with
meta-level binders.

```agda
data Termʰ (V : Type) : Type ℓ where
  var   : V → Termʰ V
  const : ↯⁺ ⌞ 𝔸 ⌟ → Termʰ V
  app   : Termʰ V → Termʰ V → Termʰ V
  lam   : (V → Termʰ V) → Termʰ V
```

We will primarily use terms where the type of variables is taken to be
the natural numbers, standing for de Bruijn *levels*. Since we can
perform case analysis on natural numbers, not every PHOAS `Termʰ`{.Agda}
with natural-number values will represent an actual `Term`{.Agda} in the
language of $\bA$. We introduce a well-foundedness predicate `wf`{.Agda}
on PHOAS terms, given a context size $\Gamma$, which asserts that every
variable is actually in scope (and thus can be converted to a de Bruijn
*index* in $\Gamma$).

```agda
private
  wf : Nat → Termʰ Nat → Type
  wf Γ (var k)   = Γ - suc k < Γ
  wf Γ (const a) = ⊤
  wf Γ (app f x) = wf Γ f × wf Γ x
  wf Γ (lam b)   = wf (suc Γ) (b Γ)
```

Note that `wf`{.Agda} is defined by recursion, rather than by induction,
so that all of its concrete instances can be filled in by instance
search. We can convert a `wf`{.Agda} PHOAS term in $\Gamma$ to a de
Bruijn term in $\Gamma$. We use levels rather than indices in the PHOAS
representation so that the case for abstractions can call the meta-level
abstraction with the length of the context.

```agda
  from-wf : ∀ {Γ} (t : Termʰ Nat) → wf Γ t → Term ⌞ 𝔸 ⌟ Γ
  from-wf {Γ} (var x) w       = var (fin (Γ - suc x) ⦃ w ⦄)
  from-wf (const x)   w       = const x
  from-wf (app f x) (wf , wx) = app (from-wf f wf) (from-wf x wx)
  from-wf {Γ} (lam f) w       = abs (from-wf (f Γ) w)
```

Finally, we introduce another recursive predicate to be filled in by
instance search indicating whether a term always denotes --- these are
the inclusions of elements from $\bA$ and top-level abstractions.

```agda
  always-denotes : ∀ {V} → Termʰ V → Type
  always-denotes (var x)   = ⊥
  always-denotes (const x) = ⊤
  always-denotes (app f x) = ⊥
  always-denotes (lam x)   = ⊤
```

To use PHOAS terms, we introduce notations for evaluating an arbitrary
expression *and* a term which always denotes, producing a partial or
total-partial element of $\bA$ respectively. Note the *parametricity* in
the argument: to prevent us from writing 'exotic' values of
`Termʰ`{.Agda}, we must work against an arbitrary choice of variable
type. If Agda had internalised parametricity, this would be enough to
prove that the arguments to `expr_`{.Agda} and `val_`{.Agda} must be
well-formed; since we do not have parametricity we instead ask instance
search to fill in the well-formedness (and definedness) assumptions
instead.

```agda
expr_ : (t : ∀ {V} → Termʰ V) ⦃ _ : wf 0 t ⦄ → ↯ ⌞ 𝔸 ⌟
expr_ t ⦃ i ⦄ = eval {n = 0} (from-wf t i) []

val_
  : (t : ∀ {V} → Termʰ V) ⦃ _ : wf 0 t ⦄
  → ⦃ _ : always-denotes {Nat} t ⦄ → ↯⁺ ⌞ 𝔸 ⌟
val_ t ⦃ i ⦄ =
  record
    { fst = eval {n = 0} (from-wf t i) []
    ; snd = d t
    }
  where abstract
  d : (t : Termʰ Nat) ⦃ i : wf 0 t ⦄ ⦃ _ : always-denotes t ⦄ → ⌞ eval {n = 0} (from-wf t i) [] ⌟
  d (const x) = x .snd
  d (lam x) = abs↓ (from-wf (x 0) _) []
```

Finally, we introduce a notation class `To-term`{.Agda} to overload the
construction of applications and abstractions in PHOAS terms.

```agda
record To-term {ℓ'} (V : Type) (X : Type ℓ') : Type (ℓ ⊔ ℓ') where
  field to : X → Termʰ V

instance
  var-to-term : ∀ {V} → To-term V V
  var-to-term = record { to = var }

  const-to-term' : ∀ {V} → To-term V ⌞ 𝔸 ⌟
  const-to-term' = record { to = λ x → const (pure x , tt) }

  const-to-term : ∀ {V} → To-term V (↯⁺ ⌞ 𝔸 ⌟)
  const-to-term = record { to = const }

  term-to-term : ∀ {V} → To-term V (Termʰ V)
  term-to-term = record { to = λ x → x }

_`·_
  : ∀ {ℓ' ℓ''} {V : Type} {A : Type ℓ'} {B : Type ℓ''}
  → ⦃ _ : To-term V A ⦄ ⦃ _ : To-term V B ⦄
  → A → B → Termʰ V
f `· x = app (to f) (to x) where open To-term ⦃ ... ⦄

lam-syntax : ∀ {ℓ} {V : Type} {A : Type ℓ} ⦃ _ : To-term V A ⦄ → (V → A) → Termʰ V
lam-syntax f = lam λ x → to (f x) where open To-term ⦃ ... ⦄

syntax lam-syntax (λ x → e) = ⟨ x ⟩ e

infixl 25 _`·_
infixl 35 _⋆_
```
