<!--
```agda
open import 1Lab.Prelude

open import Data.Partial.Base
open import Data.Nat.Base
open import Data.Power using (ℙ)
```
-->

```agda
module Data.Partial.Total where
```

<!--
```agda
private variable
  ℓ ℓ' ℓ'' : Level
  A B C X Y : Type ℓ
```
-->

# Total partial elements {defines="total-partial-element"}

An important property of the [[partial elements]] $x : \zap A$ is that
if $x$ is defined, then it is necessarily the inclusion of a unique
*total* value $x' : A$. However, when formalising, we have to contend
with the following infelicity: if we start with a partial element $x :
\zap A$, extract an underlying value $x' : A$ by proving that it is
defined, and then subsequently weaken $x'$ back to a partial element, we
do not *definitionally* end up back with $x$.

This turns into a compound annoyance when we're dealing with partial
operators, like those of a [[partial combinatory algebra]], since we
want to ergonomically build complex expressions--- which entails
'lifting' a partial operator $A \to A \to \zap A$ to a binary operation
on $\zap A$ using the monadic structure of $\zap(-)$--- but the
properties that control these operators only apply when the domains are
actually defined. We would thus have to insert tons of mediating
identifications between a (defined) partial element and the inclusion of
its underlying value.

A better approach from the perspective of formalisation is thus to
*delay projecting the underlying value* as long as possible. Instead, we
prefer to work with partial elements and carry the proofs that they are
defined 'off to the side'. To make this precise, we define a type
$\zap^+ A$ of **defined partial elements** of $A$, which, extensionally,
is just $A$ again; but which, intensionally, lets us definitionally
recover a partial $x : \zap A$ after proving that it is defined, by
merely projecting out the underlying partial element.

```agda
↯⁺ : ∀ {ℓ} {X : Type ℓ} ⦃ u : Underlying X ⦄ → X → Type _
↯⁺ A = Σ[ a ∈ ↯ ⌞ A ⌟ ] ⌞ a ⌟
```

<!--
```agda
instance
  part⁺-to-part : To-part (↯⁺ A) A
  part⁺-to-part = record { to-part = fst }

  ↯⁺-Map : Map (eff ↯⁺)
  ↯⁺-Map .Map.map f (x , hx) = part-map f x , hx

  ↯⁺-Idiom : Idiom (eff ↯⁺)
  ↯⁺-Idiom .Idiom.Map-idiom = ↯⁺-Map
  ↯⁺-Idiom .Idiom.pure x    = always x , tt
  ↯⁺-Idiom .Idiom._<*>_ (f , hf) (x , hx) = part-ap f x , hf , hx

  Extensional-↯⁺ : ⦃ _ : Extensional (↯ A) ℓ ⦄ → Extensional (↯⁺ A) ℓ
  Extensional-↯⁺ ⦃ e ⦄ = embedding→extensional (fst , Subset-proj-embedding (λ _ → hlevel 1)) e

  abstract
    H-Level-↯⁺ : ∀ {A : Type ℓ} {n} ⦃ _ : 2 ≤ n ⦄ ⦃ _ : H-Level A n ⦄ → H-Level (↯⁺ A) n
    H-Level-↯⁺ {n = suc (suc n)} ⦃ s≤s (s≤s p) ⦄ = hlevel-instance $
      embedding→is-hlevel (1 + n) (Subset-proj-embedding λ _ → hlevel 1) (hlevel (2 + n))

    {-# OVERLAPPING H-Level-↯⁺ #-}
```
-->

It's actually very easy to prove that this type is equivalent to $A$,
which at a glance might call its utility into question --- but it will
be extensively used in the development of realisability.

```agda
from-total : ↯⁺ A → A
from-total (a , ha) = a .elt ha

from-total-is-equiv : is-equiv (from-total {A = A})
from-total-is-equiv = is-iso→is-equiv record where
  from x       = pure x
  rinv _       = refl
  linv (x , a) = Σ-prop-path! (sym (is-always x a))
```

<!--
```agda
private module def where
```
-->

## Total power sets

We can perform a similar replacement to the power set $\bP A$, pairing a
predicate on *partial* elements $P \sube \zap A$ with a proof that every
member of $P$ is defined. Again, this is equivalent to $\bP A$, but it
lets us talk directly about the membership of partial elements in $P$,
even those which are not *a priori* known to be defined.

```agda
  record ℙ⁺ (A : Type ℓ) : Type ℓ where
    field
      mem     : ↯ A → Ω
      defined : ∀ {a} → ⌞ mem a ⌟ → ⌞ a ⌟
```

<!--
```agda
private unquoteDecl eqv = declare-record-iso eqv (quote def.ℙ⁺)

ℙ⁺ : ∀ {ℓ} {X : Type ℓ} ⦃ u : Underlying X ⦄ → X → Type _
ℙ⁺ X = def.ℙ⁺ ⌞ X ⌟

open def using (module ℙ⁺) public
open def.ℙ⁺ public

{-# DISPLAY def.ℙ⁺ X = ℙ⁺ X #-}

open is-iso

instance
  Membership-ℙ⁺ : ⦃ _ : To-part X A ⦄ → Membership X (def.ℙ⁺ A) _
  Membership-ℙ⁺ = record { _∈_ = λ a p → ⌞ p .mem (to-part a) ⌟ } where open To-part ⦃ ... ⦄

  Extensional-ℙ⁺ : ∀ {ℓr} ⦃ _ : Extensional (↯ A → Ω) ℓr ⦄ → Extensional (def.ℙ⁺ A) ℓr
  Extensional-ℙ⁺ ⦃ e ⦄ = injection→extensional! (λ p → Iso.injective eqv (Σ-prop-path! p)) e

  H-Level-ℙ⁺ : ∀ {n} → H-Level (def.ℙ⁺ A) (2 + n)
  H-Level-ℙ⁺ = basic-instance 2 (Iso→is-hlevel 2 eqv (hlevel 2))
```
-->

Of course, if we have a predicate $P \sube A$, we can extend it to a $P'
\sube \zap A$ defined on partial elements by defining $x \in P'$ to mean
"$x$ is defined and the projection of $x$ onto $A$ belongs to $P$".  By
construction, every member of $P'$ is defined.

```agda
from-total-predicate : ℙ A → ℙ⁺ A
from-total-predicate P .mem x = el (Σ[ hx ∈ x ] x .elt hx ∈ P) (hlevel 1)
from-total-predicate P .defined (hx , _) = hx

from-total-predicate-is-equiv : is-equiv (from-total-predicate {A = A})
from-total-predicate-is-equiv = is-iso→is-equiv record where
  from P a = P .mem (always a)
  rinv P = ext λ a → Ω-ua
    (rec! λ ha → subst (_∈ P) (sym (is-always a ha)))
    (λ pa → P .defined pa , subst (_∈ P) (is-always a _) pa)
  linv P = ext λ a → Ω-ua snd (tt ,_)
```

<!--
```agda
singleton⁺ : ↯⁺ A → ℙ⁺ A
singleton⁺ x .mem y = elΩ (x .fst ≡ y)
singleton⁺ x .defined = rec! λ p → subst ⌞_⌟ p (x .snd)
```
-->
