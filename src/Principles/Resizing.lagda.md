```agda
open import 1Lab.Reflection
open import 1Lab.Prelude
open import 1Lab.Rewrite

open import Data.List

module Principles.Resizing where
```

# Propositional Resizing

Ordinarily, the collection of all $\kappa$-small predicates on
$\kappa$-small types lives in the next universe up, $\kappa^+$. This is
because _predicates_ are not special in type theory: they are ordinary
type families, that just so happen to be valued in \r{propositions}. For
most purposes we can work with this limitation: this is called
**predicative mathematics**. But, for a few classes of theorems,
predicativity is too restrictive: Even if we don't have a single
universe of propositions that can accomodate all predicates, we would
still like for universes to be closed under power-sets.

Using some of Agda's more suspicious features, we can achieve this in a
way which does not break computation too much. Specifically, we'll use a
combination of `NO_UNIVERSE_CHECK`, postulates, and rewrite rules.

We start with the `NO_UNIVERSE_CHECK` part: We define the **small type
of propositions**, `Ω`, to be a record containing a `Type` (together
with an irrelevant proof that this type is a proposition), but contrary
to the universe checker, which would like us to put `Ω : Type₁`, we
instead force `Ω : Type`.

```agda
{-# NO_UNIVERSE_CHECK #-}
record Ω : Type where
  constructor el
  field
    ∣_∣   : Type
    is-tr : is-prop ∣_∣
open Ω public
```

This type, a priori, only contains the propositions whose underlying
type lives in the first universe. What we do now is introduce a few
postulates allowing us to show _any_ proposition is (equivalent to) one
in the first universe. We do this with a quintuple of postulates: The
type `resized`{.Agda}, its constructor `box`{.Agda}, its eliminator
`out`{.Agda}, and the computation rules, expressing that `box`{.Agda} is
a (definitional) isomorphism.

```agda
postulate
  resized : ∀ {ℓ} (T : Type ℓ) (p : is-prop T) → Type
  box     : ∀ {ℓ} {T : Type ℓ} {p : is-prop T} → T → resized T p
  out     : ∀ {ℓ} {T : Type ℓ} {p : is-prop T} → resized T p → T
  resize-box-out
    : ∀ {ℓ} {T : Type ℓ} (p : is-prop T) x → box (out {p = p} x) ≡rw x
  resize-out-box
    : ∀ {ℓ} {T : Type ℓ} (p : is-prop T) x → out (box {p = p} x) ≡rw x

{-# REWRITE resize-box-out resize-out-box #-}

resized-is-prop
  : ∀ {ℓ} {T : Type ℓ} (p : is-prop T)
  → is-prop (resized T p)
resized-is-prop p = retract→is-prop box out (λ _ → refl) p
```

<!--
```agda
instance
  H-Level-resized
    : ∀ {ℓ} {T : Type ℓ} {p : is-prop T} {n} → H-Level (resized T p) (suc n)
  H-Level-resized = prop-instance (resized-is-prop _)

  open hlevel-projection
  Ω-hlevel-proj : hlevel-projection
  Ω-hlevel-proj .underlying-type = quote Ω.∣_∣
  Ω-hlevel-proj .has-level = quote Ω.is-tr
  Ω-hlevel-proj .get-level x = pure (quoteTerm (suc zero))
  Ω-hlevel-proj .get-argument (arg _ t ∷ _) = pure t
  Ω-hlevel-proj .get-argument _ = typeError []
```
-->

We can also prove a univalence principle for `Ω`{.Agda}:

```agda
Ω-ua : {A B : Ω} → (∣ A ∣ → ∣ B ∣) → (∣ B ∣ → ∣ A ∣) → A ≡ B
Ω-ua {A} {B} f g i .∣_∣ = ua (prop-ext! f g) i
Ω-ua {A} {B} f g i .is-tr =
  is-prop→pathp (λ i → is-prop-is-prop {A = ua (prop-ext! f g) i})
    (A .is-tr) (B .is-tr) i

instance abstract
  H-Level-Ω : ∀ {n} → H-Level Ω (2 + n)
  H-Level-Ω = basic-instance 2 $ retract→is-hlevel 2
    (λ r → el ∣ r ∣ (r .is-tr))
    (λ r → el ∣ r ∣ (r .is-tr))
    (λ x → Ω-ua (λ x → x) λ x → x)
    (n-Type-is-hlevel {lzero} 1)
```

We also provide a shortened version of `resized` which automatically
derives the proof of propositionality, using the hlevel tactic, and a
shortening of `el`{.Agda} which automatically resizes its argument type.

```agda
□ : ∀ {ℓ} (T : Type ℓ) {@(tactic hlevel-tactic-worker) p : is-prop T}
  → Type
□ T {p} = resized T p

elΩ : ∀ {ℓ} (T : Type ℓ) {@(tactic hlevel-tactic-worker) p : is-prop T}
    → Ω
∣ elΩ T {p = p} ∣ = □ T {p}
elΩ T .is-tr = resized-is-prop _

{-# DISPLAY resized T p = □ T #-}
```
