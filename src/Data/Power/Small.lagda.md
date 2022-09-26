```agda
open import 1Lab.Prelude

module Data.Power.Small where
```

# Small power sets

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
way that does not break computation (too hard). Note that this is still
unsafe --- Agda's termination checker relies on predicativity --- so it
is just as unsafe as having a postulate, but with better computational
properties.

```agda
{-# NO_UNIVERSE_CHECK #-}
record Ω ℓ : Type ℓ where
  no-eta-equality
  field
    ∣_∣ : Type ℓ
    is-tr : is-prop ∣_∣

open Ω public
```

The type `Ω`{.Agda} acts as a subobject classifier, making the category
of $\kappa$-small sets into an elementary topos.

```agda
record _↔_ {ℓ} (A B : Ω ℓ) : Type ℓ where
  constructor bi
  field
    to   : ∣ A ∣ → ∣ B ∣
    from : ∣ B ∣ → ∣ A ∣

  to-equiv : is-equiv to
  to-equiv .is-eqv y .centre = from y , B .is-tr _ _
  to-equiv .is-eqv y .paths x =
    Σ-prop-path (λ _ → is-prop→is-set (B .is-tr) _ _)
      (A .is-tr _ _)
module Bi = _↔_
open Bi

Ω-univalence : ∀ {ℓ} → is-identity-system {A = Ω ℓ} _↔_ λ a → bi (λ x → x) (λ x → x)
Ω-univalence .to-path biimp i .∣_∣ = ua (_ , Bi.to-equiv biimp) i
Ω-univalence .to-path {a} {b} biimp i .is-tr =
  is-prop→pathp (λ i → is-hlevel-is-prop {A = ua (_ , Bi.to-equiv biimp) i} 1)
    (a .is-tr)
    (b .is-tr) i
Ω-univalence .to-path-over p i .to x =
  outS (ua-glue (p .to , Bi.to-equiv p) i (λ _ → x) (inS (p .to x)))
Ω-univalence .to-path-over {a} p i .from x = hcomp (∂ i) λ where
  j (j = i0) → p .from (outS (ua-unglue (p .to , Bi.to-equiv p) i x))
  j (i = i0) → a .is-tr (p .from (p .to x)) x j
  j (i = i1) → p .from x

Ω-ua : ∀ {ℓ} {A B : Ω ℓ} → A ↔ B → A ≡ B
Ω-ua = Ω-univalence .to-path

instance
  H-Level-Ω : ∀ {ℓ} {n} → H-Level (Ω ℓ) (2 + n)
  H-Level-Ω = basic-instance 2 $ identity-system→hlevel 1 Ω-univalence p where
    p : ∀ {ℓ} (x y : Ω ℓ) (p q : x ↔ y) → p ≡ q
    p x y p q i .to a = y .is-tr (p .to a) (q .to a) i
    p x y p q i .from a = x .is-tr (p .from a) (q .from a) i
