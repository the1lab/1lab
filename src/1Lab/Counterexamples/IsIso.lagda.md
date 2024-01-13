---
description: |
    By counter example we show that is-iso is not a proposition.
---
<!--
```agda
open import 1Lab.HLevel.Retracts
open import 1Lab.Path.Groupoid
open import 1Lab.Univalence
open import 1Lab.HLevel
open import 1Lab.Equiv
open import 1Lab.Path
open import 1Lab.Type

open import Homotopy.Space.Circle
```
-->

```agda
module 1Lab.Counterexamples.IsIso where
```

# is-iso is not a proposition

We show that if `is-iso`{.Agda} were a [[proposition]], then `(x : A) →
x ≡ x` would be contractible for any choice of `A`. Taking `A` to be
`S¹`{.Agda}, we show that this can not be the case. Suppose that is-iso
is a proposition.

```agda
module
  _ (iso-is-prop : ∀ {ℓ} {A B : Type ℓ} {f : A → B} → is-prop (is-iso f))
  where
```

First we characterise the type `is-iso f`{.Agda ident=is-iso} by showing
that, if it is inhabited, then it is equivalent to the _centre_ of `A`,
i.e. the loop-assigning maps of `A`:

```agda
  lemma : ∀ {ℓ} {A B : Type ℓ} {f : A → B} → is-iso f → is-iso f ≃ ((x : A) → x ≡ x)
  lemma {A = A} {B} {f} iiso =
    EquivJ (λ _ f → is-iso (f .fst) ≃ ((x : A) → x ≡ x))
           (Iso→Equiv helper)
           (f , is-iso→is-equiv iiso)
    where
```

By [equivalence induction], it suffices to cover the case where `f` is
the identity function. In that case, we can construct an isomorphism
quite readily, where the proof uses our assumption `iso-is-prop`{.Agda} for
convenience.

[equivalence induction]: 1Lab.Univalence.html#equivalence-induction

```agda
      helper : Iso _ _
      helper .fst iiso x =
        sym (iiso .is-iso.linv x) ∙ iiso .is-iso.rinv x
      helper .snd .is-iso.inv x = iso (λ x → x) x (λ _ → refl)
      helper .snd .is-iso.rinv p = funext λ x → ∙-idl _
      helper .snd .is-iso.linv x = iso-is-prop _ _
```

We thus have that `is-iso id ≃ ((x : A) → x ≡ x)` - since the former is a
prop (by assumption), then so is the latter:

```agda
  is-prop-loops : ∀ {ℓ} {A : Type ℓ} → is-prop ((x : A) → x ≡ x)
  is-prop-loops {A = A} = equiv→is-hlevel 1 (helper .fst) (helper .snd) iso-is-prop
    where helper = lemma {f = λ (x : A) → x}
                     (iso (λ x → x) (λ x → refl) (λ x → refl))
```

Thus, it suffices to choose a type for which `(x : A) → x ≡ x` has two
distinct elements. We go with the circle, `S¹`{.Agda}:

```agda
  ¬is-prop-loops : ¬ is-prop ((x : S¹) → x ≡ x)
  ¬is-prop-loops prop = refl≠loop $
    happly (prop (λ x → refl)
      λ { base → loop
        ; (loop i) j → hcomp (∂ i ∨ ∂ j) λ where
            k (k = i0) → loop (i ∨ j)
            k (i = i0) → loop j
            k (i = i1) → loop (k ∧ j)
            k (j = i0) → loop i
            k (j = i1) → loop (k ∧ i)
        })
      base
```

Hence, a contradiction:

```agda
  contra : ⊥
  contra = ¬is-prop-loops is-prop-loops
```
