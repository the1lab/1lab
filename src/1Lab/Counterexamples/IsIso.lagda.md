```agda
open import 1Lab.HLevel.Retracts
open import 1Lab.Path.Groupoid
open import 1Lab.Univalence
open import 1Lab.HIT.S1
open import 1Lab.HLevel
open import 1Lab.Equiv
open import 1Lab.Path
open import 1Lab.Type

module 1Lab.Counterexamples.IsIso where
```

# isIso is not a proposition

We show that if `isIso`{.Agda} were a proposition, then `(x : A) → x ≡
x` would be contractible for any choice of `A`. Taking `A` to be
`S¹`{.Agda}, we show that this can not be the case. Suppose that isIso is a proposition.

```agda
module
  _ (isoProp : ∀ {ℓ} {A B : Type ℓ} {f : A → B} → isProp (isIso f))
  where
```

First we characterise the type `isIso f`{.Agda ident=isIso} by showing
that, if it is inhabited, then it is equivalent to the _centre_ of `A`,
i.e. the loop-assigning maps of `A`:

```agda
  lemma : ∀ {ℓ} {A B : Type ℓ} {f : A → B} → isIso f → isIso f ≃ ((x : A) → x ≡ x)
  lemma {A = A} {B} {f} iiso = 
    EquivJ (λ _ f → isIso (f .fst) ≃ ((x : A) → x ≡ x))
           (Iso→Equiv helper)
           (f , isIso→isEquiv iiso)
    where
```

By [equivalence induction], it suffices to cover the case where `f` is
the identity function. In that case, we can construct an isomorphism
quite readily, where the proof uses our assumption `isoProp`{.Agda} for
convenience.

[equivalence induction]: 1Lab.Univalence.html#consequences

```agda
      helper : Iso _ _
      helper .fst iiso x =
        sym (iiso .isIso.linv x) ∙ iiso .isIso.rinv x
      helper .snd .isIso.inv x = iso (λ x → x) x (λ _ → refl)
      helper .snd .isIso.rinv p = funext λ x → ∙-id-l _
      helper .snd .isIso.linv x = isoProp _ _
```

We thus have that `isIso id ≃ ((x : A) → x ≡ x)` - since the former is a
prop (by assumption), then so is the latter:

```agda
  isProp-loops : ∀ {ℓ} {A : Type ℓ} → isProp ((x : A) → x ≡ x)
  isProp-loops {A = A} = isHLevel-equiv 1 (helper .fst) (helper .snd) isoProp
    where helper = lemma {f = λ (x : A) → x}
                     (iso (λ x → x) (λ x → refl) (λ x → refl))
```

Thus, it suffices to choose a type for which `(x : A) → x ≡ x` has two
distinct elements. We go with the circle, `S¹`{.Agda}:

```agda
  ¬isProp-loops : isProp ((x : S¹) → x ≡ x) → ⊥
  ¬isProp-loops prop = refl≠loop (happly (prop (λ x → refl) always-loop) base)
```

Hence, a contradiction:

```agda
  contra : ⊥
  contra = ¬isProp-loops isProp-loops
```
