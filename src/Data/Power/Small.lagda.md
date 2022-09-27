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
  constructor el
  field
    ∣_∣ : Type ℓ
    is-tr : is-prop ∣_∣

open Ω public
```

The first thing we'll establish is an \r{identity system} on the small
type of propositions, $\Omega$. This is a special case of transfer along
equivalences (and pullback of) identity systems: but note that since our
construction of `Ω`{.Agda} is _necessarily_ special-cased, we can not
use our regular tools for constructing identity systems.

Our choice of relation is the humble biimplication: a pair of functions
that goes both ways. Between inhabitants of $\Omega$, these are exactly
the equivalences.

```agda
record _↔_ {ℓ} (A B : Ω ℓ) : Type ℓ where
  constructor bi
  field
    to   : ∣ A ∣ → ∣ B ∣
    from : ∣ B ∣ → ∣ A ∣
```

<!--
```agda
  to-equiv : is-equiv to
  to-equiv .is-eqv y .centre = from y , B .is-tr _ _
  to-equiv .is-eqv y .paths x =
    Σ-prop-path (λ _ → is-prop→is-set (B .is-tr) _ _)
      (A .is-tr _ _)
module Bi = _↔_
open Bi
```
-->

A direct and fairly straightforward computation establishes that
biimplications are indeed an identity system on the type $\Omega$. This
includes, as usual, an appeal to univalence.

```agda
Ω-univalence : ∀ {ℓ} → is-identity-system {A = Ω ℓ} _↔_ λ a → bi (λ x → x) (λ x → x)
Ω-univalence .to-path biimp i .∣_∣ = ua (_ , Bi.to-equiv biimp) i
Ω-univalence .to-path {a} {b} biimp i .is-tr =
  is-prop→pathp (λ i → is-hlevel-is-prop {A = ua (_ , Bi.to-equiv biimp) i} 1)
    (a .is-tr)
    (b .is-tr) i
Ω-univalence .to-path-over p i .to x =
  outS (ua-glue (p .to , Bi.to-equiv p) i (λ _ → x) (inS (p .to x)))
Ω-univalence .to-path-over {a} p i .from x = hcomp (∂ i) λ where
  j (j = i0) → p .from (ua-unglue (p .to , Bi.to-equiv p) i x)
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
```

Another application of univalence comes in proving that the type
$\Omega$ indeed does classify subobjects: so, under the assumption that
$\Omega$ exists, we can safely put the type of all subobjects of a fixed
type $B$ in the same universe as $B$.

```agda
Ω-subobjects : ∀ {ℓ} {B : Type ℓ} → (Σ (Type ℓ) (_↪ B)) ≃ (B → Ω ℓ)
Ω-subobjects {B = B} = Iso→Equiv im where
  open is-iso
  im : Iso (Σ (Type _) (_↪ B)) (B → Ω _)
  im .fst (A , f) x = el (fibre (f .fst) x) (f .snd x)
  im .snd .inv P = (Σ B λ x → ∣ P x ∣) , fst , Subset-proj-embedding (λ x → is-tr (P x))
  im .snd .rinv P = funext λ x → Ω-ua $ bi
    (λ x → subst (λ e → ∣ P e ∣) (x .snd) (x .fst .snd))
    (λ w → (x , w) , refl)
  im .snd .linv (B , f , e) = Σ-pathp
    (ua (Total-equiv f e⁻¹))
      (Σ-prop-pathp (λ i x → Π-is-hlevel 1 λ _ → is-hlevel-is-prop 1)
      (ua→ λ { (x , y , p) → sym p }))
```
