---
description: |
  Monoids are, next to semigroups, the simplest algebraic structure with
  axioms. The definition of monoids is illustrative in application of
  the Structure Identity Principle.
---

```agda
open import 1Lab.Univalence.SIP
open import 1Lab.Path.Groupoid
open import 1Lab.Univalence
open import 1Lab.Data.Nat
open import 1Lab.HLevel
open import 1Lab.Equiv
open import 1Lab.Path
open import 1Lab.Type

open import Agda.Builtin.Sigma renaming (Σ to Sigma)

module Algebra.Monoid where
```

<!--
```
private variable
  ℓ : Level
  A : Type ℓ
```
-->

# Monoids

A **monoid** is a [set] equipped with an associative, unital binary
operation. In type theory, this structure is generally represented as a
[record] containing both the operation and the unit, together with
witnesses for all of the axioms. This encoding is certainly functional,
but in univalent mathematics, a more indirect description is
preferrable:

[record]: https://agda.readthedocs.io/en/v2.6.2/language/record-types.html
[set]: agda://1Lab.HLevel#Set

We can characterise what makes a type a monoid as a [standard notion of
structure] that is [equipped with axioms]. The structure
underlying a monoid has a scary name, but it's quite simple in reality:
**Pointed $\infty$-magmas**

[equipped with axioms]: agda://1Lab.Univalence.SIP#add-axioms
[standard notion of structure]: agda://1Lab.Univalence.SIP#SNS

```agda
Pointed∞Magma : Type ℓ → Type ℓ
Pointed∞Magma X = (X → X → X) × X
```

A **pointed $\infty$-magma structure** on a type `X` is given by a
function of type `X → X → X` and an inhabitant of `X`, subject to no
other conditions. This is why it gets prefixed with $\infty$: it's not
subject to any truncation conditions, so it can be an arbitrary
$\infty$-groupoid.

```agda
Pointed∞Magma-SNS : ∀ {ℓ} → SNS (Pointed∞Magma {ℓ})
Pointed∞Magma-SNS = sns where
  str : Structure Pointed∞Magma
  str .is-hom (X , _·_ , x) (Y , _*_ , y) (f , _) =
        (Path (X → X → Y) (λ x y → f (x · y)) (λ x y → f x * f y))
      × (Path Y (f x) y)
  str .is-hom-id .fst = refl
  str .is-hom-id .snd = refl
```

A **pointed $\infty$-magma homomorphism** is an equivalence of the
underlying types that commutes with the operation, and preserves the
identity element.

```agda
  sns : SNS _
  sns .fst = str
  sns .snd = equiv where
    sp→se~id : ∀ {X} {s t : Pointed∞Magma X} (p : _)
             → structure-path→structure-equiv str {s = s} {t = t} p
             ≡ (ap fst p , ap snd p)
    sp→se~id {X} {s} =
      J (λ y p → structure-path→structure-equiv str {s = s} {t = y} p
               ≡ (ap fst p , ap snd p))
        (transport-refl _)
```

We show that this is a `sns`{.Agda} by relating the canonical map with
something we know to be an equivalence: Specifically, it's [homotopic]
to the underlying map of the isomorphism that [characterises paths in Σ
types].

[homotopic]: agda://1Lab.Path#funext
[characterises paths in Σ types]: agda://1Lab.Path.Groupoid#Σ-PathP-iso

```agda
    simpler : isEquiv (λ x → ap fst x , ap snd x)
    simpler = isIso→isEquiv (isIso.inverse (Σ-PathP-iso .snd))
    
    equiv : isEquiv _
    equiv = subst isEquiv (sym (funext sp→se~id)) simpler
```

We define the monoid axioms in a record, for convenience of naming:

```agda
record isMonoid {ℓ} {X : Type ℓ} (P : Pointed∞Magma X) : Type ℓ where
  open Sigma P renaming (fst to infixr 30 _·_ ; snd to unit) public

  field
    monoid-set : isSet X
```

First, the underlying type **must** be a Set. This ensures that the rest
of the axioms are [propositions].

[propositions]: agda://1Lab.HLevel#isProp

Then, we need the actual monoid axioms:

```agda
    monoid-idʳ : ∀ {x} → x · unit ≡ x
    monoid-idˡ : ∀ {x} → unit · x ≡ x
    monoid-assoc : ∀ {x y z} → (x · y) · z ≡ x · y · z

open isMonoid hiding (_·_ ; unit)
```

The condition that `monoids are sets`{.Agda} ensure that the latter
three equations are propositions. This characterises
`isMonoid`{.Agda} as [axioms we can add to a SNS].

[axioms we can add to a SNS]: agda://1Lab.Univalence.SIP#add-axioms

```agda
isProp-isMonoid : {P : Pointed∞Magma A} → isProp (isMonoid P)
isProp-isMonoid {P = P} m n i .monoid-set =
  isProp-isHLevel 2 (m .monoid-set) (n .monoid-set) i
```

Since `having a given h-level is a proposition`{.Agda
ident=isProp-isHLevel}, we can construct the path relating the witnesses
`monoid-set`{.Agda}. The rest of the squares have fillers _precisely_
because `A` is assumed to be a set:

```agda
isProp-isMonoid {P = P} m n i .monoid-idʳ {e} =
  m .monoid-set _ _ (m .monoid-idʳ {e}) (n .monoid-idʳ {e}) i
isProp-isMonoid {P = P} m n i .monoid-idˡ {e} = 
  m .monoid-set _ _ (m .monoid-idˡ {e}) (n .monoid-idˡ {e}) i
isProp-isMonoid {P = P} m n i .monoid-assoc {e} {f} {g} =
  m .monoid-set _ _ (m .monoid-assoc {e} {f} {g}) (n .monoid-assoc {e} {f} {g}) i
```

We can then characterise `monoid structures`{.Agda ident=MonoidStr} and
that they are `standard`{.Agda ident=Monoid-SNS}.

```agda
MonoidStr : Type ℓ → Type ℓ
MonoidStr X = Σ[ P ∈ Pointed∞Magma X ] (isMonoid P)

Monoid-SNS : ∀ {ℓ} → SNS (MonoidStr {ℓ})
Monoid-SNS = add-axioms Pointed∞Magma-SNS (λ _ → isMonoid) isProp-isMonoid
```

A `Monoid`{.Agda} is a type equipped with a monoid structure. By the
[structure identity principle], a path between monoids is the same thing
as an equivalence of the underlying types that preserves the monoid structure:

[structure identity principle]: agda://1Lab.Univalence.SIP

```agda
Monoid : (ℓ : _) → Type (lsuc ℓ)
Monoid _ = Σ MonoidStr

MonoidPath : ∀ {ℓ} {A B : Monoid ℓ} → (A ≡ B) ≃ (A ≃[ Monoid-SNS ] B)
MonoidPath = SIP Monoid-SNS
```

---

# Concrete monoids

## Lists

The most obvious example of a monoid is the **free monoid on a set of
generators** - better known as `the type of lists`{.Agda} on a set. We
require that the type be a set since _monoids_ have to be sets, and
`lists preserve set-ness`{.Agda isSet→List-isSet}.

```agda
open import 1Lab.Data.List

List-monoid : ∀ {ℓ} {A : Type ℓ} → isSet A → MonoidStr (List A)
List-monoid isS .fst .fst = _++_
List-monoid isS .fst .snd = nil
```

The underlying pointed $\infty$-monoid structure is given by
`_++_`{.Agda} and `nil`{.Agda}.

```agda
List-monoid isS .snd .monoid-set = isSet→List-isSet isS
List-monoid isS .snd .monoid-idʳ = ++-idʳ _
List-monoid isS .snd .monoid-idˡ = ++-idˡ _
List-monoid isS .snd .monoid-assoc {f} {g} {h} = ++-assoc f g h
```

The [list module](agda://1Lab.Data.List) has the proofs of the required
equalities to make this into a monoid.

## Monoid structures on ℕ

Since `Nat`{.Agda} is a set, we can prove it has a multitude of `monoid
structures`{.Agda ident=MonoidStr}:

```agda
ℕ-+ : MonoidStr Nat
ℕ-+ .fst .fst = _+_
ℕ-+ .fst .snd = 0
ℕ-+ .snd .isMonoid.monoid-set = isSet-Nat
ℕ-+ .snd .isMonoid.monoid-idʳ {x} = +-zeroʳ x
ℕ-+ .snd .isMonoid.monoid-idˡ {x} = refl
ℕ-+ .snd .isMonoid.monoid-assoc {x} {y} {z} = +-associative x y z

ℕ-* : MonoidStr Nat
ℕ-* .fst .fst = _*_
ℕ-* .fst .snd = 1
ℕ-* .snd .monoid-set = isSet-Nat
ℕ-* .snd .monoid-idʳ {x} = *-oneʳ x
ℕ-* .snd .monoid-idˡ {x} = +-zeroʳ x
ℕ-* .snd .monoid-assoc {x} {y} {z} = *-associative x y z
```

## Friendly Interface

Since the way `Monoid`{.Agda} is associated is very inconvenient, the
following module can be used to bring the monoid data into scope using
more friendly names.

```agda
module Monoid {ℓ} (monoid : Monoid ℓ) where
  private
    module M = isMonoid (monoid .snd .snd)

  M : Type ℓ

  _⋆_ : M → M → M
  unit : M

  ⋆-assoc-l→r : {x y z : M} → (x ⋆ y) ⋆ z ≡ x ⋆ y ⋆ z
  ⋆-assoc-r→l : {x y z : M} → x ⋆ y ⋆ z ≡ (x ⋆ y) ⋆ z
  ⋆-unitˡ : {z : M} → unit ⋆ z ≡ z
  ⋆-unitʳ : {z : M} → z ⋆ unit ≡ z
```

<!--
```
  M = monoid .fst

  -- Structure
  x ⋆ y = x M.· y
  unit = M.unit

  infixr 30 _⋆_

  -- Properties
  ⋆-assoc-l→r = M.monoid-assoc
  ⋆-assoc-r→l = sym M.monoid-assoc
  ⋆-unitˡ = M.monoid-idˡ
  ⋆-unitʳ = M.monoid-idʳ
```
-->

## Properties

If we have $x \star y = y \star x$ for every $x, y$, then the monoid is
said to be _commutative_:

```
isCommutative : ∀ {ℓ} → Monoid ℓ → Type _
isCommutative mon = (x y : M) → x ⋆ y ≡ y ⋆ x
  where open Monoid mon
```