<!--
```agda
open import 1Lab.Prelude
open import Data.Sum

open import Data.Rel.Base
open import Data.Rel.Closure.Base
open import Data.Rel.Closure.Reflexive
open import Data.Rel.Closure.Transitive

```
-->

```agda
module Data.Rel.Closure.ReflexiveTransitive where
```

<!--
```agda
private variable
  ℓ ℓ' ℓ'' : Level
  A B X : Type ℓ
  R R' S : A → A → Type ℓ
```
-->

# Reflexive-Transitive Closure

The reflexive-transitive [closure] of a [relation] $R$ is the smallest
reflexive and transitive relation $R^{*}$ that contains $R$.

[relation]: Data.Rel.Base.html
[closure]: Data.Rel.Closure.html

```agda
data Refl-trans {A : Type ℓ} (R : A → A → Type ℓ') (x : A) : A → Type (ℓ ⊔ ℓ') where
  [_] : ∀ {y} → R x y → Refl-trans R x y
  reflexive : Refl-trans R x x
  transitive : ∀ {y z} → Refl-trans R x y → Refl-trans R y z → Refl-trans R x z
  trunc : ∀ {y} → is-prop (Refl-trans R x y)
```

<!--
```agda
instance
  Refl-trans-H-Level : ∀ {x y} {n} → H-Level (Refl-trans R x y) (suc n)
  Refl-trans-H-Level = prop-instance trunc

Refl-trans-elim
  : (P : ∀ (x y : A) → Refl-trans R x y → Type ℓ'')
  → (∀ {x y} → (r : R x y) → P x y [ r ])
  → (∀ {x} → P x x reflexive)
  → (∀ {x y z} → (r+ : Refl-trans R x y) → (s+ : Refl-trans R y z)
     → P x y r+ → P y z s+
     → P x z (transitive r+ s+))
  → (∀ {x y} → (r+ : Refl-trans R x y) → is-prop (P x y r+))
  → ∀ {x y} → (r+ : Refl-trans R x y) → P x y r+
Refl-trans-elim {R = R} P prel prefl ptrans pprop r+ = go r+ where
  go : ∀ {x y} → (r+ : Refl-trans R x y) → P x y r+
  go [ r ] = prel r
  go reflexive = prefl
  go (transitive r+ s+) = ptrans r+ s+ (go r+) (go s+)
  go (trunc r+ r+' i) =
    is-prop→pathp (λ i → pprop (trunc r+ r+' i)) (go r+) (go r+') i
```
-->

Following the general theme, the recursion principle for the reflexive
transitive closure witnesses it's universal property; it is the smallest
reflexive and transitive relation containing $R$.

```agda
Refl-trans-rec
  : (S : A → A → Type ℓ)
  → (∀ {x y} → (r : R x y) → S x y)
  → (∀ {x} → S x x)
  → (∀ {x y z} → S x y → S y z → S x z)
  → (∀ {x y} → is-prop (S x y))
  → ∀ {x y} → Refl-trans R x y → S x y
Refl-trans-rec {R = R} S prel prefl ptrans pprop r+ = go r+ where
  go : ∀ {x y} → Refl-trans R x y → S x y
  go [ r ] = prel r
  go reflexive = prefl
  go (transitive r+ s+) = ptrans (go r+) (go s+)
  go (trunc r+ r+' i) = pprop (go r+) (go r+') i
```

We also provide a recursion principle that inducts down the length of the
chain of relations.

```agda
Refl-trans-rec-chain
  : (S : A → A → Type ℓ)
  → (∀ {x} → S x x)
  → (∀ {x y z} → R x y → Refl-trans R y z → S y z → S x z)
  → (∀ {x y} → is-prop (S x y))
  → ∀ {x y} → Refl-trans R x y → S x y
Refl-trans-rec-chain {R = R} S pnil pstep pprop r+ = go r+ reflexive pnil where
  go : ∀ {x y z} → Refl-trans R x y → Refl-trans R y z → S y z → S x z
  go [ x→y ] y→*z acc = pstep x→y y→*z acc
  go reflexive y→*z acc = acc
  go (transitive x→*x' x'→*y) y→*z acc =
    go x→*x' (transitive x'→*y y→*z) (go x'→*y y→*z acc)
  go (trunc x→*y x→*y' i) y→*z acc =
    pprop (go x→*y y→*z acc) (go x→*y' y→*z acc) i
```

We also provide an eliminator for inspecting forks.

```agda
Refl-trans-case-fork
  : (S : A → A → A → Type ℓ)
  → (∀ {a y} → Refl-trans R' a y → S a a y)
  → (∀ {a x} → Refl-trans R a x → S a x a)
  → (∀ {a x y x' y'}
     → R a x' → Refl-trans R x' x
     → R' a y' → Refl-trans R' y' y
     → S a x y)
  → (∀ {a x y} → is-prop (S a x y))
  → ∀ {a x y} → Refl-trans R a x → Refl-trans R' a y → S a x y
Refl-trans-case-fork {R' = R'} {R = R} S refll reflr fork prop {a} {x} {y} a→*x a→*y =
  Refl-trans-rec-chain (λ a x → Refl-trans R' a y → S a x y)
    refll
    (λ {a} {a'} {x} a→a' a'→*x _ a→*y →
      Refl-trans-rec-chain
        (λ a y → R a a' → Refl-trans R a' x → S a x y)
        (λ a→a' a'→*x → reflr (transitive [ a→a' ] a'→*x))
        (λ a→a' a'→*y _ a→a'' a''→*x → fork a→a'' a''→*x a→a' a'→*y)
        (Π-is-hlevel 1 (λ _ → Π-is-hlevel 1 λ _ → prop))
        a→*y a→a' a'→*x)
    (Π-is-hlevel 1 (λ _ → prop))
    a→*x a→*y
```

If the underlying relation is symmetric, then so is the
reflexive-transitive closure.

```agda
refl-trans-clo-symmetric : is-symmetric R → is-symmetric (Refl-trans R)
refl-trans-clo-symmetric {R = R} is-sym r+ =
  Refl-trans-rec (λ x y → Refl-trans R y x)
    (λ r → [ is-sym r ])
    reflexive
    (λ r+ s+ → transitive s+ r+)
    trunc
    r+
```

The reflexive closure and the transitive closure are contained in
the reflexive transitive closure.

```agda
refl-clo⊆refl-trans-clo : Refl R ⊆r Refl-trans R
refl-clo⊆refl-trans-clo {R = R} =
  Refl-rec (Refl-trans R) [_] (λ _ → reflexive) hlevel!

trans-clo⊆refl-trans-clo : Trans R ⊆r Refl-trans R
trans-clo⊆refl-trans-clo {R = R} =
  Trans-rec (Refl-trans R) [_] transitive hlevel!
```


Note that the reflexive-transitive closure is equivalent to taking
the reflexive closure of the transitive closure.

```agda
refl-clo-trans-clo⊆refl-trans-clo : Refl (Trans R) ⊆r Refl-trans R
refl-clo-trans-clo⊆refl-trans-clo {R = R} =
  Refl-rec (Refl-trans R)
    trans-clo⊆refl-trans-clo
    (λ _ → reflexive)
    hlevel!

refl-trans-clo⊆refl-clo-trans-clo : Refl-trans R ⊆r Refl (Trans R)
refl-trans-clo⊆refl-clo-trans-clo {R = R} =
  Refl-trans-rec (Refl (Trans R))
    (λ x~y → [ [ x~y ] ])
    reflexive
    (refl-clo-transitive transitive)
    hlevel!

refl-clo-trans-clo≡refl-trans-clo : Refl (Trans R) ≡ Refl-trans R
refl-clo-trans-clo≡refl-trans-clo {R = R} =
  prop-rel-ext trunc trunc
    refl-clo-trans-clo⊆refl-trans-clo
    refl-trans-clo⊆refl-clo-trans-clo
```

The same can be said for the transitive closure of the reflexive closure.

```agda
trans-clo-refl-clo⊆refl-trans-clo : Trans (Refl R) ⊆r Refl-trans R
trans-clo-refl-clo⊆refl-trans-clo {R = R} =
  Trans-rec (Refl-trans R)
    refl-clo⊆refl-trans-clo
    transitive
    hlevel!

refl-trans-clo⊆trans-clo-refl-clo : Refl-trans R ⊆r Trans (Refl R)
refl-trans-clo⊆trans-clo-refl-clo {R = R} =
  Refl-trans-rec (Trans (Refl R))
    (λ x~y → [ [ x~y ] ])
    [ reflexive ]
    transitive
    hlevel!

trans-clo-refl-clo≡refl-trans-clo : Trans (Refl R) ≡ Refl-trans R
trans-clo-refl-clo≡refl-trans-clo {R = R} =
  prop-rel-ext trunc trunc
    trans-clo-refl-clo⊆refl-trans-clo
    refl-trans-clo⊆trans-clo-refl-clo
```
