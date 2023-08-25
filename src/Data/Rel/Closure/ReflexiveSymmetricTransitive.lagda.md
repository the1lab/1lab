<!--
```agda
open import 1Lab.Prelude
open import Data.Sum

open import Data.Rel.Base
open import Data.Rel.Closure.Base
open import Data.Rel.Closure.Reflexive
open import Data.Rel.Closure.Symmetric
open import Data.Rel.Closure.Transitive
open import Data.Rel.Closure.ReflexiveTransitive

```
-->

```agda
module Data.Rel.Closure.ReflexiveSymmetricTransitive where
```

<!--
```agda
private variable
  ℓ ℓ' ℓ'' : Level
  A B X : Type ℓ
  R R' S : A → A → Type ℓ
```
-->

# Reflexive-Symmetric-Transitive Closure

Finally, the reflexive-symmetric-transitive closure of a relation $R$ is
the smallest reflexive, symmetric, and transitive relation
$R^{\leftrightarrow*}$ that contains $R$.

```agda
data Refl-sym-trans {A : Type ℓ} (R : A → A → Type ℓ') (x : A) : A → Type (ℓ ⊔ ℓ') where
  [_] : ∀ {y} → R x y → Refl-sym-trans R x y
  reflexive : Refl-sym-trans R x x
  symmetric : ∀ {y} → Refl-sym-trans R y x → Refl-sym-trans R x y
  transitive : ∀ {y z} → Refl-sym-trans R x y → Refl-sym-trans R y z → Refl-sym-trans R x z
  trunc : ∀ {y} → is-prop (Refl-sym-trans R x y)
```

<!--
```agda
instance
  Refl-sym-trans-H-Level : ∀ {x y} {n} → H-Level (Refl-sym-trans R x y) (suc n)
  Refl-sym-trans-H-Level = prop-instance trunc

Refl-sym-trans-elim
  : (P : ∀ (x y : A) → Refl-sym-trans R x y → Type ℓ'')
  → (∀ {x y} → (r : R x y) → P x y [ r ])
  → (∀ {x} → P x x reflexive)
  → (∀ {x y} → (r+ : Refl-sym-trans R x y)
     → P x y r+ → P y x (symmetric r+))
  → (∀ {x y z} → (r+ : Refl-sym-trans R x y) → (s+ : Refl-sym-trans R y z)
     → P x y r+ → P y z s+
     → P x z (transitive r+ s+))
  → (∀ {x y} → (r+ : Refl-sym-trans R x y) → is-prop (P x y r+))
  → ∀ {x y} → (r+ : Refl-sym-trans R x y) → P x y r+
Refl-sym-trans-elim {R = R} P prel prefl psym ptrans pprop r+ = go r+ where
  go : ∀ {x y} → (r+ : Refl-sym-trans R x y) → P x y r+
  go [ r ] = prel r
  go reflexive = prefl
  go (symmetric r) = psym r (go r)
  go (transitive r+ s+) = ptrans r+ s+ (go r+) (go s+)
  go (trunc r+ r+' i) =
    is-prop→pathp (λ i → pprop (trunc r+ r+' i)) (go r+) (go r+') i
```
-->

Yet again, the recursion principle for the reflexive, symmetric,
transitive closure witnesses it's universal property; it is the smallest
reflexive, symmetric, transitive relation containing $R$.

```agda
Refl-sym-trans-rec
  : (S : A → A → Type ℓ)
  → (∀ {x y} → (r : R x y) → S x y)
  → (∀ {x} → S x x)
  → (∀ {x y} → S x y → S y x)
  → (∀ {x y z} → S x y → S y z → S x z)
  → (∀ {x y} → is-prop (S x y))
  → ∀ {x y} → Refl-sym-trans R x y → S x y
Refl-sym-trans-rec {R = R} S prel prefl psym ptrans pprop r+ = go r+ where
  go : ∀ {x y} → Refl-sym-trans R x y → S x y
  go [ r ] = prel r
  go reflexive = prefl
  go (symmetric r) = psym (go r)
  go (transitive r+ s+) = ptrans (go r+) (go s+)
  go (trunc r+ r+' i) = pprop (go r+) (go r+') i
```

We also define an alternative recursion principle for inducting down
the length of the chain of relations.

```agda
Refl-sym-trans-rec-chain
  : (S : A → A → Type ℓ)
  → (∀ {x} → S x x)
  → (∀ {x y z} → R x y → Refl-sym-trans R y z → S y z → S x z)
  → (∀ {x y z} → R y x → Refl-sym-trans R y z → S y z → S x z)
  → (∀ {x y} → is-prop (S x y))
  → ∀ {x y} → Refl-sym-trans R x y → S x y
Refl-sym-trans-rec-chain {R = R} S pnil pstep pinv pprop r+ = go r+ reflexive pnil where
  go : ∀ {x y z} → Refl-sym-trans R x y → Refl-sym-trans R y z → S y z → S x z
  go-sym : ∀ {x y z} → Refl-sym-trans R y x → Refl-sym-trans R y z → S y z → S x z

  go [ x→y ] y→*z acc = pstep x→y y→*z acc
  go reflexive y→*z acc = acc
  go (symmetric y→*x) y→*z acc = go-sym y→*x y→*z acc
  go (transitive x→*x' x'→*y) y→*z acc =
    go x→*x' (transitive x'→*y y→*z) (go x'→*y y→*z acc)
  go (trunc x→*y x→*y' i) y→*z acc =
    pprop (go x→*y y→*z acc) (go x→*y' y→*z acc) i

  go-sym [ y→x ] y→*z acc = pinv y→x y→*z acc
  go-sym reflexive y→*z acc = acc
  go-sym (symmetric x→*y) y→*z acc = go x→*y y→*z acc
  go-sym (transitive y→*y' y'→*x) y→*z acc =
    go-sym y'→*x (transitive (symmetric y→*y') y→*z) (go-sym y→*y' y→*z acc)
  go-sym (trunc y→*x y→*x' i) y→*z acc =
    pprop (go-sym y→*x y→*z acc) (go-sym y→*x' y→*z acc) i
```

## As a closure operator

```agda
refl-sym-trans-clo-mono : R ⊆r S → Refl-sym-trans R ⊆r Refl-sym-trans S
refl-sym-trans-clo-mono {S = S} p =
  Refl-sym-trans-rec (Refl-sym-trans S)
      (λ r → [ p r ])
      reflexive
      symmetric
      transitive
      trunc

refl-sym-trans-clo-closed : Refl-sym-trans (Refl-sym-trans R) ⊆r Refl-sym-trans R
refl-sym-trans-clo-closed {R = R} =
  Refl-sym-trans-rec (Refl-sym-trans R)
    id
    reflexive
    symmetric
    transitive
    trunc

refl-sym-trans-closure : is-rel-closure Refl-sym-trans
refl-sym-trans-closure .is-rel-closure.monotone = refl-sym-trans-clo-mono
refl-sym-trans-closure .is-rel-closure.extensive = [_]
refl-sym-trans-closure .is-rel-closure.closed = refl-sym-trans-clo-closed
refl-sym-trans-closure .is-rel-closure.has-prop = trunc
```

## Properties

The reflexive-transitive closure embeds into the reflexive symmetric
transitive closure.

```agda
refl-trans⊆refl-sym-trans
  : Refl-trans R ⊆r Refl-sym-trans R
refl-trans⊆refl-sym-trans =
  Refl-trans-rec (Refl-sym-trans _) [_] reflexive transitive trunc
```
