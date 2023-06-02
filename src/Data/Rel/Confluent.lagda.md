<!--
```agda
open import 1Lab.Prelude

open import Data.Rel.Closure
```
-->

```agda
module Data.Rel.Confluent where
```

# Confluence

<!--
```agda
private variable
  ℓ ℓ' ℓ'' : Level
  A B X : Type ℓ
  R : A → A → Type ℓ
```
-->

```agda
has-church-rosser : (A → A → Type ℓ) → Type _
has-church-rosser {A = A} R =
  ∀ {x y} → Refl-sym-trans R x y
  → ∃[ z ∈ A ] (Refl-trans R x z × Refl-trans R y z)

is-confluent : (A → A → Type ℓ) → Type _
is-confluent {A = A} R =
  ∀ {a x y} → Refl-trans R a x → Refl-trans R a y
  → ∃[ z ∈ A ] (Refl-trans R x z × Refl-trans R y z)

is-semi-confluent : (A → A → Type ℓ) → Type _
is-semi-confluent {A = A} R =
  ∀ {a x y} → Refl-trans R a x → R a y
  → ∃[ z ∈ A ] (Refl-trans R x z × Refl-trans R y z)

church-rosser→confluent : has-church-rosser R → is-confluent R
church-rosser→confluent church-rosser r+ s+ =
  church-rosser $
    transitive
      (symmetric (refl-trans→refl-sym-trans r+))
      (refl-trans→refl-sym-trans s+)

semiconfluent→church-rosser : is-semi-confluent R → has-church-rosser R
semiconfluent→church-rosser {R = R} semiconf r+ =
  Refl-sym-trans-rec-length
    (λ x y →  ∃[ z ∈ _ ] (Refl-trans R x z × Refl-trans R y z))
    (inc (_ , reflexive , reflexive))
    (λ x~y r+ → do
      z' , y~z' , z~z' ← r+
      z'' , z'~z'' , y~z'' ← semiconf (transitive [ x~y ] y~z') x~y
      pure (z'' , transitive [ x~y ] y~z'' , transitive z~z' z'~z''))
    (λ y~x r+ → do
      z' , y~z' , z~z' ← r+
      z'' , z'~z'' , x~z'' ← semiconf y~z' y~x
      pure (z'' , x~z'' , transitive z~z' z'~z''))
    squash
    r+

confluent→semiconfluent : is-confluent R → is-semi-confluent R
confluent→semiconfluent conf r+ s = conf r+ [ s ]

semiconfluent→confluent : is-semi-confluent R → is-confluent R
semiconfluent→confluent conf =
  church-rosser→confluent (semiconfluent→church-rosser conf)

confluent→church-rosser : is-confluent R → has-church-rosser R
confluent→church-rosser conf =
  semiconfluent→church-rosser (confluent→semiconfluent conf)

church-rosser→semiconfluent : has-church-rosser R → is-semi-confluent R
church-rosser→semiconfluent church-rosser =
  confluent→semiconfluent (church-rosser→confluent church-rosser)
```
