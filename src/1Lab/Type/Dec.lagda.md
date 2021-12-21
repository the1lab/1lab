```agda
open import 1Lab.Path
open import 1Lab.Type

module 1Lab.Type.Dec where
```

# Decidable types

A type is decidable if it's computable whether or not that type is
inhabited.

```agda
data Dec {ℓ} (A : Type ℓ) : Type ℓ where
  yes : A → Dec A
  no : (A → ⊥) → Dec A

case : ∀ {ℓ ℓ'} {A : Type ℓ} (P : Dec A → Type ℓ')
     → ((y : A) → P (yes y))
     → ((y : (A → ⊥)) → P (no y))
     → (x : Dec A) → P x
case P f g (yes x) = f x
case P f g (no x) = g x
```

A type is _discrete_ if it has decidable equality.

```agda
Discrete : ∀ {ℓ} → Type ℓ → Type ℓ
Discrete A = (x y : A) → Dec (x ≡ y)
```


