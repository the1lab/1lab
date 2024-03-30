<!--
```agda
open import Meta.Brackets

open import Data.Dec
open import Data.Fin

open import Cat.Prelude

import Data.Nat as Nat
```
-->

```agda
module Cat.Instances.Simplex where
```

<!--
```agda
open Precategory
```
-->

# The simplex category

<!--
```agda
private variable
  l m n o l' m' n' o' : Nat
```
-->

```agda
data Δ-Hom⁺ : Nat → Nat → Type where
  done⁺ : Δ-Hom⁺ 0 0
  shift⁺ : ∀ {m n} → Δ-Hom⁺ m n → Δ-Hom⁺ m (suc n)
  keep⁺ : ∀ {m n} → Δ-Hom⁺ m n → Δ-Hom⁺ (suc m) (suc n)

data Δ-Hom⁻ : Nat → Nat → Type where
  done⁻ : Δ-Hom⁻ 0 0
  crush⁻ : ∀ {m n} → Δ-Hom⁻ m (suc n) → Δ-Hom⁻ (suc m) (suc n)
  keep⁻ : ∀ {m n} → Δ-Hom⁻ m n → Δ-Hom⁻ (suc m) (suc n)
```

```agda
id⁺ : ∀ {m} → Δ-Hom⁺ m m
id⁺ {zero} = done⁺
id⁺ {suc m} = keep⁺ id⁺

id⁻ : ∀ {m} → Δ-Hom⁻ m m
id⁻ {zero} = done⁻
id⁻ {suc m} = keep⁻ id⁻

_∘⁻_ : Δ-Hom⁻ n o → Δ-Hom⁻ m n → Δ-Hom⁻ m o
done⁻ ∘⁻ g = g
crush⁻ f ∘⁻ crush⁻ g = crush⁻ (crush⁻ f ∘⁻ g)
crush⁻ f ∘⁻ keep⁻ g = crush⁻ (f ∘⁻ g)
keep⁻ f ∘⁻ crush⁻ g = crush⁻ (keep⁻ f ∘⁻ g)
keep⁻ f ∘⁻ keep⁻ g = keep⁻ (f ∘⁻ g)

_∘⁺_ : Δ-Hom⁺ n o → Δ-Hom⁺ m n → Δ-Hom⁺ m o
f ∘⁺ done⁺ = f
shift⁺ f ∘⁺ shift⁺ g = shift⁺ (f ∘⁺ shift⁺ g)
keep⁺ f ∘⁺ shift⁺ g = shift⁺ (f ∘⁺ g)
shift⁺ f ∘⁺ keep⁺ g = shift⁺ (f ∘⁺ keep⁺ g)
keep⁺ f ∘⁺ keep⁺ g = keep⁺ (f ∘⁺ g)

¡⁺ : Δ-Hom⁺ 0 m
¡⁺ {m = zero} = done⁺
¡⁺ {m = suc m} = shift⁺ ¡⁺

cast⁺ : m ≡ m' → n ≡ n' → Δ-Hom⁺ m n → Δ-Hom⁺ m' n'
cast⁺ {zero} {zero} {zero} {zero} p q done⁺ = done⁺
cast⁺ {zero} {zero} {zero} {suc n'} p q f = absurd (Nat.zero≠suc q)
cast⁺ {zero} {zero} {suc n} {zero} p q f = absurd (Nat.suc≠zero q)
cast⁺ {zero} {zero} {suc n} {suc n'} p q (shift⁺ f) = shift⁺ (cast⁺ p (Nat.suc-inj q) f)
cast⁺ {zero} {suc m'} {n} {n'} p q f = absurd (Nat.zero≠suc p)
cast⁺ {suc m} {zero} {n} {n'} p q f = absurd (Nat.suc≠zero p)
cast⁺ {suc m} {suc m'} {suc n} {zero} p q f = absurd (Nat.suc≠zero q)
cast⁺ {suc m} {suc m'} {suc n} {suc n'} p q (shift⁺ f) = shift⁺ (cast⁺ p (Nat.suc-inj q) f)
cast⁺ {suc m} {suc m'} {suc n} {suc n'} p q (keep⁺ f) = keep⁺ (cast⁺ (Nat.suc-inj p) (Nat.suc-inj q) f)

!⁻ : Δ-Hom⁻ (suc m) 1
!⁻ {m = zero} = id⁻
!⁻ {m = suc m} = crush⁻ !⁻

δ⁺ : Fin (suc n) → Δ-Hom⁺ n (suc n)
δ⁺ {n = _} fzero = shift⁺ id⁺
δ⁺ {n = suc _} (fsuc i) = keep⁺ (δ⁺ i)

σ⁻ : Fin n → Δ-Hom⁻ (suc n) n
σ⁻ fzero = crush⁻ id⁻
σ⁻ (fsuc i) = keep⁻ (σ⁻ i)
```

```agda
shift⁺-inj
  : ∀ {f g : Δ-Hom⁺ m n}
  → shift⁺ f ≡ shift⁺ g
  → f ≡ g
shift⁺-inj {m} {n} {f} {g} = ap unshift where
  unshift : Δ-Hom⁺ m (suc n) → Δ-Hom⁺ m n
  unshift (shift⁺ h) = h
  unshift (keep⁺ h) = f

keep⁺-inj
  : ∀ {f g : Δ-Hom⁺ m n}
  → keep⁺ f ≡ keep⁺ g
  → f ≡ g
keep⁺-inj {m} {n} {f} {g} = ap unkeep where
  unkeep : Δ-Hom⁺ (suc m) (suc n) → Δ-Hom⁺ m n
  unkeep (keep⁺ h) = h
  unkeep (shift⁺ h) = f

is-shift⁺ : Δ-Hom⁺ m n → Type
is-shift⁺ done⁺ = ⊥
is-shift⁺ (shift⁺ _) = ⊤
is-shift⁺ (keep⁺ _) = ⊥

is-keep⁺ : Δ-Hom⁺ m n → Type
is-keep⁺ done⁺ = ⊥
is-keep⁺ (shift⁺ _) = ⊥
is-keep⁺ (keep⁺ _) = ⊤

shift⁺≠keep⁺
  : ∀ {f : Δ-Hom⁺ (suc m) n} {g : Δ-Hom⁺ m n}
  → ¬ (shift⁺ f ≡ keep⁺ g)
shift⁺≠keep⁺ p = subst is-shift⁺ p tt

keep⁺≠shift⁺
  : ∀ {f : Δ-Hom⁺ m n} {g : Δ-Hom⁺ (suc m) n}
  → ¬ (keep⁺ f ≡ shift⁺ g)
keep⁺≠shift⁺ p = subst is-keep⁺ p tt

instance
  Discrete-Δ-Hom⁺ : Discrete (Δ-Hom⁺ m n)
  Discrete-Δ-Hom⁺ {x = done⁺} {y = done⁺} =
    yes refl
  Discrete-Δ-Hom⁺ {x = shift⁺ x} {y = shift⁺ y} =
    Dec-map (ap shift⁺) shift⁺-inj Discrete-Δ-Hom⁺
  Discrete-Δ-Hom⁺ {x = shift⁺ x} {y = keep⁺ y} =
    no shift⁺≠keep⁺
  Discrete-Δ-Hom⁺ {x = keep⁺ x} {y = shift⁺ y} =
    no keep⁺≠shift⁺
  Discrete-Δ-Hom⁺ {x = keep⁺ x} {y = keep⁺ y} =
    Dec-map (ap keep⁺) keep⁺-inj Discrete-Δ-Hom⁺

Δ-Hom⁺-is-set : is-set (Δ-Hom⁺ m n)
Δ-Hom⁺-is-set = Discrete→is-set Discrete-Δ-Hom⁺
```

# Semantics

```agda
Δ⁺-map : ∀ {m n} → Δ-Hom⁺ m n → Fin m → Fin n
Δ⁺-map (shift⁺ f) i = fsuc (Δ⁺-map f i)
Δ⁺-map (keep⁺ f) fzero = fzero
Δ⁺-map (keep⁺ f) (fsuc i) = fsuc (Δ⁺-map f i)

Δ⁻-map : ∀ {m n} → Δ-Hom⁻ m n → Fin m → Fin n
Δ⁻-map (crush⁻ f) fzero = fzero
Δ⁻-map (crush⁻ f) (fsuc i) = Δ⁻-map f i
Δ⁻-map (keep⁻ f) fzero = fzero
Δ⁻-map (keep⁻ f) (fsuc i) = fsuc (Δ⁻-map f i)
```

```agda
Δ⁺-map-inj
  : ∀ (f g : Δ-Hom⁺ m n)
  → (∀ i → Δ⁺-map f i ≡ Δ⁺-map g i)
  → f ≡ g
Δ⁺-map-inj done⁺ done⁺ p = refl
Δ⁺-map-inj (shift⁺ f) (shift⁺ g) p =
  ap shift⁺ (Δ⁺-map-inj f g (fsuc-inj ⊙ p))
Δ⁺-map-inj (shift⁺ f) (keep⁺ g) p =
  absurd (fzero≠fsuc (sym (p 0)))
Δ⁺-map-inj (keep⁺ f) (shift⁺ g) p =
  absurd (fzero≠fsuc (p 0))
Δ⁺-map-inj (keep⁺ f) (keep⁺ g) p =
  ap keep⁺ (Δ⁺-map-inj f g (fsuc-inj ⊙ p ⊙ fsuc))
```

```agda
Δ⁺-map-id : ∀ (i : Fin m) → Δ⁺-map id⁺ i ≡ i
Δ⁺-map-id fzero = refl
Δ⁺-map-id (fsuc i) = ap fsuc (Δ⁺-map-id i)

Δ⁺-map-∘
  : (f : Δ-Hom⁺ n o) (g : Δ-Hom⁺ m n)
  → ∀ (i : Fin m) → Δ⁺-map (f ∘⁺ g) i ≡ Δ⁺-map f (Δ⁺-map g i)
Δ⁺-map-∘ done⁺ done⁺ ()
Δ⁺-map-∘ (shift⁺ f) (shift⁺ g) i = ap fsuc (Δ⁺-map-∘ f (shift⁺ g) i)
Δ⁺-map-∘ (shift⁺ f) (keep⁺ g) i = ap fsuc (Δ⁺-map-∘ f (keep⁺ g) i)
Δ⁺-map-∘ (keep⁺ f) (shift⁺ g) i = ap fsuc (Δ⁺-map-∘ f g i)
Δ⁺-map-∘ (keep⁺ f) (keep⁺ g) fzero = refl
Δ⁺-map-∘ (keep⁺ f) (keep⁺ g) (fsuc i) = ap fsuc (Δ⁺-map-∘ f g i)
```

# Categories

```agda
idl⁺ : ∀ (f : Δ-Hom⁺ m n) → id⁺ ∘⁺ f ≡ f
idl⁺ f = Δ⁺-map-inj _ _ λ i →
  Δ⁺-map-∘ id⁺ f i ∙ Δ⁺-map-id (Δ⁺-map f i)

idr⁺ : ∀ (f : Δ-Hom⁺ m n) → f ∘⁺ id⁺ ≡ f
idr⁺ {m = zero} f = refl
idr⁺ {m = suc m} (shift⁺ f) = ap shift⁺ (idr⁺ f)
idr⁺ {m = suc m} (keep⁺ f) = ap keep⁺ (idr⁺ f)

assoc⁺
  : ∀ (f : Δ-Hom⁺ n o) (g : Δ-Hom⁺ m n) (h : Δ-Hom⁺ l m)
  → f ∘⁺ (g ∘⁺ h) ≡ (f ∘⁺ g) ∘⁺ h
assoc⁺ f g h = Δ⁺-map-inj _ _ λ i →
  Δ⁺-map-∘ f (g ∘⁺ h) i
  ∙ ap (Δ⁺-map f) (Δ⁺-map-∘ g h i)
  ∙ sym (Δ⁺-map-∘ f g (Δ⁺-map h i))
  ∙ sym (Δ⁺-map-∘ (f ∘⁺ g) h i)
```

```agda
record Δ-Hom (m n : Nat) : Type where
  no-eta-equality
  constructor Δ-hom
  field
    {middle} : Nat
    hom⁺ : Δ-Hom⁺ middle n
    hom⁻ : Δ-Hom⁻ m middle

open Δ-Hom

done : Δ-Hom 0 0
done .middle = 0
done .hom⁺ = done⁺
done .hom⁻ = done⁻

crush : Δ-Hom m (suc n) → Δ-Hom (suc m) (suc n)
crush f with f .middle | f .hom⁺ | f .hom⁻
... | zero  | f⁺ | done⁻ = Δ-hom (keep⁺ ¡⁺) id⁻
... | suc x | f⁺ | f⁻ = Δ-hom f⁺ (crush⁻ f⁻)

shift : Δ-Hom m n → Δ-Hom m (suc n)
shift f .middle = f .middle
shift f .hom⁺ = shift⁺ (f .hom⁺)
shift f .hom⁻ = f .hom⁻

keep : Δ-Hom m n → Δ-Hom (suc m) (suc n)
keep f .middle = suc (f .middle)
keep f .hom⁺ = keep⁺ (f .hom⁺)
keep f .hom⁻ = keep⁻ (f .hom⁻)
```

```agda
exchange
  : ∀ {m n o}
  → Δ-Hom⁻ n o → Δ-Hom⁺ m n
  → Δ-Hom m o
exchange done⁻ done⁺ = Δ-hom done⁺ done⁻
exchange (crush⁻ f) (shift⁺ g) = exchange f g
exchange (crush⁻ f) (keep⁺ g) = crush (exchange f g)
exchange (keep⁻ f) (shift⁺ g) = shift (exchange f g)
exchange (keep⁻ f) (keep⁺ g) = keep (exchange f g)
```

```agda
Δ⁺ : Precategory lzero lzero
Δ⁺ .Ob = Nat
Δ⁺ .Hom = Δ-Hom⁺
Δ⁺ .Hom-set _ _ = Δ-Hom⁺-is-set
Δ⁺ .id = id⁺
Δ⁺ ._∘_ = _∘⁺_
Δ⁺ .idr = idr⁺
Δ⁺ .idl = idl⁺
Δ⁺ .assoc = assoc⁺
```

-- ```agda
-- Δ⁺-map-pres-<
--   : ∀ {m n}
--   → (f : Δ-Hom⁺ m n)
--   → ∀ {i j} → i < j → Δ⁺-map f i < Δ⁺-map f j
-- Δ⁺-map-pres-< (shift⁺ f) {i} {j} i<j =
--   Nat.s≤s (Δ⁺-map-pres-< f i<j)
-- Δ⁺-map-pres-< (keep⁺ f) {fzero} {fsuc j} i<j =
--  Nat.s≤s Nat.0≤x
-- Δ⁺-map-pres-< (keep⁺ f) {fsuc i} {fsuc j} (Nat.s≤s i<j) =
--   Nat.s≤s (Δ⁺-map-pres-< f i<j)
-- ```

-- ```agda
-- Δ⁻-map-reflect-<
--   : ∀ {m n}
--   → (f : Δ-Hom⁻ m n)
--   → ∀ {i j} → Δ⁻-map f i < Δ⁻-map f j → i < j
-- Δ⁻-map-reflect-< (crush⁻ f) {fzero} {fsuc j} fi<fj =
--   Nat.s≤s Nat.0≤x
-- Δ⁻-map-reflect-< (crush⁻ f) {fsuc i} {fsuc j} fi<fj =
--   Nat.s≤s (Δ⁻-map-reflect-< f fi<fj)
-- Δ⁻-map-reflect-< (keep⁻ f) {fzero} {fsuc j} fi<fj =
--   Nat.s≤s Nat.0≤x
-- Δ⁻-map-reflect-< (keep⁻ f) {fsuc i} {fsuc j} (Nat.s≤s fi<fj) =
--   Nat.s≤s (Δ⁻-map-reflect-< f fi<fj)
-- ```

-- ```agda
-- Δ⁺-map-inj
--   : ∀ {m n}
--   → (f : Δ-Hom⁺ m n)
--   → ∀ {i j} → Δ⁺-map f i ≡ Δ⁺-map f j → i ≡ j
-- Δ⁺-map-inj (shift⁺ f) {i} {j} p = Δ⁺-map-inj f (fsuc-inj p)
-- Δ⁺-map-inj (keep⁺ f) {fzero} {fzero} p = refl
-- Δ⁺-map-inj (keep⁺ f) {fzero} {fsuc j} p = absurd (fzero≠fsuc p)
-- Δ⁺-map-inj (keep⁺ f) {fsuc i} {fzero} p = absurd (fzero≠fsuc (sym p))
-- Δ⁺-map-inj (keep⁺ f) {fsuc i} {fsuc j} p = ap fsuc (Δ⁺-map-inj f (fsuc-inj p))

-- Δ⁻-map-split-surj
--   : ∀ {m n}
--   → (f : Δ-Hom⁻ m n)
--   → ∀ i → fibre (Δ⁻-map f) i
-- Δ⁻-map-split-surj (crush⁻ f) i with Δ⁻-map-split-surj f i
-- ... | fzero , p = fsuc fzero , p
-- ... | fsuc j , p = fsuc (fsuc j) , p
-- Δ⁻-map-split-surj (keep⁻ f) fzero = fzero , refl
-- Δ⁻-map-split-surj (keep⁻ f) (fsuc i) =
--   Σ-map fsuc (ap fsuc) (Δ⁻-map-split-surj f i)
-- ```

-- ```agda
-- test : Fin 2 → Fin 3
-- test = Δ⁺-map (keep⁺ (shift⁺ id⁺))

-- foo : Fin 3
-- foo = {!!}
-- ```
