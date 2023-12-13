<!--
```agda
open import 1Lab.Prelude

open import Data.Fin.Finite
open import Data.Maybe.Base
open import Data.List.Base using (_∷_; [])
open import Data.Dec.Base
open import Data.Nat.Base
open import Data.Fin
```
-->

```agda
module Data.Maybe.Properties where
```

<!--
```agda
private variable
  ℓ ℓ' : Level
  A B C : Type ℓ
```
-->

# Properties of Maybe

## Path space

We can use these lemmas to characterise the path space of `Maybe A` in
terms of the path space of `A`. This involves a standard encode-decode
argument: for a more in-depth explanation, see [`Data.List`].

[`Data.List`]: Data.List.html

```agda
module MaybePath {ℓ} {A : Type ℓ} where
  Code : Maybe A → Maybe A → Type _
  Code (just x) (just y) = x ≡ y
  Code (just x) nothing  = Lift _ ⊥
  Code nothing (just y)  = Lift _ ⊥
  Code nothing nothing   = Lift _ ⊤
```

<details>
<summary>The rest of this argument is standard, so we omit it.
</summary>

```agda
  refl-code : ∀ x → Code x x
  refl-code (just x) = refl
  refl-code nothing = lift tt

  decode : ∀ x y → Code x y → x ≡ y
  decode (just x) (just y) p = ap just p
  decode nothing nothing _ = refl

  encode : ∀ x y → x ≡ y → Code x y
  encode (just x) (just y) p = just-inj p
  encode (just x) nothing p = absurd (just≠nothing p)
  encode nothing (just x) p = absurd (nothing≠just p)
  encode nothing nothing p = lift tt

  encode-refl : ∀ {x} → encode x x refl ≡ refl-code x
  encode-refl {x = just x} = refl
  encode-refl {x = nothing} = refl

  decode-refl : ∀ {x} → decode x x (refl-code x) ≡ refl
  decode-refl {x = just x} = refl
  decode-refl {x = nothing} = refl

  decode-encode : ∀ {x y} → (p : x ≡ y) → decode x y (encode x y p) ≡ p
  decode-encode {x = x} =
    J (λ y' p → decode x y' (encode x y' p) ≡ p)
      (ap (decode x x) encode-refl ∙ decode-refl)

  encode-decode : ∀ {x y} → (p : Code x y) → encode x y (decode x y p) ≡ p
  encode-decode {just x} {just y} p = refl
  encode-decode {nothing} {nothing} p = refl

  Path≃Code : ∀ x y → (x ≡ y) ≃ Code x y
  Path≃Code x y =
    Iso→Equiv (encode x y , iso (decode x y) encode-decode decode-encode)

  Code-is-hlevel
    : {x y : Maybe A} (n : Nat)
    → is-hlevel A (2 + n)
    → is-hlevel (Code x y) (1 + n)
  Code-is-hlevel {x = just x} {y = just y} n ahl = ahl x y
  Code-is-hlevel {x = just x} {y = nothing} n ahl = hlevel (1 + n)
  Code-is-hlevel {x = nothing} {y = just x} n ahl = hlevel (1 + n)
  Code-is-hlevel {x = nothing} {y = nothing} n ahl = hlevel (1 + n)
```
</details>

Now that we've characterised the path space, we can determine the h-level
of `Maybe`.

```agda
Maybe-is-hlevel
  : (n : Nat)
  → is-hlevel A (2 + n)
  → is-hlevel (Maybe A) (2 + n)
Maybe-is-hlevel n ahl x y =
  is-hlevel≃ (1 + n) (MaybePath.Path≃Code x y) (MaybePath.Code-is-hlevel n ahl)
```

<!--
```agda
instance
  decomp-maybe : ∀ {ℓ} {A : Type ℓ} → hlevel-decomposition (Maybe A)
  decomp-maybe = decomp (quote Maybe-is-hlevel) (`level-minus 2 ∷ `search ∷ [])
```
-->

We also note that `just`{.Agda} is an [[embedding]]; this follows
immediately from the characterisation of the path space.

```agda
just-cancellable : ∀ {x y : A} → (just x ≡ just y) ≃ (x ≡ y)
just-cancellable {x = x} {y = y} = MaybePath.Path≃Code (just x) (just y)

just-is-embedding : is-embedding (just {A = A})
just-is-embedding = cancellable→embedding just-cancellable
```

This lets us show that `Maybe` reflects h-levels.

```agda
Maybe-reflect-hlevel
  : (n : Nat)
  → is-hlevel (Maybe A) (2 + n)
  → is-hlevel A (2 + n)
Maybe-reflect-hlevel n mhl =
  embedding→is-hlevel {f = just} (1 + n) just-is-embedding mhl
```

## Discreteness

If `Maybe A` is discrete, then `A` must also be discrete. This follows
from the fact that `just` is injective.

```agda
Maybe-reflect-discrete
  : Discrete (Maybe A)
  → Discrete A
Maybe-reflect-discrete eq? = Discrete-inj just just-inj eq?
```

## Finiteness

If `A` is finite, then `Maybe A` is also finite.

```agda
Finite-Maybe
  : ⦃ fa : Finite A ⦄
  → Finite (Maybe A)
Finite-Maybe ⦃ fa ⦄ .cardinality = suc (fa .cardinality)
Finite-Maybe {A = A} ⦃ fa ⦄ .enumeration =
  ∥-∥-map (Iso→Equiv ∘ maybe-iso) (fa .enumeration) where
    maybe-iso : A ≃ Fin (fa .cardinality) → Iso (Maybe A) (Fin (suc (fa .cardinality)))
    maybe-iso f .fst (just x) = fsuc (Equiv.to f x)
    maybe-iso f .fst nothing = fzero
    maybe-iso f .snd .is-iso.inv fzero = nothing
    maybe-iso f .snd .is-iso.inv (fsuc i) = just (Equiv.from f i)
    maybe-iso f .snd .is-iso.rinv fzero = refl
    maybe-iso f .snd .is-iso.rinv (fsuc i) = ap fsuc (Equiv.ε f i)
    maybe-iso f .snd .is-iso.linv (just x) = ap just (Equiv.η f x)
    maybe-iso f .snd .is-iso.linv nothing = refl
```

# Misc. properties

If `A` is empty, then a `Maybe A` must be `nothing`{.Agda}.

```agda
refute-just : ¬ A → (x : Maybe A) → x ≡ nothing
refute-just ¬a (just a) = absurd (¬a a)
refute-just ¬a nothing = refl
```

As a corollary, if `A` is empty, then `Maybe A` is contractible.

```agda
empty→maybe-is-contr : ¬ A → is-contr (Maybe A)
empty→maybe-is-contr ¬a .centre = nothing
empty→maybe-is-contr ¬a .paths x = sym $ refute-just ¬a x
```

Next, note that `map`{.Agda} is functorial.

```agda
map-id : ∀ {ℓ} {A : Type ℓ} (x : Maybe A) → map id x ≡ x
map-id (just x) = refl
map-id nothing = refl

map-∘
  : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} {f : B → C} {g : A → B}
  → (x : Maybe A)
  → map (f ∘ g) x ≡ map f (map g x)
map-∘ (just x) = refl
map-∘ nothing = refl
```

Furthermore, `<|>` is left and right unital, associative, and is preserved by
`map`.

```agda
<|>-idl : ∀ {A : Type ℓ} → (x : Maybe A) → (nothing <|> x) ≡ x
<|>-idl x = refl

<|>-idr : ∀ {A : Type ℓ} → (x : Maybe A) → (x <|> nothing) ≡ x
<|>-idr (just x) = refl
<|>-idr nothing = refl

<|>-assoc
  : ∀ {A : Type ℓ}
  → (x y z : Maybe A)
  → (x <|> (y <|> z)) ≡ ((x <|> y) <|> z)
<|>-assoc (just x) y z = refl
<|>-assoc nothing y z = refl

map-<|>
  : ∀ {A : Type ℓ} {B : Type ℓ'} {f : A → B}
  → (x y : Maybe A)
  → map f (x <|> y) ≡ (map f x <|> map f y)
map-<|> (just x) y = refl
map-<|> nothing y = refl
```
