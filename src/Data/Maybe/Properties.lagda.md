<!--
```agda
open import 1Lab.Prelude

open import Data.Maybe.Base
open import Data.List.Base using (_∷_; [])
open import Data.Dec.Base
open import Data.Nat.Base
open import Data.Sum.Base
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
  Equiv→is-hlevel (1 + n) (MaybePath.Path≃Code x y) (MaybePath.Code-is-hlevel n ahl)
```

<!--
```agda
instance
  H-Level-Maybe
    : ∀ {ℓ} {A : Type ℓ} {n} ⦃ _ : 2 ≤ n ⦄ ⦃ _ : H-Level A n ⦄
    → H-Level (Maybe A) n
  H-Level-Maybe {n = suc (suc n)} ⦃ s≤s (s≤s p) ⦄ = hlevel-instance $
    Maybe-is-hlevel n (hlevel (2 + n))
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
-- Finite-Maybe
--   : ⦃ fa : Finite A ⦄
--   → Finite (Maybe A)
-- Finite-Maybe ⦃ fa ⦄ .cardinality = suc (fa .cardinality)
-- Finite-Maybe {A = A} ⦃ fa ⦄ .enumeration =
--   ∥-∥-map (Iso→Equiv ∘ maybe-iso) (fa .enumeration) where
--     maybe-iso : A ≃ Fin (fa .cardinality) → Iso (Maybe A) (Fin (suc (fa .cardinality)))
--     maybe-iso f .fst (just x) = fsuc (Equiv.to f x)
--     maybe-iso f .fst nothing = fzero
--     maybe-iso f .snd .is-iso.inv fzero = nothing
--     maybe-iso f .snd .is-iso.inv (fsuc i) = just (Equiv.from f i)
--     maybe-iso f .snd .is-iso.rinv fzero = refl
--     maybe-iso f .snd .is-iso.rinv (fsuc i) = ap fsuc (Equiv.ε f i)
--     maybe-iso f .snd .is-iso.linv (just x) = ap just (Equiv.η f x)
--     maybe-iso f .snd .is-iso.linv nothing = refl
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

```agda
Maybe-injective : Maybe A ≃ Maybe B → A ≃ B
Maybe-injective e = Iso→Equiv (a→b , iso b→a (lemma e) il) where
  a→b = maybe-injective e
  b→a = maybe-injective (Equiv.inverse e)

  module _ (e : Maybe A ≃ Maybe B) where abstract
    private
      module e = Equiv e
      module e⁻¹ = Equiv e.inverse

    lemma : is-right-inverse (maybe-injective (Equiv.inverse e)) (maybe-injective e)
    lemma x with inspect (e.from (just x))
    lemma x | just y , p with inspect (e.to (just y))
    lemma x | just y , p | just z  , q = just-inj (sym q ∙ ap e.to (sym p) ∙ e.ε _)
    lemma x | just y , p | nothing , q with inspect (e.to nothing)
    lemma x | just y , p | nothing , q | nothing , r = absurd (just≠nothing (e.injective₂ q r))
    lemma x | just y , p | nothing , q | just z  , r = absurd (nothing≠just (sym q ∙ ap e.to (sym p) ∙ e.ε _))
    lemma x | nothing , p with inspect (e.from nothing)
    lemma x | nothing , p | nothing , q = absurd (just≠nothing (e⁻¹.injective₂ p q))
    lemma x | nothing , p | just y , q with inspect (e.to (just y))
    lemma x | nothing , p | just y , q | just z  , r = absurd (just≠nothing (sym r ∙ ap e.to (sym q) ∙ e.ε _))
    lemma x | nothing , p | just y , q | nothing , r with inspect (e.to nothing)
    lemma x | nothing , p | just y , q | nothing , r | nothing , s = absurd (just≠nothing (e.injective₂ r s))
    lemma x | nothing , p | just y , q | nothing , r | just z , s = just-inj (sym s ∙ ap e.to (sym p) ∙ e.ε _)

  abstract
    il : is-left-inverse b→a a→b
    il = p' where
      p : is-right-inverse (maybe-injective (Equiv.inverse (Equiv.inverse e))) (maybe-injective (Equiv.inverse e))
      p = lemma (Equiv.inverse e)

      p' : is-right-inverse (maybe-injective e) (maybe-injective (Equiv.inverse e))
      p' = subst
        (λ e' → is-right-inverse (maybe-injective e') (maybe-injective (Equiv.inverse e)))
        {Equiv.inverse (Equiv.inverse e)} {e}
        trivial! p

Maybe-is-sum : Maybe A ≃ (⊤ ⊎ A)
Maybe-is-sum {A = A} = Iso→Equiv (to , iso from ir il) where
  to   : Maybe A → ⊤ ⊎ A
  to (just x) = inr x
  to nothing = inl tt

  from : ⊤ ⊎ A → Maybe A
  from (inr x) = just x
  from (inl _) = nothing

  ir : is-right-inverse from to
  ir (inl x) = refl
  ir (inr x) = refl

  il : is-right-inverse to from
  il nothing = refl
  il (just x) = refl
```
