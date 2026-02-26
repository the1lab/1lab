<!--
```agda
open import 1Lab.Path.IdentitySystem
open import 1Lab.HLevel.Closure
open import 1Lab.Equiv
open import 1Lab.Path
open import 1Lab.Type

open import Data.Dec.Base
```
-->

```agda
module Data.Bool.Base where
```

<!--
```agda
open import Prim.Data.Bool public
```
-->

```agda
true≠false : ¬ true ≡ false
true≠false p = subst P p tt where
  P : Bool → Type
  P false = ⊥
  P true = ⊤
```

<!--
```agda
false≠true : ¬ false ≡ true
false≠true = true≠false ∘ sym
```
-->

```agda
not : Bool → Bool
not true = false
not false = true

and or : Bool → Bool → Bool
and false y = false
and true y = y

or false y = y
or true y = true
```

```agda
instance
  Discrete-Bool : Discrete Bool
  Discrete-Bool .decide false false = yes refl
  Discrete-Bool .decide false true  = no false≠true
  Discrete-Bool .decide true  false = no true≠false
  Discrete-Bool .decide true  true  = yes refl
```

<!--
```agda
instance
  H-Level-Bool : ∀ {n} → H-Level Bool (2 + n)
  H-Level-Bool = basic-instance 2 (Discrete→is-set auto)
```
-->

```agda
x≠true→x≡false : (x : Bool) → x ≠ true → x ≡ false
x≠true→x≡false false p = refl
x≠true→x≡false true p = absurd (p refl)

x≠false→x≡true : (x : Bool) → x ≠ false → x ≡ true
x≠false→x≡true false p = absurd (p refl)
x≠false→x≡true true p = refl
```


<!--
```agda
if : ∀ {ℓ} {A : Type ℓ} → A → A → Bool → A
if x y false = y
if x y true = x

infix 0 if_then_else_

if_then_else_ : ∀ {ℓ} {A : Type ℓ} → Bool → A → A → A
if false then t else f = f
if true then t else f = t

Bool-elim : ∀ {ℓ} (A : Bool → Type ℓ) → A true → A false → ∀ x → A x
Bool-elim A at af true = at
Bool-elim A at af false = af
```
-->

```agda
is-true : Bool → Type
is-true true = ⊤
is-true false = ⊥

record So (b : Bool) : Type where
  constructor erase
  field
    @irr is-so : is-true b
```

<!--
```agda
so-true : So true
so-true = erase tt

¬so-false : So false → ⊥
¬so-false ()

oh? : ∀ x → Dec (So x)
oh? true = yes so-true
oh? false = no ¬so-false

not-so : ∀ {x} → ¬ (So x) → So (not x)
not-so {true} ¬p = absurd (¬p so-true)
not-so {false} ¬p = so-true

instance
  H-Level-So : ∀ {x n} → H-Level (So x) (suc n)
  H-Level-So = prop-instance (λ _ _ → refl)

  Dec-So : ∀ {x} → Dec (So x)
  Dec-So {x} = oh? x
```
-->


## The "not" equivalence

The construction of `not`{.Agda} as an equivalence factors through
showing that `not` is an isomorphism. In particular, `not`{.Agda} is its
own inverse, so we need a proof that it's involutive, as is proven in
`not-involutive`{.Agda}.  With this, we can get a proof that it's an
equivalence:

```agda
not-involutive : (x : Bool) → not (not x) ≡ x
not-involutive false i = false
not-involutive true  i = true

not-is-equiv : is-equiv not
not-is-equiv = is-involutive→is-equiv not-involutive

not≃ : Bool ≃ Bool
not≃ = not , not-is-equiv
```
