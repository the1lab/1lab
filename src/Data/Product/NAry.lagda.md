<!--
```agda
open import 1Lab.Path
open import 1Lab.Type
```
-->

```agda
module Data.Product.NAry where
```

# n-Ary products

This is an alternative definition of the type of n-ary products, which,
unlike [`Vec`](Data.Vec.Base.html), is defined by _recursion_ on the
length.

```agda
Vecₓ : ∀ {ℓ} → Type ℓ → Nat → Type ℓ
Vecₓ A 0             = Lift _ ⊤
Vecₓ A 1             = A
Vecₓ A (suc (suc n)) = A × Vecₓ A (suc n)
```

The point of having the type `Vecₓ`{.Agda} around is that its
inhabitants can be written using the usual tuple syntax, so that we can
define a `From-product`{.Agda} "type class" for those type constructors
(possibly indexed by the length) which can be built as a sequence of
arguments.

```agda
_ : Vecₓ Nat 3
_ = 1 , 2 , 3

record From-product {ℓ} (A : Type ℓ) (T : Nat → Type ℓ) : Type ℓ where
  field from-prod : ∀ n → Vecₓ A n → T n
```

Shuffling the arguments to `from-prod`{.Agda} slightly, we arrive at the
"list syntax" construction:

```agda
[_] : ∀ {ℓ} {A : Type ℓ} {T : Nat → Type ℓ} {n} ⦃ fp : From-product A T ⦄
    → Vecₓ A n → T n
[_] ⦃ fp = fp ⦄ = fp .From-product.from-prod _
```
