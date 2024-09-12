open import 1Lab.Reflection hiding ([_])
open import 1Lab.Prelude

open import Data.Rational.Base hiding (_/_)

module Data.Rational.Reflection where

open 1Lab.Reflection using (Bind-TC) public

{-

Simple macro that automates wrapping ℚ-elim-propⁿ so the first n ℚ
arguments are implicit.

  foo : ∀ {x y z} → P
  unquoteDef foo = by-elim-ℚ foo ?body

is equivalent to

  foo {x} {y} {z} = ℚ-elim-propⁿ {P} ?body

The number of arguments to induct over is the number of implicit pis
with ℚ domain at the head of the type. The function being defined must
have a type signature with no metas.
-}

private
  strip-leading-impl-ℚs : Term → Telescope × Term
  strip-leading-impl-ℚs it@(pi (arg i ty) (abs nm b)) = go (i .ArgInfo.arg-vis) ty module spi where
    go : Visibility → Term → Telescope × Term
    go hidden (def₀ (quote ℚ)) with (etel , tm') ← strip-leading-impl-ℚs b =
      (nm , arg (set-visibility visible i) ty) ∷ etel , tm'
    go _ ty = [] , it
  strip-leading-impl-ℚs tm = [] , tm

by-elim-ℚ : ∀ {ℓ} (n : Name) {ty : Type ℓ} → ty → TC ⊤
by-elim-ℚ nm body = do
  ty ← get-type nm >>= wait-for-type

  let
    (tel , motive) = strip-leading-impl-ℚs ty
    motive = tel→lam tel motive

    patel = set-visibility hidden tel

  body ← quoteTC body
  let
    body = def (quote ℚ-elim-propⁿ) $
      argN (lit (nat (length tel))) ∷
      argH unknown ∷ -- level
      argH motive ∷
      argN body ∷
      tel→args 0 tel

  define-function nm (clause patel (tel→pats 0 patel) body ∷ [])
