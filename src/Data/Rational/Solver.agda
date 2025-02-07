open import 1Lab.Reflection.Variables
open import 1Lab.Reflection hiding (absurd)
open import 1Lab.Prelude

open import Algebra.Ring.Cat.Initial
open import Algebra.Ring.Commutative
open import Algebra.Ring.Solver renaming (module Impl to RImpl)
open import Algebra.Ring

open import Cat.Displayed.Total

open import Data.Rational.Properties
open import Data.Set.Coequaliser
open import Data.Rational.Base
open import Data.Fin.Base
open import Data.Nat.Base

import Data.Int.Properties as ℤ
import Data.Rational.Base as Rat renaming (-ℚ_ to neg)
import Data.Int.Base as ℤ

module Data.Rational.Solver where

private
  module R = RImpl (ℚ-ring .snd)
  module Re = Explicit ℚ-ring
  module ℤs = Explicit ℤ-comm

open is-ring-hom

{-
Equational solver for expressions over the rational numbers. The
strategy is as follows:

- First, we reflect (accurately) a pair of rational expressions into a
  value of 'Exp', defined below, which contains constructors for all the
  basic operations on ℚ. Note that, since _/ℚ_ and _-ℚ_ are neutral on
  neutral values (i.e. they don't compute to x *ℚ invℚ y or x +ℚ (-ℚ y)
  until x and y are actual fractions --- in which case they'll also
  compute further, anyway), we have to reflect them, too.

  Note that the 'Exp' type can represent possibly ill-formed
  expressions, since it can have free variables in denominators. E.g.,
  the expression var 1 :/ var 0, by itself, does not carry enough
  information to be evaluated back into ℚ.

  Therefore, we define, by mutual recursion, a procedure for evaluating
  expressions back into ℚ, and a well-formedness predicate, relative to
  an environment, which records proof that every denominator is
  invertible.

- We can then use the definitions of arithmetic operations over
  fractions to split an expression over ℚ to a pair of polynomials
  (nominally over ℤ, but we stay over ℚ so we don't have to split the
  environment), representing a formal quotient.

  E.g., if e1 splits into x / u and e2 splits into y / v, then
    (e1 :+ e2) splits into (x * v + y * u) / (u * v).

  Then, we can re-use the existing ring solver: To show ⟦ e1 ⟧ = ⟦ e2 ⟧,
  it suffices to split e1 = x / u and e2 = y / v, then ask the ring
  solver to show x * v ≡ y * u.

However, the law of preservation of frustration applies: to invoke the
ring solver, we have to show that the procedure for splitting an
expression into polynomials is sound. We do this by recursion-recursion.
Assuming e is well-formed in Γ, the two theorems are

* split-denom-nz shows that the denominator of e is nonzero in ℚ
* split-sound shows that (numerator e / denominator e) is ⟦ e ⟧ in ℚ

Note that, to state split-sound, we need split-denom-nz, since otherwise
there would be no evidence that (denominator e) is something we can
divide by.
-}

module Impl where
  data Exp (n : Nat) : Type where
    var : Fin n → Exp n
    con : Fraction → Exp n
    _:+_ _:*_ _:-_ _:/_ : Exp n → Exp n → Exp n
    neg inv : Exp n → Exp n

  Wf : ∀ {n} (e : Exp n) (env : Vec ℚ n) → Type
  embed : ∀ {n} (e : Exp n) (env : Vec ℚ n) → Wf e env → ℚ

  Wf (var x) env  = ⊤
  Wf (con x) env  = ⊤
  Wf (x :+ y) env = Wf x env × Wf y env
  Wf (x :* y) env = Wf x env × Wf y env
  Wf (x :- y) env = Wf x env × Wf y env
  Wf (x :/ y) env = Wf x env × Σ[ y' ∈ Wf y env ] Nonzero (embed y env y')
  Wf (neg x) env  = Wf x env
  Wf (inv x) env  = Σ[ x' ∈ Wf x env ] Nonzero (embed x env x')

  embed (var x)  env tt              = lookup env x
  embed (con x)  env tt              = toℚ x
  embed (x :+ y) env (wx , wy)       = embed x env wx +ℚ embed y env wy
  embed (x :* y) env (wx , wy)       = embed x env wx *ℚ embed y env wy
  embed (x :- y) env (wx , wy)       = embed x env wx -ℚ embed y env wy
  embed (x :/ y) env (wx , wy , nzy) = (embed x env wx /ℚ embed y env wy) ⦃ nzy ⦄
  embed (neg x)  env wf              = -ℚ (embed x env wf)
  embed (inv x)  env (wf , nz)       = invℚ (embed x env wf) ⦃ nz ⦄

  split : ∀ {n} → Exp n → R.Polynomial n × R.Polynomial n
  split (var x) = R.var x , 1
  split (con (n / d [ p ])) = R.con n , R.con d
  split (x :+ y) with (xn , xd) ← split x | (yn , yd) ← split y = xn R.:* yd R.:+ yn R.:* xd , xd R.:* yd
  split (x :* y) with (xn , xd) ← split x | (yn , yd) ← split y = xn R.:* yn , xd R.:* yd
  split (x :- y) with (xn , xd) ← split x | (yn , yd) ← split y = xn R.:* yd R.:- yn R.:* xd , xd R.:* yd
  split (x :/ y) with (xn , xd) ← split x | (yn , yd) ← split y = xn R.:* yd , xd R.:* yn
  split (neg x) with (xn , xd) ← split x = R.:- xn , xd
  split (inv x) with (xn , xd) ← split x = xd , xn

  rem₁ : ∀ d → R.embed-coe d ≡ d Rat./ 1
  rem₁ = R.embed-lemma λ where
    .pres-id → refl
    .pres-+ (lift x) (lift y) → quotℚ (to-same-rational (ℤs.solve 2 (λ x y → (x ℤs.:+ y) ℤs.:* 1 ℤs.≔ (x ℤs.:* 1 ℤs.:+ y ℤs.:* 1) ℤs.:* 1) x y refl))
    .pres-* (lift x) (lift y) → refl

  module _ {n} (env : Vec ℚ n) where
    ↑e : Exp n → ℚ
    ↑e e = ⟦ split e .fst ⟧ env

    ↓e : Exp n → ℚ
    ↓e e = ⟦ split e .snd ⟧ env

    split-denom-nz : ∀ e → Wf e env → Nonzero (↓e e)
    split-sound
      : ∀ (e : Exp n) (ewf : Wf e env)
      → _/ℚ_ (↑e e) (↓e e) ⦃ split-denom-nz e ewf ⦄ ≡ embed e env ewf

    split-denom-nz (var x) wf = auto
    split-denom-nz (con (n / d [ p ])) wf =
      subst Nonzero (sym (rem₁ d))
        (inc λ q → ℤ.positive→nonzero p (sym (ℤ.*ℤ-oner d) ∙ from-same-rational (unquotℚ q)))
    split-denom-nz (x :+ y) (wx , wy) = *ℚ-nonzero (split-denom-nz x wx) (split-denom-nz y wy)
    split-denom-nz (x :* y) (wx , wy) = *ℚ-nonzero (split-denom-nz x wx) (split-denom-nz y wy)
    split-denom-nz (x :- y) (wx , wy) = *ℚ-nonzero (split-denom-nz x wx) (split-denom-nz y wy)
    split-denom-nz (x :/ y) (wx , wy , wnz) = *ℚ-nonzero (split-denom-nz x wx)
      (/ℚ-nonzero-num
        (subst Nonzero (sym (split-sound y wy)) wnz))
      where instance nz1 = split-denom-nz y wy
    split-denom-nz (neg e) we = split-denom-nz e we
    split-denom-nz (inv e) (we , wnz) = /ℚ-nonzero-num (subst Nonzero (sym (split-sound e we)) wnz)
      where instance nz1 = split-denom-nz e we

    split-sound (var x) ewf = /ℚ-oner (lookup env x)
    split-sound (con (n / d [ p ])) ewf =
        /ℚ-ap {q = to-nonzero-frac (ℤ.positive→nonzero p)} (rem₁ n) (rem₁ d)
      ∙ /ℚ-frac {n} {d} ⦃ p ⦄

    split-sound (x :+ y) (xw , yw) =
      (↑e x *ℚ ↓e y +ℚ ↑e y *ℚ ↓e x) /ℚ (↓e x *ℚ ↓e y) ≡˘⟨ /ℚ-def-+ℚ ⟩
      (↑e x /ℚ ↓e x) +ℚ (↑e y /ℚ ↓e y)                 ≡⟨ ap₂ _+ℚ_ (split-sound x xw) (split-sound y yw) ⟩
      embed x env xw +ℚ embed y env yw                 ∎
      where instance
        nz1 = split-denom-nz x xw
        nz2 = split-denom-nz y yw

    split-sound (x :* y) (xw , yw) =
      (↑e x *ℚ ↑e y) /ℚ (↓e x *ℚ ↓e y) ≡˘⟨ /ℚ-def-*ℚ ⟩
      (↑e x /ℚ ↓e x) *ℚ (↑e y /ℚ ↓e y) ≡⟨ ap₂ _*ℚ_ (split-sound x xw) (split-sound y yw) ⟩
      embed x env xw *ℚ embed y env yw                 ∎
      where instance
        nz2 = split-denom-nz y yw
        nz3 = split-denom-nz x xw

    split-sound (x :- y) (xw , yw) =
      (↑e x *ℚ ↓e y +ℚ -ℚ (↑e y *ℚ ↓e x)) /ℚ (↓e x *ℚ ↓e y) ≡⟨ /ℚ-ap (-ℚ-def _ _) refl ⟩
      (↑e x *ℚ ↓e y -ℚ ↑e y *ℚ ↓e x) /ℚ (↓e x *ℚ ↓e y)      ≡˘⟨ /ℚ-def-subℚ ⟩
      (↑e x /ℚ ↓e x) -ℚ (↑e y /ℚ ↓e y)                      ≡⟨ ap₂ _-ℚ_ (split-sound x xw) (split-sound y yw) ⟩
      embed x env xw -ℚ embed y env yw                      ∎
      where instance
        nz1 = split-denom-nz y yw
        nz2 = split-denom-nz x xw

    split-sound (x :/ y) (xw , yw , ynz) =
      let
        instance
          nz1 = split-denom-nz x xw
          nz2 = split-denom-nz y yw
          nz3 = ynz
          nz4 = subst Nonzero (sym (split-sound y yw)) ynz
          nz5 = /ℚ-nonzero-num {↑e y} {↓e y} auto
      in
        (↑e x *ℚ ↓e y) /ℚ (↓e x *ℚ ↑e y)               ≡⟨ /ℚ-def ⟩
        (↑e x *ℚ ↓e y) *ℚ invℚ (↓e x *ℚ ↑e y)          ≡⟨ ap₂ _*ℚ_ (λ i → ↑e x *ℚ ↓e y) invℚ-*ℚ ⟩
        (↑e x *ℚ ↓e y) *ℚ (invℚ (↓e x) *ℚ invℚ (↑e y)) ≡⟨ Re.solve 4 (λ x y u v → (x Re.:* y) Re.:* (u Re.:* v) Re.≔ (x Re.:* u) Re.:* (y Re.:* v)) (↑e x) (↓e y) (invℚ (↓e x)) (invℚ (↑e y)) refl ⟩
        (↑e x *ℚ invℚ (↓e x)) *ℚ (↓e y *ℚ invℚ (↑e y)) ≡˘⟨ ap₂ _*ℚ_ /ℚ-def refl ⟩
        (↑e x /ℚ ↓e x) *ℚ (↓e y *ℚ invℚ (↑e y))        ≡˘⟨ ap₂ _*ℚ_ refl (invℚ-*ℚ ∙ *ℚ-commutative _ _ ∙ ap₂ _*ℚ_ invℚ-invℚ refl) ⟩
        (↑e x /ℚ ↓e x) *ℚ invℚ (↑e y *ℚ invℚ (↓e y))   ≡˘⟨ ap₂ _*ℚ_ refl (ap₂ (λ e p → invℚ e ⦃ p ⦄) /ℚ-def prop!) ⟩
        (↑e x /ℚ ↓e x) *ℚ invℚ (↑e y /ℚ ↓e y)          ≡⟨ sym /ℚ-def ⟩
        (↑e x /ℚ ↓e x) /ℚ (↑e y /ℚ ↓e y)               ≡⟨ /ℚ-ap (split-sound x xw) (split-sound y yw) ⟩
        embed x env xw /ℚ embed y env yw               ∎

    split-sound (neg e) ewf =
      (-ℚ (↑e e)) /ℚ ↓e e  ≡˘⟨ /ℚ-negatel ⟩
      -ℚ (↑e e /ℚ ↓e e)    ≡⟨ ap -ℚ_ (split-sound e ewf) ⟩
      -ℚ embed e env ewf   ∎
      where instance nz1 = split-denom-nz e ewf

    split-sound (inv e) (ewf , enz) =
      ↓e e /ℚ ↑e e                 ≡˘⟨ invℚ-/ℚ ⦃ _ ⦄ ⦃ _ ⦄ ⟩
      invℚ (↑e e /ℚ ↓e e)          ≡⟨ ap₂ (λ e p → invℚ e ⦃ p ⦄) (split-sound e ewf) (to-pathp refl) ⟩
      invℚ (embed e env ewf) ⦃ _ ⦄ ∎
      where instance
        nz1 = split-denom-nz e ewf
        nz2 = /ℚ-nonzero-num {↑e e} {↓e e} (subst Nonzero (sym (split-sound e ewf)) enz)

  module _ {n} (x y : Exp n) (env : Vec ℚ n) where abstract
    open Σ (split x) renaming (fst to ↑x ; snd to ↓x)
    open Σ (split y) renaming (fst to ↑y ; snd to ↓y)

    solve
      : R.En (R.normal (↑x R.:* ↓y)) env ≡ R.En (R.normal (↑y R.:* ↓x)) env
      → ∀ wfx wfy → embed x env wfx ≡ embed y env wfy
    solve p wfx wfy =
      embed x env wfx                ≡˘⟨ split-sound env x wfx ⟩
      R.eval ↑x env /ℚ R.eval ↓x env ≡⟨ /ℚ-same (R.solve (↑x R.:* ↓y) (↑y R.:* ↓x) env p) ⟩
      ↑e env y /ℚ ↓e env y           ≡⟨ split-sound env y wfy ⟩
      embed y env wfy                ∎
      where instance
        nz1 : Nonzero (↓e env x)
        nz1 = split-denom-nz env x wfx

        nz2 : Nonzero (↓e env y)
        nz2 = split-denom-nz env y wfy

build : Variables ℚ → Term → TC (Term × Variables ℚ)
build vars (con (quote ℚ.inc)
  (con (quote Coeq.inc) (_ h∷ _ h∷ _ h∷ _ h∷ _ h∷ _ h∷ f v∷ []) v∷ [])) =
  pure (con (quote Impl.con) (f v∷ []) , vars)

build vars (def (quote _+ℚ_) (x v∷ y v∷ [])) = do
  (x , vars) ← build vars x
  (y , vars) ← build vars y
  pure (con (quote Impl._:+_) (x v∷ y v∷ []) , vars)

build vars (def (quote _*ℚ_) (x v∷ y v∷ [])) = do
  (x , vars) ← build vars x
  (y , vars) ← build vars y
  pure (con (quote Impl._:*_) (x v∷ y v∷ []) , vars)

build vars (def (quote _-ℚ_) (x v∷ y v∷ [])) = do
  (x , vars) ← build vars x
  (y , vars) ← build vars y
  pure (con (quote Impl._:-_) (x v∷ y v∷ []) , vars)

build vars (def (quote Rat.neg) (x v∷ [])) = do
  (x , vars) ← build vars x
  pure (con (quote Impl.neg) (x v∷ []) , vars)

build vars (def (quote invℚ) (x v∷ arg _ y ∷ [])) = do
  (x , vars) ← build vars x
  pure (con (quote Impl.inv) (x v∷ []) , vars)

build vars (def (quote _/ℚ_) (x v∷ y v∷ arg _ i ∷ [])) = do
  (x , vars) ← build vars x
  (y , vars) ← build vars y
  pure (con (quote Impl._:/_) (x v∷ y v∷ []) , vars)

build vars tm = do
  (v , vars) ← bind-var vars tm
  pure (con (quote Impl.var) (argN v ∷ []) , vars)

private
  dr : List Name
  dr = [ quote _+ℚ_ , quote _*ℚ_ , quote Rat.neg , quote _-ℚ_ , quote _/ℚ_ , quote invℚ  ]

rational!-worker : Term → TC ⊤
rational!-worker hole = withNormalisation false $ withReduceDefs (false , dr) $ do
  goal ← infer-type hole >>= wait-for-type
  just (lhs , rhs) ← get-boundary goal
    where nothing → typeError $ strErr "Can't determine boundary: " ∷
                                termErr goal ∷ []
  elhs , vs ← normalise lhs >>= build empty-vars
  erhs , vs ← normalise rhs >>= build vs
  size , env ← environment vs

  withReduceDefs (false , []) do
    -- Note: it's important that we allow the operators over ℚ to
    -- compute, but only after we've already built the expression. This
    -- lets us take advantage of the definitional equalities of _+ℚ_
    -- etc.
    done ← check-type (def (quote Impl.solve) (elhs v∷ erhs v∷ env v∷ def₀ (quote refl) v∷ unknown v∷ unknown v∷ [])) goal
    unify hole done

macro
  rational! : Term → TC ⊤
  rational! = rational!-worker

module _ (a b c : ℚ) ⦃ pa : Nonzero a ⦄ ⦃ pb : Nonzero b ⦄ ⦃ pc : Nonzero c ⦄ where
  _ : (a /ℚ 3) +ℚ (a /ℚ 3) ≡ ((a *ℚ 2) /ℚ 3)
  _ = rational!

  _ : ((a +ℚ b) *ℚ c) ≡ (a *ℚ c) +ℚ (c *ℚ b)
  _ = rational!

  _ : ((a *ℚ b) /ℚ c) ≡ ((a *ℚ c) /ℚ c) *ℚ (b /ℚ c)
  _ = rational!

  _ : ((a *ℚ c) /ℚ c) ≡ a
  _ = rational!

  _ : (a /ℚ 3) +ℚ (b /ℚ 2) ≡ ((a *ℚ 2) +ℚ (b *ℚ 3)) /ℚ 6
  _ = rational!

  _ : ∀ {pc' : Nonzero c} → invℚ c ⦃ pc ⦄ ≡ invℚ c ⦃ pc' ⦄
  _ = rational!
