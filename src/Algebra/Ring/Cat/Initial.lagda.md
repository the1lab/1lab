<!--
```agda
open import Algebra.Group.Ab
open import Algebra.Group
open import Algebra.Ring

open import Cat.Displayed.Univalence.Thin
open import Cat.Diagram.Initial
open import Cat.Prelude hiding (_+_ ; _*_)

open import Data.Int.Properties
open import Data.Int.Base

import Algebra.Ring.Reasoning as Kit

import Data.Nat as Nat
```
-->

```agda
module Algebra.Ring.Cat.Initial {ℓ} where
```

# The initial ring {defines="initial-ring"}

We have, in the introduction to rings, mentioned offhand that the ring
$\ZZ$ is an initial object. This turns out to be a fairly nontrivial
theorem to formalise, so we have decided to do so in this module. For
starters, note that the ring $\ZZ$ is an object of the category of
"rings in the zeroth universe", whereas we would like any category of
$\kappa$-compact rings to have its own initial object. So, the first
thing we must do is define a lifting of $\ZZ$ to larger universes:

```agda
Liftℤ : Ring ℓ
Liftℤ = to-ring mr where
  open make-ring
  mr : make-ring (Lift ℓ Int)
  mr .ring-is-set = hlevel 2
  mr .1R = lift 1
  mr .0R = lift 0
  mr .-_  (lift x)          = lift (negℤ x)
  mr ._+_ (lift x) (lift y) = lift (x +ℤ y)
  mr ._*_ (lift x) (lift y) = lift (x *ℤ y)
```

<!--
```agda
  mr .*-idl      (lift x)                   = ap lift $ *ℤ-onel x
  mr .*-idr      (lift x)                   = ap lift $ *ℤ-oner x
  mr .+-idl      (lift x)                   = ap lift $ +ℤ-zerol x
  mr .+-invr     (lift x)                   = ap lift $ +ℤ-invr x
  mr .+-comm     (lift x) (lift y)          = ap lift $ +ℤ-commutative x y
  mr .+-assoc    (lift x) (lift y) (lift z) = ap lift $ +ℤ-assoc x y z
  mr .*-assoc    (lift x) (lift y) (lift z) = ap lift $ *ℤ-associative x y z
  mr .*-distribl (lift x) (lift y) (lift z) = ap lift $ *ℤ-distribl x y z
  mr .*-distribr (lift x) (lift y) (lift z) = ap lift $ *ℤ-distribr x y z
```
-->

With that set up out of the way, we can now proceed to the _actual_
theorem we're interested in: For a ring $R$, there is a contractible
space of homomorphisms $\ZZ \to R$. The definition of this construction
is _fairly_ involved, as algebra tends to be, so let's see it in parts:
The first thing we must do is write a procedure to turn natural numbers
into elements of $R$. There's really only one choice^[though the fact
that there's only one choice is sorta the theorem we are trying to
prove...], so here it is:

```agda
Int-is-initial : is-initial (Rings ℓ) Liftℤ
Int-is-initial R = contr z→r λ x → ext (lemma x) where
  module R = Kit R
```

Note that we treat 1 with care: we could have this map 1 to `1r + 0r`,
but this results in worse definitional behaviour when actually using the
embedding. This will result in a bit more work right now, but is work
worth doing.

```agda
  e : Nat → ⌞ R ⌟
  e zero          = R.0r
  e (suc zero)    = R.1r
  e (suc (suc x)) = R.1r R.+ e (suc x)
```

Zero gets sent to zero, and "adding one" gets sent to adding one. Is
anyone surprised? I know I'm not. Anyway, this operation is a semiring
homomorphism from the natural numbers to $R$, i.e., it sends sums of
naturals to sums in $R$, and products of naturals to products in $R$.
We'll need this later.

```agda
  e-suc : ∀ n → e (suc n) ≡ R.1r R.+ e n
  e-add : ∀ m n → e (m Nat.+ n) ≡ e m R.+ e n
  e-mul : ∀ m n → e (m Nat.* n) ≡ e m R.* e n
```

<!--
```agda
  e-suc zero = sym R.+-idr
  e-suc (suc n) = refl

  e-add zero n = sym R.+-idl
  e-add (suc m) n =
    e (suc m Nat.+ n)      ≡⟨ e-suc (m Nat.+ n) ⟩
    R.1r R.+ e (m Nat.+ n) ≡⟨ ap (R.1r R.+_) (e-add m n) ⟩
    R.1r R.+ (e m R.+ e n) ≡⟨ R.+-associative ⟩
    (R.1r R.+ e m) R.+ e n ≡˘⟨ ap (R._+ e n) (e-suc m) ⟩
    e (suc m) R.+ e n ∎

  e-mul zero n = sym R.*-zerol
  e-mul (suc m) n =
    e (suc m Nat.* n)            ≡⟨ e-add n (m Nat.* n) ⟩
    e n R.+ e (m Nat.* n)        ≡⟨ ap (e n R.+_) (e-mul m n) ⟩
    e n R.+ e m R.* e n          ≡˘⟨ ap (R._+ (e m R.* e n)) R.*-idl ⟩
    R.1r R.* e n R.+ e m R.* e n ≡˘⟨ R.*-distribr ⟩
    (R.1r R.+ e m) R.* e n       ≡˘⟨ ap (R._* e n) (e-suc m) ⟩
    (e (suc m) R.* e n) ∎
```
-->

The last thing we need is a little lemma that will be used in showing
that our embedding $e : \NN \mono R$ extends to a function $f : \ZZ \to
R$: We want to define $f$ by sending $[a - b]$ to $e(a) - e(b)$, meaning
that $e$ must respect the path constructor used in the definition of
integers, i.e. we need $e(m) - e(n) = e(1 + m) - e(1 + n)$. This is
annoying to show, but not _too_ annoying:

```agda
  e-tr : ∀ m n → e m R.- e n ≡ e (suc m) R.- e (suc n)
  e-tr m n = sym $
    (e (suc m) R.- e (suc n))                   ≡⟨ ap₂ R._-_ (e-suc m) (e-suc n) ⟩
    (R.1r R.+ e m) R.- (R.1r R.+ e n)           ≡⟨ ap₂ R._+_ refl (R.a.inv-comm ∙ R.+-commutes) ∙ R.+-associative ⟩
    R.1r R.+ e m R.+ (R.- R.1r) R.+ (R.- e n)   ≡⟨ ap₂ R._+_ (R.pullr R.+-commutes ∙ R.pulll refl) refl ⟩
    R.1r R.+ (R.- R.1r) R.+ e m R.+ (R.- e n)   ≡⟨ ap₂ R._+_ (R.eliml R.+-invr) refl ⟩
    e m R.- e n                                 ∎
```

We can now build the embedding $\ZZ \mono R$. It remains to show that
this is a ring homomorphism... which involves a mountain of annoying
algebra, so I won't comment on it too much: it can be worked out on
paper, following the ring laws.

```agda
  ℤ↪R : Int → ⌞ R ⌟
  ℤ↪R (pos x) = e x
  ℤ↪R (negsuc x) = R.- (e (suc x))

  open is-ring-hom

  z-nat-diff : ∀ x y → ℤ↪R (x ℕ- y) ≡ e x R.- e y
  z-nat-diff x zero = R.intror R.inv-unit
  z-nat-diff zero (suc y) = R.introl refl
  z-nat-diff (suc x) (suc y) = z-nat-diff x y ∙ e-tr x y

  z-add : ∀ x y → ℤ↪R (x +ℤ y) ≡ ℤ↪R x R.+ ℤ↪R y
  z-add (pos x) (pos y) = e-add x y
  z-add (pos x) (negsuc y) = z-nat-diff x (suc y)
  z-add (negsuc x) (pos y) = z-nat-diff y (suc x) ∙ R.+-commutes
  z-add (negsuc x) (negsuc y) =
    R.- (e 1 R.+ e (suc x Nat.+ y))         ≡⟨ ap R.-_ (ap₂ R._+_ refl (e-add (suc x) y) ∙ R.extendl R.+-commutes) ⟩
    R.- (e (suc x) R.+ (e 1 R.+ e y))       ≡⟨ R.a.inv-comm ⟩
    (R.- (e 1 R.+ e y)) R.+ (R.- e (suc x)) ≡⟨ R.+-commutes ⟩
    (R.- e (suc x)) R.+ (R.- (e 1 R.+ e y)) ≡⟨ ap₂ R._+_ refl (ap R.-_ (sym (e-add 1 y))) ⟩
    (R.- e (suc x)) R.+ (R.- e (1 Nat.+ y)) ∎

  z-mul : ∀ x y → ℤ↪R (x *ℤ y) ≡ ℤ↪R x R.* ℤ↪R y
  z-mul (pos x) (pos y) =
    ℤ↪R (assign pos (x Nat.* y)) ≡⟨ ap ℤ↪R (assign-pos (x Nat.* y)) ⟩
    e (x Nat.* y)                ≡⟨ e-mul x y ⟩
    (e x R.* e y)                ∎
  z-mul (posz) (negsuc y) = sym R.*-zerol
  z-mul (possuc x) (negsuc y) =
    R.- e (suc x Nat.* suc y)     ≡⟨ ap R.-_ (e-mul (suc x) (suc y)) ⟩
    R.- (e (suc x) R.* e (suc y)) ≡˘⟨ R.*-negater ⟩
    e (suc x) R.* (R.- e (suc y)) ∎
  z-mul (negsuc x) (posz) =
    ℤ↪R (assign neg (x Nat.* 0)) ≡⟨ ap ℤ↪R (ap (assign neg) (Nat.*-zeror x)) ⟩
    ℤ↪R 0                        ≡⟨ sym R.*-zeror ⟩
    ℤ↪R (negsuc x) R.* R.0r      ∎
  z-mul (negsuc x) (possuc y) =
    R.- e (suc x Nat.* suc y)     ≡⟨ ap R.-_ (e-mul (suc x) (suc y)) ⟩
    R.- (e (suc x) R.* e (suc y)) ≡⟨ sym R.*-negatel ⟩
    (R.- e (suc x)) R.* e (suc y) ∎
  z-mul (negsuc x) (negsuc y) =
    e (suc x Nat.* suc y)               ≡⟨ e-mul (suc x) (suc y) ⟩
    e (suc x) R.* e (suc y)             ≡˘⟨ R.inv-inv ⟩
    R.- (R.- (e (suc x) R.* e (suc y))) ≡˘⟨ ap R.-_ R.*-negater ⟩
    R.- (e (suc x) R.* ℤ↪R (negsuc y))  ≡˘⟨ R.*-negatel ⟩
    ℤ↪R (negsuc x) R.* ℤ↪R (negsuc y)   ∎

  z→r : Rings.Hom Liftℤ R
  z→r .fst (lift x) = ℤ↪R x
  z→r .snd .pres-id = refl
  z→r .snd .pres-+ (lift x) (lift y) = z-add x y
  z→r .snd .pres-* (lift x) (lift y) = z-mul x y
```

The last thing we must show is that this is the _unique_ ring
homomorphism from the integers to $R$. This, again, is slightly
indirect: We know for a fact that, if we have some _other_ homomorphism
$f : \ZZ \to R$, then it must enjoy $f(1) = 1$, just as our chosen
embedding does.  Now, no matter how trivial this coming observation may
seem, do not brush it aside: The integer $n$ is the sum of $n$ copies of
the number 1. This is actually precisely what we need to establish the
result! That's because we have

$$
f(n) = f(1 + \cdots + 1) = f(1) + \cdots + f(1) = 1 + \cdots + 1
$$,

and that last expression is pretty exactly what our canonical map
evaluates to on $n$. So we're done!

```agda
  module _ (f : Rings.Hom Liftℤ R) where
    private module f = is-ring-hom (f .snd)

    f-pos : ∀ x → e x ≡ f · lift (pos x)
    f-pos zero = sym f.pres-0
    f-pos (suc x) = e-suc x ∙ sym (f.pres-+ (lift 1) (lift (pos x)) ∙ ap₂ R._+_ f.pres-id (sym (f-pos x)))

    lemma : (i : Int) → z→r · lift i ≡ f · lift i
    lemma (pos x) = f-pos x
    lemma (negsuc x) = sym (f.pres-neg {lift (possuc x)} ∙ ap R.-_ (sym (f-pos (suc x))))
```
