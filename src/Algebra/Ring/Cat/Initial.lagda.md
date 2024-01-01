<!--
```agda
open import Algebra.Ring.Module.Action
open import Algebra.Group.Ab
open import Algebra.Prelude
open import Algebra.Group
open import Algebra.Ring

open import Cat.Diagram.Initial

open import Data.Int.HIT

import Data.Nat as Nat

import Prim.Data.Nat as Nat
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
  mr .-_  (lift x)          = lift (negate x)
  mr ._+_ (lift x) (lift y) = lift (x +ℤ y)
  mr ._*_ (lift x) (lift y) = lift (x *ℤ y)
```

<!--
```agda
  mr .*-idl      {lift x}                   = ap lift $ *ℤ-idl x
  mr .*-idr      {lift x}                   = ap lift $ *ℤ-idr x
  mr .+-idl      {lift x}                   = ap lift $ +ℤ-zerol x
  mr .+-invr     {lift x}                   = ap lift $ +ℤ-inverser x
  mr .+-comm     {lift x} {lift y}          = ap lift $ +ℤ-commutative x y
  mr .+-assoc    {lift x} {lift y} {lift z} = ap lift $ +ℤ-associative x y z
  mr .*-assoc    {lift x} {lift y} {lift z} = ap lift $ *ℤ-associative x y z
  mr .*-distribl {lift x} {lift y} {lift z} = ap lift $ *ℤ-distrib-+ℤ-l x y z
  mr .*-distribr {lift x} {lift y} {lift z} = ap lift $ *ℤ-distrib-+ℤ-r x y z
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
Int-is-initial R = contr z→r λ x → Homomorphism-path λ { (lift i) → lemma x i }
  where
  module R = Ring-on (R .snd)
```

Note that we treat 1 with care: we could have this map 1 to `1r + 0r`,
but this results in worse definitional behaviour when actually using the embedding.
This will result in a bit more work right now, but is work worth doing.


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
```
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

Note that we special case `diff x 0` here for better definitional
behaviour of the embedding.

```agda

  ℤ↪R : Int → ⌞ R ⌟
  ℤ↪R (diff x zero)          = e x
  ℤ↪R (diff x (suc y))       = e x R.- e (suc y)
  ℤ↪R (Int.quot m zero i)    = along i $
    e m                     ≡⟨ R.intror R.+-invr ⟩
    e m R.+ (R.1r R.- R.1r) ≡⟨ R.+-associative ⟩
    (e m R.+ R.1r) R.- R.1r ≡⟨ ap (R._- R.1r) R.+-commutes ⟩
    (R.1r R.+ e m) R.- R.1r ≡˘⟨ ap (R._- R.1r) (e-suc m) ⟩
    e (suc m) R.- R.1r      ∎
  ℤ↪R (Int.quot m (suc n) i) = e-tr m (suc n) i

  open is-ring-hom

  ℤ↪R-diff : ∀ m n → ℤ↪R (diff m n) ≡ e m R.- e n
  ℤ↪R-diff m zero = R.intror R.inv-unit
  ℤ↪R-diff m (suc n) = refl

  z→r : Rings.Hom Liftℤ R
  z→r .hom (lift x) = ℤ↪R x
```
<!--
```agda
  z→r .preserves .pres-id = refl
  z→r .preserves .pres-+ (lift x) (lift y) =
    Int-elim₂-prop {P = λ x y → ℤ↪R (x +ℤ y) ≡ ℤ↪R x R.+ ℤ↪R y}
      (λ _ _ → hlevel 1)
      pf
      x y
      where abstract
        pf : ∀ a b x y → ℤ↪R (diff (a Nat.+ x) (b Nat.+ y)) ≡ (ℤ↪R (diff a b)) R.+ (ℤ↪R (diff x y))
        pf a b x y =
          ℤ↪R (diff (a Nat.+ x) (b Nat.+ y))    ≡⟨ ℤ↪R-diff (a Nat.+ x) (b Nat.+ y) ⟩
          e (a Nat.+ x) R.- e (b Nat.+ y)       ≡⟨ ap₂ R._-_ (e-add a x) (e-add b y) ⟩
          (e a R.+ e x) R.- (e b R.+ e y)       ≡⟨ ap₂ R._+_ refl (R.inv-comm ∙ R.+-commutes) ⟩
          (e a R.+ e x) R.+ ((R.- e b) R.- e y) ≡⟨ R.extendl (R.extendr R.+-commutes) ⟩
          (e a R.- e b) R.+ (e x R.- e y)       ≡˘⟨ ap₂ R._+_ (ℤ↪R-diff a b) (ℤ↪R-diff x y) ⟩
          ℤ↪R (diff a b) R.+ ℤ↪R (diff x y)     ∎
  z→r .preserves .pres-* (lift x) (lift y) =
    Int-elim₂-prop {P = λ x y → ℤ↪R (x *ℤ y) ≡ ℤ↪R x R.* ℤ↪R y}
      (λ _ _ → hlevel 1)
      pf
      x y
    where abstract
      swizzle : ∀ a b x y
                → (a R.- b) R.* (x R.- y)
                ≡ (a R.* x R.+ b R.* y) R.- (a R.* y R.+ b R.* x)
      swizzle a b x y =
        (a R.- b) R.* (x R.- y)                                                       ≡⟨ R.*-distribl ⟩
        ((a R.- b) R.* x) R.+ ((a R.- b) R.* (R.- y))                                 ≡⟨ ap₂ R._+_ refl (sym R.neg-*-r) ⟩
        ((a R.- b) R.* x) R.- ((a R.- b) R.* y)                                       ≡⟨ ap₂ R._-_ R.*-distribr R.*-distribr ⟩
        (a R.* x R.+ (R.- b) R.* x) R.- (a R.* y R.+ (R.- b) R.* y)                   ≡⟨ ap₂ R._+_ refl (R.a.inv-comm ∙ R.+-commutes) ⟩
        (a R.* x R.+ (R.- b) R.* x) R.+ ((R.- (a R.* y)) R.+ ⌜ R.- ((R.- b) R.* y) ⌝) ≡⟨ ap! (ap R.a._⁻¹ (sym R.neg-*-l) ∙ R.a.inv-inv) ⟩
        (a R.* x R.+ (R.- b) R.* x) R.+ ((R.- (a R.* y)) R.+ (b R.* y))               ≡⟨ R.pulll (R.extendr R.+-commutes) ⟩
        (a R.* x) R.+ (R.- (a R.* y)) R.+ ((R.- b) R.* x) R.+ (b R.* y)               ≡⟨ R.pullr R.+-commutes ·· R.extendl (R.pullr R.+-commutes) ·· R.pulll (R.pulll refl) ∙ R.pullr (ap₂ R._+_ refl (sym R.neg-*-l) ·· sym R.a.inv-comm ·· ap R.a._⁻¹ R.+-commutes) ⟩
        (a R.* x R.+ b R.* y) R.- (a R.* y R.+ b R.* x)                               ∎

      pf : ∀ a b x y → ℤ↪R (diff a b *ℤ diff x y) ≡ (ℤ↪R (diff a b) R.* ℤ↪R (diff x y))
      pf a b x y =
        ℤ↪R (diff (a Nat.* x Nat.+ b Nat.* y) (a Nat.* y Nat.+ b Nat.* x))      ≡⟨ ℤ↪R-diff (a Nat.* x Nat.+ b Nat.* y) (a Nat.* y Nat.+ b Nat.* x) ⟩
        e (a Nat.* x Nat.+ b Nat.* y) R.- e (a Nat.* y Nat.+ b Nat.* x)         ≡⟨ ap₂ R._-_ (e-add (a Nat.* x) (b Nat.* y)) (e-add (a Nat.* y) (b Nat.* x)) ⟩
        (e (a Nat.* x) R.+ e (b Nat.* y)) R.- (e (a Nat.* y) R.+ e (b Nat.* x)) ≡⟨ ap₂ R._-_ (ap₂ R._+_ (e-mul a x) (e-mul b y)) (ap₂ R._+_ (e-mul a y) (e-mul b x)) ⟩
        ((e a R.* e x) R.+ (e b R.* e y)) R.- ((e a R.* e y) R.+ (e b R.* e x)) ≡˘⟨ swizzle (e a) (e b) (e x) (e y) ⟩
        (e a R.- e b) R.* (e x R.- e y)                                         ≡˘⟨ ap₂ R._*_ (ℤ↪R-diff a b) (ℤ↪R-diff x y) ⟩
        ℤ↪R (diff a b) R.* ℤ↪R (diff x y) ∎

```
-->

The last thing we must show is that this is the _unique_ ring
homomorphism from the integers to $R$. This, again, is slightly
indirect: We know for a fact that, if we have some _other_ homomorphism
$f : \ZZ \to R$, then it must enjoy $f(1) = 1$, just as our chosen
embedding does.  Now, no matter how trivial this coming observation may
seem, do not brush it aside: The integer $n$ is the sum of $n$ copies of
the number 1. This is actually precisely what we need to establish the
result! That's because we have

$$
f(n) = f(1 + \cdots + 1) = f(1) + \cdots + f(1) = 1 + \cdots + 1\text{,}
$$

and that last expression is pretty exactly what our canonical map
evaluates to on $n$. So we're done!

```agda
  lemma : ∀ (f : Rings.Hom Liftℤ R) i → z→r # lift i ≡ f # lift i
  lemma f =
    Int-elim-prop (λ _ → hlevel 1) λ a b → sym $
      f # lift (diff a b)                         ≡⟨ ap (f #_) (ap lift (p a b)) ⟩
      f # lift (diff a 0 +ℤ diff 0 b)             ≡⟨ f .preserves .pres-+ (lift (diff a 0)) (lift (diff 0 b)) ⟩
      f # lift (diff a 0) R.+ f # lift (diff 0 b) ≡⟨ ap₂ R._+_ (q a) (is-group-hom.pres-inv gh {x = lift (diff b 0)} ∙ ap R.-_ (q b)) ⟩
      (e a) R.+ (R.- e b)                         ≡˘⟨ ℤ↪R-diff a b ⟩
      z→r # lift (diff a b)                       ∎
    where
      p : ∀ a b → diff a b ≡ diff a 0 +ℤ diff 0 b
      p a b = ap (λ e → diff e b) (sym (Nat.+-zeror a))

      gh : is-group-hom
            (Ring-on.additive-group (Liftℤ .snd) .snd)
            (Ring-on.additive-group (R .snd) .snd)
            _
      gh = record { pres-⋆ = f .preserves .pres-+ }

      q : ∀ a → f # lift (diff a 0) ≡ e a
      q zero = is-group-hom.pres-id gh
      q (suc n) =
        f # lift (diff (suc n) 0)          ≡⟨ f .preserves .pres-+ (lift (diff 1 0)) (lift (diff n 0)) ⟩
        f # lift 1 R.+ f # lift (diff n 0) ≡⟨ ap₂ R._+_ (f .preserves .pres-id) (q n) ⟩
        R.1r R.+ (e n)                     ≡˘⟨ e-suc n ⟩
        e (suc n) ∎
```

## Abelian groups as Z-modules

A fun consequence of $\ZZ$ being the initial ring is that every
[[abelian group]] admits a unique $\ZZ$-module structure. This is, if
you ask me, rather amazing! The correspondence is as follows: Because of
the delooping-endomorphism ring adjunction, we have a correspondence
between "$R$-module structures on G" and "ring homomorphisms $R \to
\rm{Endo}(G)$" --- and since the latter is contractible, so is the
former!

```agda
ℤ-module-unique : ∀ (G : Abelian-group ℓ) → is-contr (Ring-action Liftℤ (G .snd))
ℤ-module-unique G = is-hlevel≃ 0 (Action≃Hom Liftℤ G) (Int-is-initial _)
```
