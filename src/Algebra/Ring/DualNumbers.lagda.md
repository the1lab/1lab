<!--
```agda
open import 1Lab.Prelude hiding (_*_ ; _+_ ; _-_)

open import Algebra.Ring.Commutative
open import Algebra.Ring.Solver
open import Algebra.Ring

open import Cat.Displayed.Total

import Cat.Reasoning
```
-->

```agda
module Algebra.Ring.DualNumbers {ℓ} (R : CRing ℓ) where
```

<!--
```agda
private
  module R = CRing-on (R .snd)
  module CR = Cat.Reasoning (CRings ℓ)

open make-ring
open is-ring-hom
```
-->

# The ring of dual numbers {defines="dual-numbers"}

The **dual numbers** over a commutative [[ring]] $R$ are the
commutative $R$-algebra $R[\epsilon] := R[x]/(x^2)$: the "smallest"
extension of $R$ by a formally infinitesimal quantity, one whose
square — and every higher power — simply *is* zero. Physicists'
computations that keep terms "to first order in $\epsilon$" are exact
computations in $R[\epsilon]$, and probing spaces by the formal dual
of $R[\epsilon]$ is what makes the naive infinitesimal reasoning of
variational calculus rigorous, in the tradition of synthetic
differential geometry.

Because the quotient is by such a tame relation, no quotient is
needed: $R[\epsilon]$ has carrier $R \times R$, recording coefficients
$a + b\epsilon$, with multiplication truncating the $\epsilon^2$ term.
All the ring laws are decided by the [[commutative ring
solver|ring-solver]].

<!--
```agda
private abstract
  l+idl : ∀ a → R.0r R.+ a ≡ a
  l+idl a = cring! R

  l+invr : ∀ a → a R.+ (R.- a) ≡ R.0r
  l+invr a = cring! R

  l+assoc : ∀ a c e → a R.+ (c R.+ e) ≡ (a R.+ c) R.+ e
  l+assoc a c e = cring! R

  l+comm : ∀ a c → a R.+ c ≡ c R.+ a
  l+comm a c = cring! R

  l*idl : ∀ a → R.1r R.* a ≡ a
  l*idl a = cring! R

  l*idl' : ∀ a b → R.1r R.* b R.+ R.0r R.* a ≡ b
  l*idl' a b = cring! R

  l*idr : ∀ a → a R.* R.1r ≡ a
  l*idr a = cring! R

  l*idr' : ∀ a b → a R.* R.0r R.+ b R.* R.1r ≡ b
  l*idr' a b = cring! R

  l*assoc : ∀ a c e → a R.* (c R.* e) ≡ (a R.* c) R.* e
  l*assoc a c e = cring! R

  l*assoc'
    : ∀ a b c d e f
    → a R.* (c R.* f R.+ d R.* e) R.+ b R.* (c R.* e)
    ≡ (a R.* c) R.* f R.+ (a R.* d R.+ b R.* c) R.* e
  l*assoc' a b c d e f = cring! R

  l*distl : ∀ a c e → a R.* (c R.+ e) ≡ a R.* c R.+ a R.* e
  l*distl a c e = cring! R

  l*distl'
    : ∀ a b c d e f
    → a R.* (d R.+ f) R.+ b R.* (c R.+ e)
    ≡ (a R.* d R.+ b R.* c) R.+ (a R.* f R.+ b R.* e)
  l*distl' a b c d e f = cring! R

  l*distr : ∀ a c e → (c R.+ e) R.* a ≡ c R.* a R.+ e R.* a
  l*distr a c e = cring! R

  l*distr'
    : ∀ a b c d e f
    → (c R.+ e) R.* b R.+ (d R.+ f) R.* a
    ≡ (c R.* b R.+ d R.* a) R.+ (e R.* b R.+ f R.* a)
  l*distr' a b c d e f = cring! R

  l*comm : ∀ a c → a R.* c ≡ c R.* a
  l*comm a c = cring! R

  l*comm' : ∀ a b c d → a R.* d R.+ b R.* c ≡ c R.* b R.+ d R.* a
  l*comm' a b c d = cring! R

  lι+ : R.0r ≡ R.0r R.+ R.0r
  lι+ = cring! R

  lι* : ∀ a b → R.0r ≡ a R.* R.0r R.+ R.0r R.* b
  lι* a b = cring! R

  lε₁ : R.0r R.* R.0r ≡ R.0r
  lε₁ = cring! R

  lε₂ : R.0r R.* R.1r R.+ R.1r R.* R.0r ≡ R.0r
  lε₂ = cring! R
```
-->

```agda
R[ε] : CRing ℓ
R[ε] .fst = el! (⌞ R ⌟ × ⌞ R ⌟)
R[ε] .snd .CRing-on.has-ring-on = to-ring-on mk where
  mk : make-ring (⌞ R ⌟ × ⌞ R ⌟)
  mk .ring-is-set = hlevel 2
  mk .0R = R.0r , R.0r
  mk ._+_ x y = x .fst R.+ y .fst , x .snd R.+ y .snd
  mk .-_ x = R.- x .fst , R.- x .snd
  mk .+-idl (a , b) = ap₂ _,_ (l+idl a) (l+idl b)
  mk .+-invr (a , b) = ap₂ _,_ (l+invr a) (l+invr b)
  mk .+-assoc (a , b) (c , d) (e , f) = ap₂ _,_ (l+assoc a c e) (l+assoc b d f)
  mk .+-comm (a , b) (c , d) = ap₂ _,_ (l+comm a c) (l+comm b d)
  mk .1R = R.1r , R.0r
  mk ._*_ x y =
    x .fst R.* y .fst , x .fst R.* y .snd R.+ x .snd R.* y .fst
  mk .*-idl (a , b) = ap₂ _,_ (l*idl a) (l*idl' a b)
  mk .*-idr (a , b) = ap₂ _,_ (l*idr a) (l*idr' a b)
  mk .*-assoc (a , b) (c , d) (e , f) =
    ap₂ _,_ (l*assoc a c e) (l*assoc' a b c d e f)
  mk .*-distribl (a , b) (c , d) (e , f) =
    ap₂ _,_ (l*distl a c e) (l*distl' a b c d e f)
  mk .*-distribr (a , b) (c , d) (e , f) =
    ap₂ _,_ (l*distr a c e) (l*distr' a b c d e f)
R[ε] .snd .CRing-on.*-commutes {a , b} {c , d} =
  ap₂ _,_ (l*comm a c) (l*comm' a b c d)
```

<!--
```agda
private module Rε = CRing-on (R[ε] .snd)
```
-->

The infinitesimal itself is the element $\epsilon = 0 + 1\epsilon$,
and it squares to zero — the equation that in physics is an
approximation, and here is a definition.

```agda
εᴿ : ⌞ R[ε] ⌟
εᴿ = R.0r , R.1r

ε² : εᴿ Rε.* εᴿ ≡ Rε.0r
ε² = ap₂ _,_ lε₁ lε₂
```

$R[\epsilon]$ is an $R$-algebra: $R$ includes as the constants, and
there is an **augmentation** $R[\epsilon] \to R$ which forgets the
infinitesimal part — "evaluation at $\epsilon = 0$". The composite is
the identity: the constants have no infinitesimal part to forget.

```agda
ι-dual : CR.Hom R R[ε]
ι-dual .∫Hom.fst a = a , R.0r
ι-dual .∫Hom.snd .pres-id = refl
ι-dual .∫Hom.snd .pres-+ x y = ap₂ _,_ refl lι+
ι-dual .∫Hom.snd .pres-* x y = ap₂ _,_ refl (lι* x y)

aug-dual : CR.Hom R[ε] R
aug-dual .∫Hom.fst = fst
aug-dual .∫Hom.snd .pres-id = refl
aug-dual .∫Hom.snd .pres-+ x y = refl
aug-dual .∫Hom.snd .pres-* x y = refl

aug-ι : aug-dual CR.∘ ι-dual ≡ CR.id
aug-ι = ∫Hom-path _ refl prop!
```
