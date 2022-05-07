```agda
module Data.Nat.Solver where

open import 1Lab.Type
open import 1Lab.Path
open import Data.Nat.Base
open import Data.Nat.Properties
open import Data.Fin.Base
open import Data.Bool

open import 1Lab.Reflection
open import 1Lab.Reflection.Variables
```

# The Nat Solver

This module defines a solver for equations in commutative semiring
of natural numbers. This module can be split up into 3 clean parts:
- Horner normal forms for polynomials
- Evaluation of reflected terms into polynomials
- The reflection interface

## Horner Normal Forms

If we ignore the `suc`{.Agda} and `zero`{.Agda} constructors and their
respective equations, the core problem at hand is trying to compute
normal forms for polynomials. Luckily, like most problems involving polynomials,
this has been thoroughly studied! There are many possible normal forms to choose
from, but the most useful for our task is *Horner Normal Form*, as it admits a
particularly nice inductive characterization.

The core idea is that we can rewrite a (univariate) polynomial of the form
$$ a_0 + a_1 x + a_2 x^2 + a_3 x^3 + \cdots + a_n x^n $$
into the following form:
$$ a_0 + x ( a_1 + x ( a_2 + x ( a_3 + \cdots + x ( a_{n-1} + x a_n ) ) ) ) $$

However, we need /multivariate/ polynomials, not just univariate! To do this,
we can exploit the isomorphism between $A[X_0, \cdots, X_n]$ and
$A[X_0][X_1]\cdots[X_n]$. This allows us to define the normal form of a 
multivariate polynomial as (essentially) a product of univariate ones.

We start by defining the type of n-ary multivariate polynomials.
```agda
data Poly {a} (A : Type a) : Nat → Type a where
```
The first polynomial we define is the constant polynomial $c \in A[X_0]$.
```agda
  const : (c : A) → Poly A 0
```
Next, we define the 0 polynomial $0 \in A[X_0, \cdots, X_n]$. Note that
we do /not/ include $A[X_0]$ here! This is important for ensuring that our
datatype defines a (somewhat) /unique/ normal form.
If we had instead chosen `Poly A (suc n)`, we could represent the 0 polynomial by
both `const 0` and `zerop`, which complicates matters somewhat.
```agda
  zerop  : ∀ {n} → Poly A (suc n)
```
Finally, we define both addition, multiplication by $X_0$ in one fell swoop.
This constructor represents the polynomial $p * X_0 + q$, where
$p \in A[X_0]\cdots[X_n]$, and $q \in A[X_1]\cdots[X_n]$.

This flipping of the index may seem confusing at first, but it serves an
important purpose: it makes evaluation /really/ easy! When evaluating,
we will need some environment `Vec A n` to be able to provide values for
the various $X_i$. When encountering this case, the index will ensure that
we have a `_∷_` constructor, at which point we can use the tail of the
vector to evaluate `q`! In this sense, not only does this constructor handle
additiona and multiplication by $X_0$, it _also_ handles weakening.
```agda
  _*X+_ : ∀ {n} → (p : Poly A (suc n)) → (q : Poly A n) → Poly A (suc n) 
```

<!--
```
infixl 2 _*X+_

private variable
  a : Level
  A : Type a
  n : Nat

lookup : Vec A n → Fin n → A
lookup (x ∷ xs) fzero = x
lookup (x ∷ xs) (fsuc i) = lookup xs i

-- NOTE: These little helper lemmas become very useful, and make
-- some of the really involved proofs a lot less painful.
commute-inner : ∀ w x y z → (w + x) + (y + z) ≡ (w + y) + (x + z)
commute-inner w x y z =
  (w + x) + (y + z) ≡⟨ +-associative w x (y + z) ⟩
  w + (x + (y + z)) ≡˘⟨ ap (w +_) (+-associative x y z) ⟩
  w + ((x + y) + z) ≡⟨ ap (λ ϕ → w + (ϕ + z)) (+-commutative x y) ⟩
  w + (y + x + z)   ≡⟨ ap (w +_) (+-associative y x z) ⟩
  w + (y + (x + z)) ≡˘⟨  +-associative w y (x + z) ⟩
  (w + y) + (x + z) ∎

commute-last : ∀ x y z → (x * y) * z ≡ (x * z) * y
commute-last x y z =
  x * y * z   ≡⟨ *-associative x y z ⟩
  x * (y * z) ≡⟨ ap (x *_) (*-commutative y z) ⟩
  x * (z * y) ≡˘⟨ *-associative x z y ⟩
  x * z * y ∎
```
-->

Note that this representation, while convienent, does pose some problems.
We pay for the (relative) uniqueness by having larger terms: For instance, the
polynomial $X^4 + 1$ is represented as so:

```agda
private
  x⁴+1 : Poly Nat 1
  x⁴+1 = zerop *X+ (const 1) *X+ const 0 *X+ (const 0) *X+ (const 0) *X+ (const 0)
```

This could be alieviated by using a *sparse* representation, but this is decidedly
more difficult. As the Nat Solver is not expected to deal with polynomials with
large degrees, this term blow up is not anticipated to be a problem in practice.

### Operations on Horner Normal Forms

Now, let's define a handful of functions for constructing and combining polynomials.
The naming here can get a bit confusion, so let's stick with the convention
of adding a subscript 'p' to denote an operation on polynomials. As a further note,
all of the following section could be generalized to an arbitrary semiring, but
this would complicate the dependency graph somewhat, so we stick to natural
numbers.

As previously mentioned, we have different representations of the 0
polynomial depending on if we are working with `Poly A zero` or `Poly A (suc n)`.
This is somewhat annoying, so we define a small helper for picking the correct
representation.

```agda
0ₚ : Poly Nat n
0ₚ {n = zero} = const zero
0ₚ {n = suc n} = zerop
```

While we are at it, we also define the polynomial that represents the constant
polynomial $c \in A[X_0]\cdots[X_n]$.

```agda
constₚ : Nat → Poly Nat n
constₚ {n = zero}  c = const c
constₚ {n = suc n} c = 0ₚ *X+ constₚ c
```

The constant 1 is important enough that it deserves it's own syntax.
```agda
1ₚ : Poly Nat n
1ₚ = constₚ 1
```

We also define the identity monomials $X_i \in A[X_0]\cdots[X_n]$.

```agda
X[_] : Fin n → Poly Nat n
X[_] fzero = 1ₚ *X+ 0ₚ
X[_] (fsuc i) = 0ₚ *X+ X[ i ]
```

Now, onto addition of polynomials. This is more or less what one would expect
if they wrote out the polynomials and did the addition by hand.

```agda
infixl 6 _+ₚ_
infixl 7 _*ₚ_

_+ₚ_ : Poly Nat n → Poly Nat n → Poly Nat n
const c₁ +ₚ const c₂ = const (c₁ + c₂)
zerop +ₚ q = q
(p *X+ q) +ₚ zerop = p *X+ q
(p *X+ r) +ₚ (q *X+ s) = (p +ₚ q) *X+ (r +ₚ s)
```

Multiplication, however, is somewhat more tricky. The problem is that during
the course of recursion, we will need to multiply a `Poly A n` by a `Poly A (suc n)`.
This ends up being mutually recursive, so let's predeclare their types.
```agda
_*ₚ_ : Poly Nat n → Poly Nat n → Poly Nat n
_*ₚ′_ : Poly Nat n → Poly Nat (suc n) → Poly Nat (suc n)
```

First, the homogenous multiplication. The first two cases are pretty straightforward,
but the final one is decidedly less so. To start, we can distribute the multiplication
of `r` across the `+`, invoking `_+ₚ_`{.Agda} to add the results together. When multiplying
`q` and `r`, we need to use the aforementioned heterogeneous multiplication, as 
$q \in A[X_1]\cdots[X_n]$. When multiplying `p` and `r`, we need to add on a 
`0ₚ` under the `*X`, as this is the only way of multiplying by $X_0$.

```agda
const c₁ *ₚ const c₂ = const (c₁ * c₂)
zerop *ₚ q = zerop
(p *X+ q) *ₚ r = ((p *ₚ r) *X+ 0ₚ) +ₚ (q *ₚ′ r)
```

For the heterogeneous case, the recursion is somewhat more simple.

```agda
r *ₚ′ zerop = zerop 
r *ₚ′ (p *X+ q) = (r *ₚ′ p) *X+ (r *ₚ q)
```

### Evaluation of Horner Normal Forms

Multivariate polynomials represent functions $A^n \to A$, so we should be able
to interpret them as such. Luckily, Horner Normal Forms are extremely easy to
evaluate. As a historical note, this is why this representation was created in first
place! In this light, they should probably be called
"Sharaf al-Din al-Tusi Normal Forms".

```agda
block : Nat → Nat
block x = x
```

```agda
⟦_⟧ₚ : Poly Nat n → Vec Nat n → Nat
⟦ const c ⟧ₚ env = c
⟦ zerop ⟧ₚ env = 0
⟦ p *X+ q ⟧ₚ (x₀ ∷ env) = ⟦ p ⟧ₚ (x₀ ∷ env) * x₀ + ⟦ q ⟧ₚ env 
```

### Soundness of the Operations

Now, it's important that the operations we defined actually denote the correct
operations on natural numbers.

As a warm up, let's show that the zero polynomial really represents
the function $f(x_0, \cdots, x_n) = 0$.

```agda
sound-0ₚ : ∀ (env : Vec Nat n) → ⟦ 0ₚ ⟧ₚ env ≡ 0
sound-0ₚ [] = refl
sound-0ₚ (x ∷ env) = refl
```

We do the same for the constant polynomial.

```agda
sound-constₚ : ∀ c → (env : Vec Nat n) → ⟦ constₚ c ⟧ₚ env ≡ c
sound-constₚ c [] = refl
sound-constₚ c (x ∷ env) = sound-constₚ c env
```

At the risk o

f repeating myself, we also show the same for the monomial $X_i$.

```agda
sound-X[_] : ∀ i → (env : Vec Nat n) → ⟦ X[ i ] ⟧ₚ env ≡ lookup env i
sound-X[ fzero ] (x₀ ∷ env) =
  ⟦ constₚ 1 ⟧ₚ env * x₀ + ⟦ 0ₚ ⟧ₚ env ≡⟨ ap₂ (λ ϕ ψ → ϕ * x₀ + ψ) (sound-constₚ 1 env) (sound-0ₚ env) ⟩
  1 * x₀ + 0                           ≡⟨ +-zeror (1 * x₀) ⟩
  1 * x₀                               ≡⟨ *-onel x₀ ⟩
  x₀ ∎
sound-X[ fsuc i ] (_ ∷ env) = sound-X[ i ] env
```

Now, for something more involved: let's show that addition of polynomials really
deserves the name addition.

```agda
sound-+ₚ : ∀ p q → (env : Vec Nat n)
           → ⟦ p +ₚ q ⟧ₚ env ≡ ⟦ p ⟧ₚ env + ⟦ q ⟧ₚ env
sound-+ₚ (const c1) (const c2) env = refl
sound-+ₚ zerop q env = refl
sound-+ₚ (p *X+ r) zerop env =
  sym (+-zeror (⟦ (p *X+ r) +ₚ zerop ⟧ₚ env))
sound-+ₚ (p *X+ r) (q *X+ s) (x₀ ∷ env) =
  ⟦p+q⟧ * x₀ + ⟦r+s⟧                ≡⟨ ap₂ (λ ϕ ψ → ϕ * x₀ + ψ) (sound-+ₚ p q (x₀ ∷ env)) (sound-+ₚ r s env) ⟩
  (⟦p⟧ + ⟦q⟧) * x₀ + (⟦r⟧ + ⟦s⟧)    ≡⟨ ap (λ ϕ → ϕ + (⟦r⟧ + ⟦s⟧)) (*-distrib-+r ⟦p⟧ ⟦q⟧ x₀) ⟩
  ⟦p⟧ * x₀ + ⟦q⟧ * x₀ + (⟦r⟧ + ⟦s⟧) ≡⟨ commute-inner (⟦p⟧ * x₀) (⟦q⟧ * x₀) ⟦r⟧ ⟦s⟧ ⟩
  ⟦p⟧ * x₀ + ⟦r⟧ + (⟦q⟧ * x₀ + ⟦s⟧) ∎
  where
    ⟦p+q⟧ = ⟦ p +ₚ q ⟧ₚ (x₀ ∷ env)
    ⟦r+s⟧ = ⟦ r +ₚ s ⟧ₚ env
    ⟦p⟧ = ⟦ p ⟧ₚ (x₀ ∷ env)
    ⟦r⟧ = ⟦ r ⟧ₚ env
    ⟦q⟧ = ⟦ q ⟧ₚ (x₀ ∷ env)
    ⟦s⟧ = ⟦ s ⟧ₚ env
```

Wow, that was a bit painful! This is a somewhat common theme when writing proof
automation: it distills down a lot of the annoying proofs we need to write across
the entire codebase into one _extremely_ painful proof. Thus, convervation of
frustration is preserved.

Philisophical reflections aside, let's move onto multiplication of polynomials.
As the homogenous and heterogeneous multiplication were defined in a mutual recursive
manner, we must do so for their proofs as well.

```agda
sound-*ₚ : ∀ p q → (env : Vec Nat n)
           → ⟦ p *ₚ q ⟧ₚ env ≡ ⟦ p ⟧ₚ env * ⟦ q ⟧ₚ env
sound-*ₚ′ : ∀ p q → (x₀ : Nat) → (env : Vec Nat n)
            → ⟦ p *ₚ′ q ⟧ₚ (x₀ ∷ env) ≡ ⟦ p ⟧ₚ env * ⟦ q ⟧ₚ (x₀ ∷ env)
```

The first couple of cases of homogenous multiplication don't look so bad...

```agda
sound-*ₚ (const c1) (const c2) env = refl
sound-*ₚ zerop q env = refl
sound-*ₚ (p *X+ r) zerop (x₀ ∷ env) =
  ⟦ p *ₚ zerop ⟧ₚ (x₀ ∷ env) * x₀ + ⟦ 0ₚ ⟧ₚ env ≡⟨ ap₂ (λ ϕ ψ → ϕ * x₀ + ψ) (sound-*ₚ p zerop (x₀ ∷ env)) (sound-0ₚ env) ⟩
  ⟦p⟧ * 0 * x₀ + 0                              ≡⟨ ap (λ ϕ → (ϕ * x₀) + 0) (*-zeror ⟦p⟧) ⟩
  0                                             ≡˘⟨ *-zeror (⟦p⟧ * x₀ + ⟦r⟧) ⟩
  (⟦p⟧ * x₀ + ⟦r⟧) * 0 ∎
  where
    ⟦p⟧ = ⟦ p ⟧ₚ (x₀ ∷ env)
    ⟦r⟧ = ⟦ r ⟧ₚ env
```

However, the case where we need to distribute is not so easy. The consists of
repeatedly expanding out the polynomial operations into those on natural numbers,
then doing a brutal bit of symbol shuffling. There's not too much to be gained
from dwelling on this, so let's move on.

```agda
sound-*ₚ (p *X+ r) (q *X+ s) (x₀ ∷ env) =
  ⟦p*⟨qx+s⟩+r*q⟧ * x₀ + ⟦ 0ₚ +ₚ (r *ₚ s) ⟧ₚ env                ≡⟨ ap (λ ϕ → ⟦p*⟨qx+s⟩+r*q⟧ * x₀ + ϕ) (sound-+ₚ 0ₚ (r *ₚ s) env) ⟩
  ⟦p*⟨qx+s⟩+r*q⟧ * x₀ + (⟦ 0ₚ ⟧ₚ env + ⟦ r *ₚ s ⟧ₚ env)        ≡⟨ ap₂ (λ ϕ ψ → ⟦p*⟨qx+s⟩+r*q⟧ * x₀ + (ϕ + ψ)) (sound-0ₚ env) (sound-*ₚ r s env) ⟩
  ⟦p*⟨qx+s⟩+r*q⟧ * x₀ + (⟦r⟧ * ⟦s⟧)                            ≡⟨ ap (λ ϕ → ϕ * x₀ + ⟦r⟧ * ⟦s⟧) (sound-+ₚ (p *ₚ (q *X+ s)) (r *ₚ′ q) (x₀ ∷ env)) ⟩
  (⟦p*⟨qx+s⟩⟧ + ⟦r*q⟧) * x₀ + ⟦r⟧ * ⟦s⟧                        ≡⟨ ap₂ (λ ϕ ψ → (ϕ + ψ) * x₀ + ⟦r⟧ * ⟦s⟧) (sound-*ₚ p (q *X+ s) (x₀ ∷ env)) (sound-*ₚ′ r q x₀ env) ⟩
  (⟦p⟧ * (⟦q⟧ * x₀ + ⟦s⟧) + ⟦r⟧ * ⟦q⟧) * x₀ + ⟦r⟧ * ⟦s⟧        ≡⟨ ap (λ ϕ → ϕ + ⟦r⟧ * ⟦s⟧) (*-distrib-+r (⟦p⟧ * (⟦q⟧ * x₀ + ⟦s⟧)) (⟦r⟧ * ⟦q⟧) x₀) ⟩
  ⟦p⟧ * (⟦q⟧ * x₀ + ⟦s⟧) * x₀ + ⟦r⟧ * ⟦q⟧ * x₀ + ⟦r⟧ * ⟦s⟧     ≡⟨ +-associative (⟦p⟧ * (⟦q⟧ * x₀ + ⟦s⟧) * x₀) (⟦r⟧ * ⟦q⟧ * x₀) (⟦r⟧ * ⟦s⟧) ⟩
  ⟦p⟧ * (⟦q⟧ * x₀ + ⟦s⟧) * x₀ + (⟦r⟧ * ⟦q⟧ * x₀ + ⟦r⟧ * ⟦s⟧)   ≡⟨ ap (λ ϕ →  ⟦p⟧ * (⟦q⟧ * x₀ + ⟦s⟧) * x₀ + (ϕ + ⟦r⟧ * ⟦s⟧)) (*-associative ⟦r⟧ ⟦q⟧ x₀) ⟩
  ⟦p⟧ * (⟦q⟧ * x₀ + ⟦s⟧) * x₀ + (⟦r⟧ * (⟦q⟧ * x₀) + ⟦r⟧ * ⟦s⟧) ≡˘⟨ ap (λ ϕ → ⟦p⟧ * (⟦q⟧ * x₀ + ⟦s⟧) * x₀ + ϕ) (*-distrib-+l (⟦q⟧ * x₀) ⟦s⟧ ⟦r⟧) ⟩
  ⟦p⟧ * (⟦q⟧ * x₀ + ⟦s⟧) * x₀ + ⟦r⟧ * (⟦q⟧ * x₀ + ⟦s⟧)         ≡⟨ ap (λ ϕ → ϕ + ⟦r⟧ * (⟦q⟧ * x₀ + ⟦s⟧)) (commute-last ⟦p⟧ (⟦q⟧ * x₀ + ⟦s⟧) x₀) ⟩
  ⟦p⟧ * x₀ * (⟦q⟧ * x₀ + ⟦s⟧) + ⟦r⟧ * (⟦q⟧ * x₀ + ⟦s⟧)         ≡˘⟨ *-distrib-+r (⟦p⟧ * x₀) ⟦r⟧ (⟦q⟧ * x₀ + ⟦s⟧) ⟩
  (⟦p⟧ * x₀ + ⟦r⟧) * (⟦q⟧ * x₀ + ⟦s⟧)                          ∎
  where
    ⟦p*⟨qx+s⟩+r*q⟧ = ⟦ (p *ₚ (q *X+ s)) +ₚ (r *ₚ′ q) ⟧ₚ (x₀ ∷ env)
    ⟦p*⟨qx+s⟩⟧ = ⟦ p *ₚ (q *X+ s) ⟧ₚ (x₀ ∷ env)
    ⟦r*q⟧ = ⟦ r *ₚ′ q ⟧ₚ (x₀ ∷ env)
    ⟦p⟧ = ⟦ p ⟧ₚ (x₀ ∷ env)
    ⟦r⟧ = ⟦ r ⟧ₚ env
    ⟦q⟧ = ⟦ q ⟧ₚ (x₀ ∷ env)
    ⟦s⟧ = ⟦ s ⟧ₚ env
```

As a nice pallate cleanser, the proofs for heterogeneous multiplication are
nowhere near as bad.

```agda
sound-*ₚ′ p zerop x₀ env = sym (*-zeror (⟦ p ⟧ₚ env))
sound-*ₚ′ r (p *X+ q) x₀ env =
  ⟦ r *ₚ′ p ⟧ₚ (x₀ ∷ env) * x₀ + ⟦ r *ₚ q ⟧ₚ env ≡⟨  ap₂ (λ ϕ ψ → ϕ * x₀ + ψ) (sound-*ₚ′ r p x₀ env) (sound-*ₚ r q env) ⟩
  ⟦r⟧ * ⟦p⟧ * x₀ + ⟦r⟧ * ⟦q⟧                     ≡⟨ ap (λ ϕ → ϕ + ⟦r⟧ * ⟦q⟧) (*-associative ⟦r⟧ ⟦p⟧ x₀) ⟩
  ⟦r⟧ * (⟦p⟧ * x₀) + ⟦r⟧ * ⟦q⟧                   ≡˘⟨ *-distrib-+l  (⟦p⟧ * x₀) ⟦q⟧ ⟦r⟧ ⟩
  ⟦r⟧ * (⟦p⟧ * x₀ + ⟦q⟧)                         ∎
  where
    ⟦r⟧ = ⟦ r ⟧ₚ env
    ⟦p⟧ = ⟦ p ⟧ₚ (x₀ ∷ env)
    ⟦q⟧ = ⟦ q ⟧ₚ env
```

This concludes phase one of the solver.

## Evaluation into Polynomials

Now that we've gotten the first phase of the solver done, let's move on
to expressions in the language of natural numbers. Our first move shall be
defining expressions in the equational theory of natural numbers.

However, there is an efficiency problem we need to take care of here. If we naively
expand out `_+_`{.Agda} and `_*_`{.Agda} during reflection, we could end
up in a situation where we need to contend with a _huge_ amount of `suc`{.Agda}
constructors when large literals get involved. Therefore, we prevent reduction
of such functions, but this means this phase of the solver needs to be aware of
nat literals.

With that in mind, let's define our expressions. Note that things that the solver
is unable to deal with (for instance, functions that aren't `_+_`{.Agda}
or `_*_`{.Agda}) are represented as variables, and will be replaced during
evaluation.

```agda
data Expr : Nat → Type where
  ‵_   : ∀ {n} → Fin n → Expr n
  ‵0   : ∀ {n} → Expr n
  ‵1+_ : ∀ {n} → Expr n → Expr n
  ‵lit : ∀ {n} → Nat → Expr n
  _‵+_ : ∀ {n} → Expr n → Expr n → Expr n
  _‵*_ : ∀ {n} → Expr n → Expr n → Expr n
```


We also define an interpretation of expressions
into functions $\mathbb{N}^n \to \mathbb{N}$.

```agda
⟦_⟧ₑ : Expr n → Vec Nat n → Nat
⟦ ‵ i ⟧ₑ env = lookup env i
⟦ ‵0 ⟧ₑ env = 0
⟦ ‵1+ e ⟧ₑ env = suc (⟦ e ⟧ₑ env)
⟦ ‵lit k ⟧ₑ env = k
⟦ e1 ‵+ e2 ⟧ₑ env = ⟦ e1 ⟧ₑ env + ⟦ e2 ⟧ₑ env
⟦ e1 ‵* e2 ⟧ₑ env = ⟦ e1 ⟧ₑ env * ⟦ e2 ⟧ₑ env
```

We also define an evaluation of expressions into polynomials. The only thing
to note here is the evaluation of quoted `suc`{.Agda} constructors as polynomial
addition. This is somewhat inneficient, but in practice we rarely have too
many `suc`{.Agda} constructors to deal with, as we handle literals separately.

```agda
↓_ : Expr n → Poly Nat n
↓ (‵ i) = X[ i ]
↓ ‵0 = 0ₚ
↓ (‵1+ e) = constₚ 1 +ₚ ↓ e
↓ ‵lit k = constₚ k
↓ (e₁ ‵+ e₂) = (↓ e₁) +ₚ (↓ e₂)
↓ (e₁ ‵* e₂) = (↓ e₁) *ₚ (↓ e₂)
```

### Soundness of Evaluation

With all of that machinery in place, our final proof shall be to show that evaluating
an expression into a polynomial has the same semantics as the original expression.
Luckily, most of legwork is done already, and we can sit back and enjoy the fruits
of our labor.

```agda
sound : ∀ e → (env : Vec Nat n) → ⟦ ↓ e ⟧ₚ env ≡ ⟦ e ⟧ₑ env
sound (‵ i) env = sound-X[ i ] env
sound ‵0 env = sound-0ₚ env
sound (‵1+ e) env =
  ⟦ constₚ 1 +ₚ (↓ e) ⟧ₚ env       ≡⟨ sound-+ₚ (constₚ 1) (↓ e) env ⟩
  ⟦ constₚ 1 ⟧ₚ env + ⟦ ↓ e ⟧ₚ env ≡⟨ ap (λ ϕ → ϕ + ⟦ ↓ e ⟧ₚ env ) (sound-constₚ 1 env) ⟩
  suc (⟦ ↓ e ⟧ₚ env)               ≡⟨ ap suc (sound e env) ⟩
  suc (⟦ e ⟧ₑ env) ∎
sound (‵lit k) env = sound-constₚ k env
sound (e₁ ‵+ e₂) env =
  ⟦ (↓ e₁) +ₚ (↓ e₂) ⟧ₚ env     ≡⟨ sound-+ₚ (↓ e₁) (↓ e₂) env ⟩
  ⟦ ↓ e₁ ⟧ₚ env + ⟦ ↓ e₂ ⟧ₚ env ≡⟨ ap₂ _+_ (sound e₁ env) (sound e₂ env) ⟩
  ⟦ e₁ ⟧ₑ env + ⟦ e₂ ⟧ₑ env     ∎
sound (e₁ ‵* e₂) env =
  ⟦ (↓ e₁) *ₚ (↓ e₂) ⟧ₚ env     ≡⟨ sound-*ₚ (↓ e₁) (↓ e₂) env ⟩
  ⟦ ↓ e₁ ⟧ₚ env * ⟦ ↓ e₂ ⟧ₚ env ≡⟨ ap₂ _*_ (sound e₁ env) (sound e₂ env) ⟩
  ⟦ e₁ ⟧ₑ env * ⟦ e₂ ⟧ₑ env     ∎

```

Now, all we need to do is expose an interface for the reflection portion of the solver.
The `abstract` here is VERY IMPORTANT, as it prevents the proof from unfolding
into an enourmous term that kills our compile times.

```agda
abstract
  solve : ∀ e₁ e₂ → (env : Vec Nat n)
             → (⟦ ↓ e₁ ⟧ₚ env ≡ ⟦ ↓ e₂ ⟧ₚ env)
             → ⟦ e₁ ⟧ₑ env ≡ ⟦ e₂ ⟧ₑ env
  solve e₁ e₂ env p = sym (sound e₁ env) ∙ p ∙ (sound e₂ env)
```

We also expose a function for "simplifying" expressions. In reality this
will almost always make the term more complicated, but it's useful for debugging
purposes.

```agda
expand : (e : Expr n) → (env : Vec Nat n) → Nat
expand e env = ⟦ ↓ e ⟧ₚ env
```

## Reflection

Now, for the _truly_ difficult part: the reflection interface. We begin by
defining some pattern synonyms for expressions we want to reflect into our
`Expr`{.Agda} type.

```agda
private  
  pattern nat-lit n =
    def (quote Number.fromNat) (_ h∷ _ h∷ _ v∷ (lit (nat n)) v∷ _)
  pattern ″zero″ =
    con (quote zero) []
  pattern ″suc″ x =
    con (quote suc) (x v∷ [])
  pattern _″+″_ x y =
    def (quote _+_) (x v∷ y v∷ _)
  pattern _″*″_ x y =
    def (quote _*_) (x v∷ y v∷ _)
```

Next, we construct quoted a `Expr`{.Agda} from a term, replacing any unknown
`Term`{.Agda} nodes with variables. This uses the `Variable` interface
for managing the `Fin` variables and the environment. A discussion of the internals
of this is out of scope of this solver; we have already looked into the abyss too
deeply.

```agda
private
  build-expr : Variables Nat → Term → TC (Term × Variables Nat)
  build-expr vs (nat-lit n) = do
    ‵n ← quoteTC n
    returnTC $ con (quote ‵lit) (‵n v∷ []) , vs
  build-expr vs ″zero″ = do
    returnTC $ con (quote ‵0) (unknown h∷ []) , vs
  build-expr vs (″suc″ t) = do
    e , vs ← build-expr vs t
    returnTC $ con (quote ‵1+_) (unknown h∷ e v∷ []) , vs
  build-expr vs (t₁ ″+″ t₂) = do
    e₁ , vs ← build-expr vs t₁
    e₂ , vs ← build-expr vs t₂
    returnTC $ con (quote _‵+_) (unknown h∷ e₁ v∷ e₂ v∷ []) , vs
  build-expr vs (t₁ ″*″ t₂) = do
    e₁ , vs ← build-expr vs t₁
    e₂ , vs ← build-expr vs t₂
    returnTC $ con (quote _‵*_) (unknown h∷ e₁ v∷ e₂ v∷ []) , vs
  build-expr vs tm = do
    (v , vs′) ← bind-var vs tm 
    returnTC $ con (quote ‵_) (v v∷ []) , vs′
```

Next, a quick helper for getting the endpoints of an equality.

```agda
private
  getBoundary : Term → TC (Maybe (Term × Term))
  getBoundary tm@(def (quote PathP) (_ h∷ T v∷ x v∷ y v∷ [])) = do
    unify tm (def (quote _≡_) (x v∷ y v∷ []))
    returnTC (just (x , y))
  getBoundary (meta m _) = blockOnMeta m
  getBoundary _ = returnTC nothing
```

Next, let's define the quoted forms of some terms that we will
use to interface with the solver.

```agda
private
  ″expand″ : Term → Term → Term
  ″expand″ e env = def (quote expand) (unknown h∷ e v∷ env v∷ [])
  
  ″solve″ : Term → Term → Term → Term
  ″solve″ lhs rhs env =
    def (quote solve)
        (unknown h∷ lhs v∷ rhs v∷ env v∷ def (quote refl) [] v∷ [])
```

### The Actual Macros

Now, the actual reflection API calls. In order to keep drawing this file
out, we start by defining some useful debugging macros. As we noted a looong time ago,
we don't want to unfold the `_+_`{.Agda} or `_*_`{.Agda} functions, so 
let's make a list of those names so that we can call `dontReduceDefs`{.Agda}
more easily.

```agda
private
  dont-reduce : List Name
  dont-reduce = quote _+_ ∷ quote _*_ ∷ quote Number.fromNat ∷ []
```

The `repr!` macro prints out a bunch of information about a given expression
of type `Nat`. This is _very_ useful when we are debugging.

```agda
repr-macro : Nat → Term → TC ⊤
repr-macro n hole =
  withNormalisation false $
  dontReduceDefs dont-reduce $ do
  tm ← quoteTC n
  e , vs ← build-expr empty-vars tm
  size , env ← environment vs
  repr ← normalise $ def (quote ↓_) (size h∷ e v∷ [])
  typeError $ strErr "The expression\n  " ∷
                termErr tm ∷
              strErr "\nIs represented by the expression\n  " ∷
                termErr e ∷
              strErr "\nAnd the polynomial\n  " ∷
                termErr repr ∷
              strErr "\nThe environment is\n  " ∷
                termErr env ∷ []
macro
  repr! : Nat → Term → TC ⊤
  repr! n = repr-macro n
```

Slightly more useful is the `expand!` macro. This takes in a natural
number, and will fill in the hole with it's expanded form. This is intended
to be used with the `agda2-elaborate-give` command in Emacs, which is bound to
`C-c RET` by default.

```agda
expand-macro : Nat → Term → TC ⊤
expand-macro n hole =
  withNormalisation false $
  dontReduceDefs dont-reduce $ do
  tm ← quoteTC n
  e , vs ← build-expr empty-vars tm
  size , env ← environment vs
  expanded ← reduce (″expand″ e env)
  unify hole expanded

macro
  expand! : Nat → Term → TC ⊤
  expand! n = expand-macro n
```

Now, finally we have reached the summit. The `solve!` macro
allows us to automatically solve equations involving natural numbers.

```agda
solve-macro : Term → TC ⊤
solve-macro hole =
  withNormalisation false $
  dontReduceDefs dont-reduce $ do
  goal ← inferType hole >>= reduce

  just (lhs , rhs) ← getBoundary goal
    where nothing → typeError $ strErr "Can't determine boundary: " ∷
                                termErr goal ∷ []
  elhs , vs ← build-expr empty-vars lhs
  erhs , vs ← build-expr vs rhs
  size , env ← environment vs
  (noConstraints $ unify hole (″solve″ elhs erhs env)) <|> do
    nf-lhs ← normalise (″expand″ elhs env)
    nf-rhs ← normalise (″expand″ erhs env)
    typeError (strErr "Could not solve the following goal:\n  " ∷
                 termErr lhs ∷ strErr " ≡ " ∷ termErr rhs ∷
               strErr "\nComputed normal forms:\n  LHS: " ∷
                 termErr nf-lhs ∷
               strErr "\n  RHS: " ∷
                 termErr nf-rhs ∷ [])

macro
  solve! : Term → TC ⊤
  solve! = solve-macro
```

# Examples

Congratulations! We now have a solver. Let's marvel at all of our hard work
for a moment.

```agda
private
  wow-good-job : ∀ x y z
                 → (x + 5 + suc y) * z ≡ z * 5 + x * z + z + z * y 
  wow-good-job x y z = solve!
```

Thus concludes our journey. There is still room for improvement, however.
A sparse representation would be much more efficient, but these proofs are
already quite difficult to begin with. For the brave, here is what a
sparse representation might look like.

```agda
private
  data SparsePoly {a} (A : Type a) : Nat → Type a where
    const-sparse : ∀ {n} → A → SparsePoly A n
    shift        : ∀ {n} → (j : Nat) → SparsePoly A n
                   → SparsePoly A (j + n)
    _*X^_+_      : ∀ {n} → SparsePoly A (suc n) → Nat → SparsePoly A n
                   → SparsePoly A (suc n)
```
