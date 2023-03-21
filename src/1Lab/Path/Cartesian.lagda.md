```agda
open import 1Lab.Type
open import 1Lab.Path

module 1Lab.Path.Cartesian where
```

## Coercion

In Cubical Agda, the interval is given the structure of a De Morgan
algebra. This is not the only choice of structure on the interval that
gives a model of univalent type theory: We could also subject the
interval to _no_ additional structure other than what comes from the
structural rules of type theory (introducing variables, ignoring
variables, swapping variables, etc). This is a different cubical type
theory, called _Cartesian cubical type theory_.

In Cartesian cubical type theory, rather than our `transp`{.Agda}
operation, the fundamental operation for manipulating paths is
`coe`{.Agda}, which implements an arbitrary change of interval variables
$A(i) \to A(j)$. We can implement `coe`{.Agda} using our pre-existing
"squeezes" and "spreads", as the filler of the square

~~~{.quiver}
\[\begin{tikzcd}
  {a} && {\rm{coe}^A_{1\to0}(a)} \\
  \\
  {\rm{coe}^A_{0\to1}(a)} && {a\text{.}}
  \arrow["{\rm{coe}^A_{0\to j}(a)}"', from=1-1, to=3-1]
  \arrow["{\rm{coe}^A_{1\to j}(a)}", from=1-3, to=3-3]
  \arrow[""{name=0, anchor=center, inner sep=0}, "{\rm{coe}^A_{i\to0}(a)}", from=1-1, to=1-3]
  \arrow[""{name=1, anchor=center, inner sep=0}, "{\rm{coe}^A_{i\to1}(a)}"', dashed, from=3-1, to=3-3]
  \arrow["{\rm{coe}^A_{i\to j}(a)}"{description}, Rightarrow, draw=none, from=0, to=1]
\end{tikzcd}\]
~~~

```agda
coe : ∀ {ℓ : I → Level} (A : ∀ i → Type (ℓ i)) (i j : I) → A i → A j
coe A i j a = fill A (∂ i) j λ where
  j (i = i0) → coe0→i A j a
  j (i = i1) → coe1→i A j a
  j (j = i0) → coei→0 A i a
```

Note that `coe`{.Agda} also brings its own version of the $i \to i1$
squeeze, with much worse computational behaviour. We can't get the
definition above to agree with our squeezes and spreads on all possible
moves, so we chose $i \to i1$ as a sacrifice.

```
coei→1′ : ∀ {ℓ : I → Level} (A : ∀ i → Type (ℓ i)) (i : I) → A i → A i1
coei→1′ A i a = coe A i i1 a
```

This operation satisfies, _definitionally_, a whole host of equations.
For starters, we have that the $\rm{coe}^A_{i\to1}$ (resp $i \to 0$)
specialises to transport when $i = 0$ (resp. $i = 1$), and to the
identity when $i = 1$ (resp. $i = 0$):

```agda
coei0→1 : ∀ {ℓ} (A : I → Type ℓ) (a : A i0) → coei→1 A i0 a ≡ coe0→1 A a
coei0→1 A a = refl

coei1→1 : ∀ {ℓ} (A : I → Type ℓ) (a : A i1) → coei→1 A i1 a ≡ a
coei1→1 A a = refl

coei1→0 : ∀ {ℓ} (A : I → Type ℓ) (a : A i1) → coei→0 A i1 a ≡ coe1→0 A a
coei1→0 A a = refl

coei0→0 : ∀ {ℓ} (A : I → Type ℓ) (a : A i0) → coei→0 A i0 a ≡ a
coei0→0 A a = refl
```

Then we have paths connecting the "master coercion" `coe`{.Agda} and
its several faces:

```
coei→i0 : ∀ {ℓ} (A : I → Type ℓ) (i : I) (a : A i)
        → coe A i i0 a ≡ coei→0 A i a
coei→i0 A i a = refl

coei0→i : ∀ {ℓ} (A : I → Type ℓ) (i : I) (a : A i0)
        → coe A i0 i a ≡ coe0→i A i a
coei0→i A i a = refl

-- This one is really hard to prove, but fortunately, we never need it:
-- coei→i1 : ∀ {ℓ} (A : I → Type ℓ) (i : I) (a : A i)
--         → coe A i i1 a ≡ coei→1 A i a
-- coei→i1 A i a = refl

coei1→i : ∀ {ℓ} (A : I → Type ℓ) (i : I) (a : A i1)
        → coe A i1 i a ≡ coe1→i A i a
coei1→i A i a = refl
```

In Cartesian cubical type theory, the following equation is
definitional. It says that the top right and bottom left corners of the
diagram are indeed what I said they were! However, in Cubical Agda, it
is only propositional:

```agda
coei→i : ∀ {ℓ} (A : I → Type ℓ) (i : I) (a : A i) → coe A i i a ≡ a
coei→i A i = coe0→i (λ i → (a : A i) → coe A i i a ≡ a) i (λ _ → refl)
```

<!--
```agda
module _ {ℓ} {A : I → Type ℓ} {x y} (p : PathP A x y) {i} where
  coe-path-i→j : ∀ j → coe A i j (p i) ≡ p j
  coe-path-i→j j =
    coe (λ k → coe A i k (p i) ≡ p k) i j (coei→i A i (p i))

  coe-path-i→i : Square (coe-path-i→j i) (coei→i A i (p i)) refl refl
  coe-path-i→i =
    sym (coei→i (λ k → coe A i k (p i) ≡ p k) i (coei→i A i (p i)))
    ◁ λ m k → coe-path-i→j i (m ∨ k)
```
-->
