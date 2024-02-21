<!--
```agda
open import 1Lab.Path
open import 1Lab.Type
```
-->

```agda
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
$A(i) \to A(j)$. In Cubical Agda, we can implement this by transporting
along a function of three variables $t, x, y$ which "interpolates"
between $x$ and $y$ as $t$ increases.

The interpolation function we're using was discovered by Tom Jack, who
kindly allowed us to use it here on the 1Lab:

```agda
I-eq : I → I → I
I-eq i j = (i ∧ j) ∨ (~ i ∧ ~ j)

I-interp : I → I → I → I
I-interp t x y = (~ t ∧ x) ∨ (t ∧ y) ∨ (x ∧ y)
```

```agda
coe : ∀ {ℓ : I → Level} (A : ∀ i → Type (ℓ i)) (i j : I) → A i → A j
coe A i j a = transp (λ k → A (I-interp k i j)) (I-eq i j) a
```

To show that this definition computes as expected, we can compare it to
the other coercion operations (squeezes and spreads) we've already
defined by hand:

```agda
coei0→0 : ∀ {ℓ} (A : I → Type ℓ) a → coei→0 A i0 a ≡ a
coei1→0 : ∀ {ℓ} (A : I → Type ℓ) a → coei→0 A i1 a ≡ coe1→0 A a

coei0→1 : ∀ {ℓ} (A : I → Type ℓ) a → coei→1 A i0 a ≡ coe0→1 A a
coei1→1 : ∀ {ℓ} (A : I → Type ℓ) a → coei→1 A i1 a ≡ a

coei→i0 : ∀ {ℓ} (A : I → Type ℓ) i a → coe A i i0 a ≡ coei→0 A i a
coei→i1 : ∀ {ℓ} (A : I → Type ℓ) i a → coe A i i1 a ≡ coei→1 A i a

coei0→i : ∀ {ℓ} (A : I → Type ℓ) i a → coe A i0 i a ≡ coe0→i A i a
coei1→i : ∀ {ℓ} (A : I → Type ℓ) i a → coe A i1 i a ≡ coe1→i A i a
```

Impressively, all these computation rules are `refl`{.Agda}:

```agda
coei0→1 A a = refl
coei1→1 A a = refl
coei1→0 A a = refl
coei0→0 A a = refl
coei→i0 A i a = refl
coei0→i A i a = refl
coei→i1 A i a = refl
coei1→i A i a = refl
```

In Cartesian cubical type theory, the following equation is
definitional. However, in Cubical Agda, it is only propositional:

```agda
coei→i : ∀ {ℓ} (A : I → Type ℓ) i x → coe A i i x ≡ x
coei→i A i x j = transp (λ _ → A i) (j ∨ i ∨ ~ i) x
```

<!--
```agda
coe-path : ∀ {ℓ} (A : I → Type ℓ) (p : ∀ i → A i) i j → coe A i j (p i) ≡ p j
coe-path A p i j k = transp
  (λ l → A (I-interp k (I-interp l i j) j))
  (I-interp k (I-eq i j) i1)
  (p (I-interp k i j))
```
-->
