<!--
```agda
open import Prim.Interval
open import Prim.Type
```
-->

```agda
module Prim.Extension where
```

# Primitives: Extension types

Using the type of `Partial`{.Agda} elements lets us specify maps from
some sub-object of a power of the interval to a type $A$. The _cubical
subtypes_, or extension types, give us the ability to encode that such a
partial element $p$ fits into a commutative diagram

~~~{.quiver}
\[\begin{tikzcd}
  {\sqcup^n_\varphi} && A \\
  \\
  {\square^n}
  \arrow[dashed, from=1-1, to=3-1]
  \arrow["p", from=1-1, to=1-3]
  \arrow["e", from=3-1, to=1-3]
\end{tikzcd}\]
~~~

where $e$ is an ordinary element of $A$ (with $n$ dimension variables).
Commutativity means that, where $p$ is defined, $e$ agrees with it
definitionally.

```agda
{-# BUILTIN SUB _[_↦_] #-}

postulate
  inS : ∀ {ℓ} {A : Type ℓ} {φ} (x : A) → A [ φ ↦ (λ _ → x) ]

{-# BUILTIN SUBIN inS #-}

private module X where primitive
  primSubOut : ∀ {ℓ} {A : Type ℓ} {φ : I} {u : Partial φ A} → A [ φ ↦ u ] → A

open X renaming (primSubOut to outS) public
```

Using extension types, we can represent the accurate type of
`primPOr`{.Agda}, where the two partial elements `u` and `v` must agree
on the intersection `i ∧ j`.

```agda
partial-pushout
  : ∀ {ℓ} (i j : I) {A : Partial (i ∨ j) (Type ℓ)}
    {ai : PartialP {a = ℓ} (i ∧ j) (λ { (j ∧ i = i1) → A 1=1 }) }
  → (.(z : IsOne i) → A (leftIs1 i j z)  [ (i ∧ j) ↦ (λ { (i ∧ j = i1) → ai 1=1 }) ])
  → (.(z : IsOne j) → A (rightIs1 i j z) [ (i ∧ j) ↦ (λ { (i ∧ j = i1) → ai 1=1 }) ])
  → PartialP (i ∨ j) A
partial-pushout i j u v = primPOr i j (λ z → outS (u z)) (λ z → outS (v z))
```
