<!--
```agda
open import Cat.Prelude

open import Order.Base
```
-->

```agda
module Order.Reasoning {ℓ ℓ'} (P : Poset ℓ ℓ') where
```

# Partial order syntax

This module defines a syntax for reasoning with transitivity in a
[[partial order]]. Simply speaking, it lets us write chains like

$$
a \le b \le c
$$

to mean something like "$a \le c$ through the intermediate step $b$". In
the syntax, we intersperse the justification for _why_ $a \le b$ and $b
\le c$. We also allow equality steps, so chains like $a \le b = b' \le
c$ are supported, too.

```agda
open Poset P public

private variable
  a b c d : ⌞ P ⌟

_≤⟨_⟩_ : (a : ⌞ P ⌟) → a ≤ b → b ≤ c → a ≤ c
_=⟨_⟩_ : (a : ⌞ P ⌟) → a ≡ b → b ≤ c → a ≤ c
_=˘⟨_⟩_ : (a : ⌞ P ⌟) → b ≡ a → b ≤ c → a ≤ c
_≤∎    : (a : ⌞ P ⌟) → a ≤ a

f ≤⟨ p ⟩ q = ≤-trans p q
f =⟨ p ⟩ q = subst (_≤ _) (sym p) q
f =˘⟨ p ⟩ q = subst (_≤ _) p q
f ≤∎ = ≤-refl

infixr 2 _=⟨_⟩_ _=˘⟨_⟩_ _≤⟨_⟩_
infix  3 _≤∎
```
