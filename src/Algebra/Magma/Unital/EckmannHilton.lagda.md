
```agda
open import 1Lab.Prelude

open import Algebra.Magma.Unital
open import Algebra.Semigroup
open import Algebra.Monoid

module Algebra.Magma.Unital.EckmannHilton where
```

# The Eckmann-Hilton Argument

The **Eckmann-Hilton argument** shows that two
`unital magmas`{.Agda ident=isUnitalMagma} on the same carrier type that
satisfy a particular interchange law are not only equal to another,
but are also commutative and associative.

More precisely, let $(A,e,\star)$ and $(A,e',\star')$ two unital magmas
such that $(a \star b) \star' (c \star d) = (a \star' c) \star (b \star' d)$.

```agda
module _ {ℓ : _} {A : Type ℓ} {_⋆_ : A → A → A} {_⋆'_ : A → A → A} {e : A} {e' : A}
  (unitalMgm : isUnitalMagma e _⋆_) (unitalMgm' : isUnitalMagma e' _⋆'_)
  (interchange : (a b c d : A) → (a ⋆ b) ⋆' (c ⋆ d) ≡ (a ⋆' c) ⋆ (b ⋆' d)) where
```

Then, one can first show that both operations share a unit,
i.e. $e = e'$. Notably, this holds because the units can be expanded to
products of themselves, which can then be transformed into another by
making use of the interchange equation.

```agda
  unitsEqual : e ≡ e'
  unitsEqual =
    e                        ≡⟨ sym (idˡ unitalMgm) ⟩
    (e ⋆ e)                  ≡⟨ ap₂ _⋆_ (sym (idˡ unitalMgm')) (sym (idʳ unitalMgm')) ⟩
    ((e' ⋆'  e) ⋆ (e ⋆' e')) ≡⟨ sym (interchange e' e e e') ⟩
    ((e' ⋆ e) ⋆' (e ⋆ e'))   ≡⟨ ap₂ _⋆'_ (idʳ unitalMgm) (idˡ unitalMgm) ⟩
    (e' ⋆' e')               ≡⟨ idˡ unitalMgm' ⟩
    e' ∎
```

From there on, we are able to derive that one operation is equal to the
dual of the other, once again by using the interchange law as well as
swapping units whenever needed.

```agda
  ⋆-reverse-⋆' : (x y : A) → x ⋆ y ≡ y ⋆' x
  ⋆-reverse-⋆' x y =
    x ⋆ y                 ≡⟨ ap₂ _⋆_ (sym (idˡ unitalMgm')) (sym (idʳ unitalMgm')) ⟩
    (e' ⋆' x) ⋆ (y ⋆' e') ≡⟨ sym (interchange e' y x e') ⟩
    (e' ⋆ y) ⋆' (x ⋆ e')  ≡⟨ ap₂ _⋆'_ (ap (_⋆ y) (sym unitsEqual)) (ap (x ⋆_) (sym unitsEqual)) ⟩
    (e ⋆ y) ⋆' (x ⋆ e)    ≡⟨ ap₂ _⋆'_ (idˡ unitalMgm) (idʳ unitalMgm) ⟩
    y ⋆' x ∎
```

By a similar method, we can show pointwise equality of the two
operators.

```agda
  operationsEqual : (x y : A) → x ⋆ y ≡ x ⋆' y
  operationsEqual x y =
    x ⋆ y                 ≡⟨ ap₂ _⋆_ (sym (idʳ unitalMgm')) (sym (idˡ unitalMgm')) ⟩
    (x ⋆' e') ⋆ (e' ⋆' y) ≡⟨ sym (interchange x e' e' y) ⟩
    (x ⋆ e') ⋆' (e' ⋆ y)  ≡⟨ ap₂ _⋆'_ (sym (ap (_⋆_ x) unitsEqual)) (sym (ap (_⋆ y) unitsEqual)) ⟩
    (x ⋆ e) ⋆' (e ⋆ y)    ≡⟨ ap₂ _⋆'_ (idʳ unitalMgm) (idˡ unitalMgm) ⟩
    x ⋆' y ∎
```

These two properties make it rather straightforward to show that $\star$
is commutative - since we know that $a \star b = a \star' b$ as well as
$a \star b = b \star' a$, the proof can be completed by simple path
concatenation.

```agda
  ⋆-commutative : (x y : A) → x ⋆ y ≡ y ⋆ x
  ⋆-commutative x y = ⋆-reverse-⋆' x y ∙ sym (operationsEqual y x)
```

Finally, associativity of the operation can be established by what can
be informally described as rotating the elements of the product, using
commutativity inside the factors of a products that can then be
interchanged and reduced. Thus, associativity combined with the assumed
unitality allows us to prove that the operation is a monoid.

```agda
  ⋆-associative : (x y z : A) → x ⋆ (y ⋆ z) ≡ (x ⋆ y) ⋆ z
  ⋆-associative x y z = sym (
    (x ⋆ y) ⋆ z         ≡⟨ ap (λ a → (x ⋆ y) ⋆ a) (sym (idʳ unitalMgm)) ⟩
    (x ⋆ y) ⋆ (z ⋆ e)   ≡⟨ ap (λ x → x ⋆ (z ⋆ e)) (⋆-commutative x y) ⟩
    (y ⋆ x) ⋆ (z ⋆ e)   ≡⟨ operationsEqual (y ⋆ x) (z ⋆ e) ⟩
    (y ⋆ x) ⋆' (z ⋆ e)  ≡⟨ interchange y x z e ⟩
    (y ⋆' z) ⋆ (x ⋆' e) ≡⟨ ⋆-commutative (y ⋆' z) (x ⋆' e) ⟩
    (x ⋆' e) ⋆ (y ⋆' z) ≡⟨ ap₂ _⋆_ (sym (operationsEqual x e)) (sym (operationsEqual y z)) ⟩
    (x ⋆ e) ⋆ (y ⋆ z)   ≡⟨ ap (_⋆ (y ⋆ z)) (idʳ unitalMgm) ⟩
    x ⋆ (y ⋆ z) ∎)

  ⋆-isMonoid : isMonoid e _⋆_
  ⋆-isMonoid .hasIsSemigroup .hasIsMagma = unitalMgm .hasIsMagma
  ⋆-isMonoid .hasIsSemigroup .associative = ⋆-associative _ _ _
  ⋆-isMonoid .idˡ = unitalMgm .idˡ
  ⋆-isMonoid .idʳ = unitalMgm .idʳ
```
