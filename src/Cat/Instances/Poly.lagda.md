<!--
```agda
open import 1Lab.Reflection.Record

open import Cat.Univalent.Instances.Opposite
open import Cat.Displayed.Instances.Family
open import Cat.Displayed.Univalence
open import Cat.Instances.Discrete
open import Cat.Displayed.Total
open import Cat.Instances.Sets
open import Cat.Prelude

import Cat.Reasoning
```
-->

```agda
module Cat.Instances.Poly where
```

<!--
```agda
open Functor
open Total-hom
```
-->

# Polynomial functors and lenses

The category of _polynomial functors_ is the free coproduct completion
of $\Sets\op$. Equivalently, it is the [[total category]] of the [family
fibration] of $\Sets\op$. More concretely, an object of $\thecat{Poly}$
is given by a set $I$ and a family of sets $A : I \to \Sets$. The idea
is that these data corresponds to the polynomial (set-valued, with set
coefficients) given by

$$
p(y) = \sum_{i : I} y^{A_i}
$$

[family fibration]: Cat.Displayed.Instances.Family.html

```agda
Poly : ∀ ℓ → Precategory (lsuc ℓ) ℓ
Poly ℓ = ∫ {ℓ = ℓ} (Family (Sets ℓ ^op))

module Poly {ℓ} = Cat.Reasoning (Poly ℓ)
```

Our standard toolkit for showing [[univalence of total categories]]
applies here:

```agda
Poly-is-category : ∀ {ℓ} → is-category (Poly ℓ)
Poly-is-category =
  is-category-total _ Sets-is-category $
    is-category-fibrewise' _
      Sets-is-category
      (λ x → Families-are-categories _ x (opposite-is-category Sets-is-category))
```

It is entirely mechanical to calculate that morphisms in $\thecat{Poly}$
are given by pairs of a reindexing together with a contravariant action
on the families. It is _so_ mechanical that we can do it automatically:

```agda
poly-maps : ∀ {ℓ} {A B} → Iso
  (Poly.Hom {ℓ} A B)
  (Σ[ f ∈ (⌞ A ⌟ → ⌞ B ⌟) ] ∀ x → ∣ B .snd (f x) ∣ → ∣ A .snd x ∣)
unquoteDef poly-maps = define-record-iso poly-maps (quote Total-hom)
```

We also derive a convenient characterisation of paths between $\thecat{Poly}$ morphisms
using regularity:

```agda
poly-map-path
  : ∀ {ℓ A B} {f g : Poly.Hom {ℓ} A B}
  → (hom≡ : f .hom ≡ g .hom)
  → (pre≡ : ∀ a b → f .preserves a (subst (λ hom → ∣ B .snd (hom a) ∣) (sym hom≡) b)
                  ≡ g .preserves a b)
  → f ≡ g
poly-map-path hom≡ pre≡ = total-hom-path _ hom≡
  (to-pathp (ext λ a b → Regularity.precise! (pre≡ a b)))
```

## Polynomials as functors

We commented above that polynomials, i.e. terms of the type
`Poly`{.Agda}, should correspond to particular $\Sets$-valued
polynomials. In particular, given a polynomial $(I, A)$, it should be
possible to evaluate it at a set $X$ and get back a set. We take the
interpretation above _literally_:

```agda
Polynomial-functor : ∀ {ℓ} → Poly.Ob {ℓ} → Functor (Sets ℓ) (Sets ℓ)
Polynomial-functor (I , A) .F₀ X = el! (Σ[ i ∈ ∣ I ∣ ] (∣ A i ∣ → ∣ X ∣))
Polynomial-functor (I , A) .F₁ f (a , g) = a , λ z → f (g z)
Polynomial-functor (I , A) .F-id = refl
Polynomial-functor (I , A) .F-∘ f g = refl
```

Correspondingly, we refer to a polynomial whose family is $x \mapsto 1$
as _linear_, since these are those of the form $\sum_{i : I} y^1$, i.e.
$Iy^1$. If the family is constant at some _other_ set, e.g. $B$, we
refer to the corresponding polynomial as a _monomial_, since it can be
written $Iy^B$.

## Lenses

We call the maps in $\thecat{Poly}$ _dependent lenses_, or simply
_lenses_, because in the case of maps between monomials $Si^T \to Ay^B$,
we recover the usual definition of the Haskell type `Lens s t a b`:

```agda
Lens : ∀ {ℓ} (S T A B : Set ℓ) → Type ℓ
Lens S T A B = Poly.Hom (S , λ _ → T) (A , λ _ → B)

_ : ∀ {ℓ} {S T A B : Set ℓ} → Iso
  (Lens S T A B)
  ((∣ S ∣ → ∣ A ∣) × (∣ S ∣ → ∣ B ∣ → ∣ T ∣))
_ = poly-maps
```

We have a _view_ function $S \to A$ together with an _update_ function
$S \to B \to T$. The view and update functions are allowed to change the
type of the container: the idea is that a lens represents a "label" or
"pointer" from which one can read off an $A$ value given an $S$, but
upon writing a $B$ to the same pointer, our $S$ changes to a $T$
instead.
