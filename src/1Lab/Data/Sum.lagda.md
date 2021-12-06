```agda
open import 1Lab.Data.Dec
open import 1Lab.Equiv
open import 1Lab.Path
open import 1Lab.Type

module 1Lab.Data.Sum where
```

# Sum Types

Sum types are one of the fundamental ingredients of type theory.
They play a dual role to the [product type](agda://1Lab.Type#_×_);
if products allow us to state that we have elements of two types simultaneously,
sum types allow us to state that we have an element of _one_ of two types.

We use the notation `A ⊎ B` to hint at this type's set-theoretic analog: 
the disjoint union.

```agda
infixr 1 _⊎_

data _⊎_ {a b} (A : Type a) (B : Type b) : Type (a ⊔ b) where
  inₗ : A → A ⊎ B
  inᵣ : B → A ⊎ B
```
<!--
```agda
private variable
    a b c d : Level
    A : Type a
    B : Type b
    C : Type c
    D : Type d
```
-->

## Universal Properties

One of the most important things about sum types is the following property:
given two functions `A → C` and `B → C`, we can construct a function
`A ⊎ B → C`.

```agda
[_,_] : (A → C) → (B → C) → (A ⊎ B) → C
[ f , g ] (inₗ x) = f x
[ f , g ] (inᵣ x) = g x
```

Furthermore, this function is "universal" in the following sense:
if we have some function `h : A ⊎ B → C` that behaves like
`f` when provided an `inₗ a`, and like `g` when provided `inᵣ b`, then
`h` _must_ be equal to `[ f , g ]`.

```agda
[]-unique : ∀ {f : A → C} {g : B → C} {h} → f ≡ h ∘ inₗ → g ≡ h ∘ inᵣ → [ f , g ] ≡ h
[]-unique p q = funext λ { (inₗ x) i → p i x ; (inᵣ x) i → q i x }
```

We also have the following **eta law**. In general, eta laws relate the
_introduction_ forms with the _elimination_ forms. The most familiar eta
law is the one for functions: `λ x → (f x)` is the same as `f`. In agda,
the eta law for functions requires no proof, it holds by definition.
However, the same cannot be said for sum types, so we prove it here.

```agda
[]-η : ∀ (x : A ⊎ B) → [ inₗ , inᵣ ] x ≡ x
[]-η (inₗ x) = refl
[]-η (inᵣ x) = refl
```

This universal property can be strengthened to characterising the space
of _dependent functions_ out of the disjoint union: A dependent function
`(x : A ⊎ B) → P x` is the product of functions covering the left and
right cases.

```
⊎-universal : ∀ {a b p} {A : Type a} {B : Type b} {P : A ⊎ B → Type p}
            → ((x : A ⊎ B) → P x)
            ≃ (((x : A) → P (inₗ x)) × ((y : B) → P (inᵣ y)))
⊎-universal {A = A} {B} {P} = Iso→Equiv the-iso where
  the-iso : Iso _ _
```

For "splitting" a dependent function from the coproduct, we can compose
it with either of the constructors to restrict to a function on that
factor:

```
  the-iso .fst f = (λ x → f (inₗ x)) , (λ x → f (inᵣ x))
```

Similarly, given a pair of functions, we can do a case split on the
coproduct to decide which function to apply:

```
  the-iso .snd .isIso.g (f , g) (inₗ x) = f x
  the-iso .snd .isIso.g (f , g) (inᵣ x) = g x

  the-iso .snd .isIso.right-inverse x = refl
  the-iso .snd .isIso.left-inverse f i (inₗ x) = f (inₗ x)
  the-iso .snd .isIso.left-inverse f i (inᵣ x) = f (inᵣ x)
```

## Transformations

Let's move away from the abstract nonsense of universal properties for a bit,
and cleanse our pallate with some small helper functions for mapping between sum
types.

```agda
⊎-map : (A → C) → (B → D) → A ⊎ B → C ⊎ D
⊎-map f g (inₗ a) = inₗ (f a)
⊎-map f g (inᵣ b) = inᵣ (g b)

⊎-mapₗ : (A → C) → A ⊎ B → C ⊎ B
⊎-mapₗ f = ⊎-map f id

⊎-mapᵣ : (B → C) → A ⊎ B → A ⊎ C
⊎-mapᵣ f = ⊎-map id f
```

## Decidablity

This type has a very similar structure to [Dec](agda://1Lab.Data.Dec#Dec), so
we provide some helpers to convert between the two.

```agda
from-dec : Dec A → A ⊎ (A → ⊥)
from-dec (yes a) = inₗ a
from-dec (no ¬a) = inᵣ ¬a

to-dec : A ⊎ (A → ⊥) → Dec A
to-dec (inₗ  a) = yes a
to-dec (inᵣ ¬a) = no ¬a
```
