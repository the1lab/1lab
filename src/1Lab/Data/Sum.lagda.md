```agda
open import 1Lab.HLevel.Retracts
open import 1Lab.Data.Bool
open import 1Lab.Data.Nat
open import 1Lab.Data.Dec
open import 1Lab.HLevel
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
⊎-universal : ∀ {A : Type a} {B : Type b} {C : A ⊎ B → Type c}
            → ((x : A ⊎ B) → C x)
            ≃ ( ((x : A) → C (inₗ x))
              × ((y : B) → C (inᵣ y)))
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

These helpers are clearly inverses, and thus constitute an equivalence:

```
isEquiv-from-dec : {A : Type a} → isEquiv (from-dec {A = A})
isEquiv-from-dec = isIso→isEquiv (iso to-dec p q) where
  p : _
  p (inₗ x) = refl
  p (inᵣ x) = refl

  q : _
  q (yes x) = refl
  q (no x) = refl
```

## Closure under h-levels

If $A$ and $B$ are $n$-types, for $n \ge 2$, then so is their coproduct.
This is because the coproduct can be expressed as a `dependent
sum`{.Agda ident=_⊎_} indexed by `Bool`{.Agda}

```
isHLevel⊎ : (n : Nat)
          → isHLevel A (2 + n) → isHLevel B (2 + n)
          → isHLevel (A ⊎ B) (2 + n)
isHLevel⊎ {A = A} {B = B} hl a-hl b-hl =
  isHLevel-retract (2 + hl) ∐→⊎ ⊎→∐ retraction ∐-hlevel
  where
    common : Level
    common = level-of A ⊔ level-of B

    ∐ : Type common
    ∐ = Σ {A = Bool} λ { true → Lift common A ; false → Lift common B } 
```

We start by respelling the definition of `_⊎_`{.Agda} in terms of
`Σ`{.Agda}. This is a common _implementation_ of coproducts in languages
that do not support them: We have a _tag_, in this case `Bool`{.Agda},
and based on the tag, we store a value of either type. In this case, we
store `A` with `true`{.Agda} and `B` with `false`{.Agda}.

Note that since `A` and `B` may live in different universes, we must
`Lift`{.Agda} them to the least universe which contains both. Then we
can prove that `_⊎_`{.Agda} is a retract of `∐`{.Agda}:

```
    ⊎→∐ : A ⊎ B → ∐
    ⊎→∐ (inₗ x) = true , lift x
    ⊎→∐ (inᵣ x) = false , lift x

    ∐→⊎ : ∐ → A ⊎ B
    ∐→⊎ (false , snd₁) = inᵣ (Lift.lower snd₁)
    ∐→⊎ (true , snd₁) = inₗ (Lift.lower snd₁)

    retraction : (x : A ⊎ B) → ∐→⊎ (⊎→∐ x) ≡ x
    retraction (inₗ x) = refl
    retraction (inᵣ x) = refl
```

Because of computation, this is essentially automatic. Note that we must
both `lift`{.Agda} and `lower`{.Agda} values of type A/B when passing
from `_⊎_` to `∐`. Then a simple case split gives us the required property:

```
    bool' : isHLevel Bool (2 + hl)
    bool' = subst (λ e → isHLevel Bool e)
                  (+-commutative hl 2)
                  (isHLevel-+ 2 hl isSet-Bool)
```

Since `Bool`{.Agda} `is a set`{.Agda ident=isSet-Bool}, we have that it
automatically has any h-level greater than 2, i.e. `2 + hl`. We've
reduced the problem of showing that `_⊎_`{.Agda} has said h-level to the
problem of proving that `∐` does, which follows from `closure of
h-levels under Σ`{.Agda ident=isHLevelΣ}.

```
    ∐-hlevel : isHLevel ∐ (2 + hl)
    ∐-hlevel = isHLevelΣ (2 + hl) bool'
      λ { false → isHLevel-Lift (2 + hl) b-hl
        ; true → isHLevel-Lift (2 + hl) a-hl
        }
```

Note that, in general, [being a proposition] and [being contractible]
are not preserved under coproducts. Consider the case where `(A, a)` and
`(B, b)` are both contractible (this generalises to propositions): Then
their coproduct has two distinct points, `in­ₗ a` and `inᵣ b`. However,
the coproduct of _disjoint_ propositions is a proposition:

[being a proposition]: agda://1Lab.HLevel#isProp
[being contractible]: agda://1Lab.HLevel#isContr

```
isProp-disjoint-⊎ : isProp A → isProp B → (A × B → ⊥)
                  → isProp (A ⊎ B)
isProp-disjoint-⊎ Ap Bp notab (inₗ x) (inₗ y) = ap inₗ (Ap x y)
isProp-disjoint-⊎ Ap Bp notab (inₗ x) (inᵣ y) = absurd (notab (x , y))
isProp-disjoint-⊎ Ap Bp notab (inᵣ x) (inₗ y) = absurd (notab (y , x))
isProp-disjoint-⊎ Ap Bp notab (inᵣ x) (inᵣ y) = ap inᵣ (Bp x y)
```