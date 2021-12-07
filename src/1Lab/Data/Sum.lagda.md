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
  inl : A → A ⊎ B
  inr : B → A ⊎ B
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

As warmup, we have that both constructors are embeddings:

```
inl-inj : {B : Type b} {x y : A} → inl {B = B} x ≡ inl y → x ≡ y
inl-inj {A = A} {x = x} path = ap f path where
  f : A ⊎ B → A
  f (inl x) = x
  f (inr _) = x

inr-inj : {A : Type b} {x y : B} → inr {A = A} x ≡ inr y → x ≡ y
inr-inj {B = B} {x = x} path = ap f path where
  f : A ⊎ B → B
  f (inl _) = x
  f (inr x) = x

⊎-disjoint : {A : Type a} {B : Type b} {x : A} {y : B} → inl x ≡ inr y → ⊥
⊎-disjoint path = subst (λ { (inl x) → ⊤ ; (inr x) → ⊥ }) path tt
```

## Universal Properties

One of the most important things about sum types is the following property:
given two functions `A → C` and `B → C`, we can construct a function
`A ⊎ B → C`.

```agda
[_,_] : (A → C) → (B → C) → (A ⊎ B) → C
[ f , g ] (inl x) = f x
[ f , g ] (inr x) = g x
```

Furthermore, this function is "universal" in the following sense:
if we have some function `h : A ⊎ B → C` that behaves like
`f` when provided an `inl a`, and like `g` when provided `inr b`, then
`h` _must_ be equal to `[ f , g ]`.

```agda
[]-unique : ∀ {f : A → C} {g : B → C} {h} → f ≡ h ∘ inl → g ≡ h ∘ inr → [ f , g ] ≡ h
[]-unique p q = funext λ { (inl x) i → p i x ; (inr x) i → q i x }
```

We also have the following **eta law**. In general, eta laws relate the
_introduction_ forms with the _elimination_ forms. The most familiar eta
law is the one for functions: `λ x → (f x)` is the same as `f`. In agda,
the eta law for functions requires no proof, it holds by definition.
However, the same cannot be said for sum types, so we prove it here.

```agda
[]-η : ∀ (x : A ⊎ B) → [ inl , inr ] x ≡ x
[]-η (inl x) = refl
[]-η (inr x) = refl
```

This universal property can be strengthened to characterising the space
of _dependent functions_ out of the disjoint union: A dependent function
`(x : A ⊎ B) → P x` is the product of functions covering the left and
right cases.

```
⊎-universal : ∀ {A : Type a} {B : Type b} {C : A ⊎ B → Type c}
            → ((x : A ⊎ B) → C x)
            ≃ ( ((x : A) → C (inl x))
              × ((y : B) → C (inr y)))
⊎-universal {A = A} {B} {P} = Iso→Equiv the-iso where
  the-iso : Iso _ _
```

For "splitting" a dependent function from the coproduct, we can compose
it with either of the constructors to restrict to a function on that
factor:

```
  the-iso .fst f = (λ x → f (inl x)) , (λ x → f (inr x))
```

Similarly, given a pair of functions, we can do a case split on the
coproduct to decide which function to apply:

```
  the-iso .snd .isIso.g (f , g) (inl x) = f x
  the-iso .snd .isIso.g (f , g) (inr x) = g x

  the-iso .snd .isIso.right-inverse x = refl
  the-iso .snd .isIso.left-inverse f i (inl x) = f (inl x)
  the-iso .snd .isIso.left-inverse f i (inr x) = f (inr x)
```

## Transformations

Let's move away from the abstract nonsense of universal properties for a bit,
and cleanse our pallate with some small helper functions for mapping between sum
types.

```agda
⊎-map : (A → C) → (B → D) → A ⊎ B → C ⊎ D
⊎-map f g (inl a) = inl (f a)
⊎-map f g (inr b) = inr (g b)

⊎-mapl : (A → C) → A ⊎ B → C ⊎ B
⊎-mapl f = ⊎-map f id

⊎-mapr : (B → C) → A ⊎ B → A ⊎ C
⊎-mapr f = ⊎-map id f
```

## Decidablity

This type has a very similar structure to [Dec](agda://1Lab.Data.Dec#Dec), so
we provide some helpers to convert between the two.

```agda
from-dec : Dec A → A ⊎ (A → ⊥)
from-dec (yes a) = inl a
from-dec (no ¬a) = inr ¬a

to-dec : A ⊎ (A → ⊥) → Dec A
to-dec (inl  a) = yes a
to-dec (inr ¬a) = no ¬a
```

These helpers are clearly inverses, and thus constitute an equivalence:

```
isEquiv-from-dec : {A : Type a} → isEquiv (from-dec {A = A})
isEquiv-from-dec = isIso→isEquiv (iso to-dec p q) where
  p : _
  p (inl x) = refl
  p (inr x) = refl

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
    ⊎→∐ (inl x) = true , lift x
    ⊎→∐ (inr x) = false , lift x

    ∐→⊎ : ∐ → A ⊎ B
    ∐→⊎ (false , snd₁) = inr (Lift.lower snd₁)
    ∐→⊎ (true , snd₁) = inl (Lift.lower snd₁)

    retraction : (x : A ⊎ B) → ∐→⊎ (⊎→∐ x) ≡ x
    retraction (inl x) = refl
    retraction (inr x) = refl
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
their coproduct has two distinct points, `in­l a` and `inr b`. However,
the coproduct of _disjoint_ propositions is a proposition:

[being a proposition]: agda://1Lab.HLevel#isProp
[being contractible]: agda://1Lab.HLevel#isContr

```
isProp-disjoint-⊎ : isProp A → isProp B → (A × B → ⊥)
                  → isProp (A ⊎ B)
isProp-disjoint-⊎ Ap Bp notab (inl x) (inl y) = ap inl (Ap x y)
isProp-disjoint-⊎ Ap Bp notab (inl x) (inr y) = absurd (notab (x , y))
isProp-disjoint-⊎ Ap Bp notab (inr x) (inl y) = absurd (notab (y , x))
isProp-disjoint-⊎ Ap Bp notab (inr x) (inr y) = ap inr (Bp x y)
```

## Closure under equivalences

[Univalence] automatically implies that all type formers respect
equivalences. However, the proof using univalence is restricted to types
of the same universe level. Thus, `⊎-ap`{.Agda}: Coproducts respect
equivalences in both arguments, across levels.

[Univalence]: 1Lab.Univalence.html#the-axiom

```
⊎-ap : A ≃ B → C ≃ D → (A ⊎ C) ≃ (B ⊎ D)
⊎-ap (f , f-eqv) (g , g-eqv) = Iso→Equiv cong where
  f-iso = isEquiv→isIso f-eqv
  g-iso = isEquiv→isIso g-eqv

  cong : Iso _ _
  cong .fst (inl x) = inl (f x)
  cong .fst (inr x) = inr (g x)

  cong .snd .isIso.g (inl x) = inl (f-iso .isIso.g x)
  cong .snd .isIso.g (inr x) = inr (g-iso .isIso.g x)

  cong .snd .isIso.right-inverse (inl x) = ap inl (f-iso .isIso.right-inverse x)
  cong .snd .isIso.right-inverse (inr x) = ap inr (g-iso .isIso.right-inverse x)

  cong .snd .isIso.left-inverse (inl x) = ap inl (f-iso .isIso.left-inverse x)
  cong .snd .isIso.left-inverse (inr x) = ap inr (g-iso .isIso.left-inverse x)

⊎-apˡ : A ≃ B → (A ⊎ C) ≃ (B ⊎ C)
⊎-apˡ f = ⊎-ap f (id , idEquiv)

⊎-apʳ : B ≃ C → (A ⊎ B) ≃ (A ⊎ C)
⊎-apʳ f = ⊎-ap (id , idEquiv) f
```

## Algebraic properties

Considered as an algebraic operator on _types_, the coproduct satisfies
many of the same properties of addition. Specifically, when restricted
to finite types, the coproduct is exactly the same as addition.

```
⊎-comm : (A ⊎ B) ≃ (B ⊎ A)
⊎-comm = Iso→Equiv i where
  i : Iso _ _
  i .fst (inl x) = inr x
  i .fst (inr x) = inl x

  i .snd .isIso.g (inl x) = inr x
  i .snd .isIso.g (inr x) = inl x

  i .snd .isIso.right-inverse (inl x) = refl
  i .snd .isIso.right-inverse (inr x) = refl
  i .snd .isIso.left-inverse (inl x) = refl
  i .snd .isIso.left-inverse (inr x) = refl

⊎-assoc : ((A ⊎ B) ⊎ C) ≃ (A ⊎ (B ⊎ C))
⊎-assoc = Iso→Equiv i where
  i : Iso _ _
  i .fst (inl (inl x)) = inl x
  i .fst (inl (inr x)) = inr (inl x)
  i .fst (inr x)       = inr (inr x)

  i .snd .isIso.g (inl x)       = inl (inl x)
  i .snd .isIso.g (inr (inl x)) = inl (inr x)
  i .snd .isIso.g (inr (inr x)) = inr x

  i .snd .isIso.right-inverse (inl x) = refl
  i .snd .isIso.right-inverse (inr (inl x)) = refl
  i .snd .isIso.right-inverse (inr (inr x)) = refl

  i .snd .isIso.left-inverse (inl (inl x)) = refl
  i .snd .isIso.left-inverse (inl (inr x)) = refl
  i .snd .isIso.left-inverse (inr x) = refl

⊎-zeroʳ : (A ⊎ ⊥) ≃ A
⊎-zeroʳ .fst (inl x) = x
⊎-zeroʳ .snd .isEqv y .centre = inl y , refl
⊎-zeroʳ .snd .isEqv y .paths (inl x , p) i = inl (p (~ i)) , λ j → p (~ i ∨ j)

⊎-zeroˡ : (⊥ ⊎ A) ≃ A
⊎-zeroˡ .fst (inr x) = x
⊎-zeroˡ .snd .isEqv y .centre = inr y , refl
⊎-zeroˡ .snd .isEqv y .paths (inr x , p) i = inr (p (~ i)) , λ j → p (~ i ∨ j)
```