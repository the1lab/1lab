<!--
```agda
open import 1Lab.HLevel
open import 1Lab.Equiv
open import 1Lab.Path
open import 1Lab.Type
```
-->

```agda
module Data.Sum.Base where
```

# Sum types {defines="sum-type"}

Sum types are one of the fundamental ingredients of type theory. They
play a dual role to the [[product type]]; if products allow us to state
that we have elements of two types simultaneously, sum types allow us to
state that we have an element of _one_ of two types.

We use the notation `A ⊎ B` to hint at this type's set-theoretic analog:
the disjoint union.

```agda
infixr 3 _⊎_

data _⊎_ {a b} (A : Type a) (B : Type b) : Type (a ⊔ b) where
  inl : A → A ⊎ B
  inr : B → A ⊎ B
```
<!--
```agda
private variable
  a b c d : Level
  A B C D : Type a
```
-->


## Universal properties

One of the most important things about sum types is the following property:
given two functions `A → C` and `B → C`, we can construct a function
`A ⊎ B → C`.

```agda
[_,_] : (A → C) → (B → C) → (A ⊎ B) → C
[ f , g ] (inl x) = f x
[ f , g ] (inr x) = g x
```

<!--
```agda
infix 0 if⁺_then_else_

if⁺_then_else_ : A ⊎ B → C → C → C
if⁺ inl _ then y else n = y
if⁺ inr _ then y else n = n
```
-->

Furthermore, this function is "universal" in the following sense: if we
have some function `h : A ⊎ B → C` that behaves like `f` when provided
an `inl a`, and like `g` when provided `inr b`, then `h` _must_ be
identical to `[ f , g ]`.

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

```agda
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

```agda
  the-iso .fst f = (λ x → f (inl x)) , (λ x → f (inr x))
```

Similarly, given a pair of functions, we can do a case split on the
coproduct to decide which function to apply:

```agda
  the-iso .snd .is-iso.inv (f , g) (inl x) = f x
  the-iso .snd .is-iso.inv (f , g) (inr x) = g x

  the-iso .snd .is-iso.rinv x = refl
  the-iso .snd .is-iso.linv f i (inl x) = f (inl x)
  the-iso .snd .is-iso.linv f i (inr x) = f (inr x)
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

## Closure under equivalences

[Univalence] automatically implies that all type formers respect
equivalences. However, the proof using univalence is restricted to types
of the same universe level. Thus, `⊎-ap`{.Agda}: Coproducts respect
equivalences in both arguments, across levels.

[Univalence]: 1Lab.Univalence.html#the-axiom

```agda
⊎-ap : A ≃ B → C ≃ D → (A ⊎ C) ≃ (B ⊎ D)
⊎-ap (f , f-eqv) (g , g-eqv) = Iso→Equiv cong where
  f-iso = is-equiv→is-iso f-eqv
  g-iso = is-equiv→is-iso g-eqv

  cong : Iso _ _
  cong .fst = ⊎-map f g

  cong .snd .is-iso.inv (inl x) = inl (f-iso .is-iso.inv x)
  cong .snd .is-iso.inv (inr x) = inr (g-iso .is-iso.inv x)

  cong .snd .is-iso.rinv (inl x) = ap inl (f-iso .is-iso.rinv x)
  cong .snd .is-iso.rinv (inr x) = ap inr (g-iso .is-iso.rinv x)

  cong .snd .is-iso.linv (inl x) = ap inl (f-iso .is-iso.linv x)
  cong .snd .is-iso.linv (inr x) = ap inr (g-iso .is-iso.linv x)

⊎-apl : A ≃ B → (A ⊎ C) ≃ (B ⊎ C)
⊎-apl f = ⊎-ap f (id , id-equiv)

⊎-apr : B ≃ C → (A ⊎ B) ≃ (A ⊎ C)
⊎-apr f = ⊎-ap (id , id-equiv) f
```

## Algebraic properties

Considered as an algebraic operator on _types_, the coproduct satisfies
many of the same properties of addition. Specifically, when restricted
to finite types, the coproduct is exactly the same as addition.

```agda
⊎-comm : (A ⊎ B) ≃ (B ⊎ A)
⊎-comm = Iso→Equiv i where
  i : Iso _ _
  i .fst (inl x) = inr x
  i .fst (inr x) = inl x

  i .snd .is-iso.inv (inl x) = inr x
  i .snd .is-iso.inv (inr x) = inl x

  i .snd .is-iso.rinv (inl x) = refl
  i .snd .is-iso.rinv (inr x) = refl
  i .snd .is-iso.linv (inl x) = refl
  i .snd .is-iso.linv (inr x) = refl

⊎-assoc : ((A ⊎ B) ⊎ C) ≃ (A ⊎ (B ⊎ C))
⊎-assoc = Iso→Equiv i where
  i : Iso _ _
  i .fst (inl (inl x)) = inl x
  i .fst (inl (inr x)) = inr (inl x)
  i .fst (inr x)       = inr (inr x)

  i .snd .is-iso.inv (inl x)       = inl (inl x)
  i .snd .is-iso.inv (inr (inl x)) = inl (inr x)
  i .snd .is-iso.inv (inr (inr x)) = inr x

  i .snd .is-iso.rinv (inl x) = refl
  i .snd .is-iso.rinv (inr (inl x)) = refl
  i .snd .is-iso.rinv (inr (inr x)) = refl

  i .snd .is-iso.linv (inl (inl x)) = refl
  i .snd .is-iso.linv (inl (inr x)) = refl
  i .snd .is-iso.linv (inr x) = refl

⊎-zeror : (A ⊎ ⊥) ≃ A
⊎-zeror .fst (inl x) = x
⊎-zeror .snd .is-eqv y .centre = inl y , refl
⊎-zeror .snd .is-eqv y .paths (inl x , p) i = inl (p (~ i)) , λ j → p (~ i ∨ j)

⊎-zerol : (⊥ ⊎ A) ≃ A
⊎-zerol .fst (inr x) = x
⊎-zerol .snd .is-eqv y .centre = inr y , refl
⊎-zerol .snd .is-eqv y .paths (inr x , p) i = inr (p (~ i)) , λ j → p (~ i ∨ j)

⊎-×-distribute : ((A ⊎ B) × C) ≃ ((A × C) ⊎ (B × C))
⊎-×-distribute = Iso→Equiv i where
  i : Iso _ _
  i .fst (inl x , y) = inl (x , y)
  i .fst (inr x , y) = inr (x , y)
  i .snd .is-iso.inv (inl (x , y)) = inl x , y
  i .snd .is-iso.inv (inr (x , y)) = inr x , y
  i .snd .is-iso.rinv (inl x) = refl
  i .snd .is-iso.rinv (inr x) = refl
  i .snd .is-iso.linv (inl x , _) = refl
  i .snd .is-iso.linv (inr x , _) = refl
```
