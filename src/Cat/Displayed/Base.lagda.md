<!--
```agda
open import 1Lab.Reflection.HLevel
open import 1Lab.HLevel.Closure
open import 1Lab.Reflection
open import 1Lab.HLevel
open import 1Lab.Path
open import 1Lab.Type hiding (id ; _∘_)

open import Cat.Base
```
-->

```agda
module Cat.Displayed.Base where
```

# Displayed categories {defines=displayed-category}

The core idea behind displayed categories is that we want to capture the
idea of being able to place extra structure over some sort of "base"
category. For instance, we can think of categories of algebraic objects
(monoids, groups, rings, etc) as being extra structure placed atop the
objects of Set, and extra conditions placed atop the morphisms of Set.

We start by defining a displayed category over a base category $\cB$
which will act as the category we add the extra structure to.

```agda
record Displayed {o ℓ} (B : Precategory o ℓ)
                 (o' ℓ' : Level) : Type (o ⊔ ℓ ⊔ lsuc o' ⊔ lsuc ℓ') where
  no-eta-equality
  open Precategory B
```

For each object of the base category, we associate a type of objects.
Going back to our original example of algebraic structures over $\Sets$,
this would be something like `Monoid-on : Set → Type`. This highlights
an important point for intuition: we should think of the objects of the
displayed category as _structures_ over the objects of the base.

```agda
  field
    Ob[_] : Ob → Type o'
```

We do a similar thing for morphisms: For each morphism `f : Hom x y`
in the base category, there is a **set** of morphisms between objects
in the displayed category. Keeping with our running example, given a
function `f : X → Y` and monoid structures `M : Monoid-on X`,
`N : Monoid-on Y`, then `Hom[ f ] M N` is the proposition that "f is a
monoid homomorphism". Again, we should best think of these as
_structures_ over morphisms.

```agda
    Hom[_] : ∀ {x y} → Hom x y → Ob[ x ] → Ob[ y ] → Type ℓ'
    Hom[_]-set : ∀ {a b} (f : Hom a b) (x : Ob[ a ]) (y : Ob[ b ])
               → is-set (Hom[ f ] x y)
```

We also have identity and composition of displayed morphisms, but this
is best thought of as witnessing that the identity morphism in the base
_has_ some structure, and that composition _preserves_ that structure.
For monoids, this would be a proof that the identity function is a
monoid homomorphism, and that the composition of homomorphisms is
indeed a homomorphism.

```agda
    id' : ∀ {a} {x : Ob[ a ]} → Hom[ id ] x x
    _∘'_ : ∀ {a b c x y z} {f : Hom b c} {g : Hom a b}
         → Hom[ f ] y z → Hom[ g ] x y → Hom[ f ∘ g ] x z
```

Now, for the difficult part of displayed category theory: equalities.
If we were to naively try to write out the right-identity law, we would
immediately run into trouble. The problem is that
`f' ∘' id' : Hom[ f ∘ id ] x y`, but `f' : Hom [ f ] x y`! IE: the laws
only hold relative to equalities in the base category. Therefore, instead
of using `_≡_`, we _must_ use `PathP`. Let's provide some helpful
notation for doing so.

```agda
  infixr 40 _∘'_

  _≡[_]_ : ∀ {a b x y} {f g : Hom a b} → Hom[ f ] x y → f ≡ g → Hom[ g ] x y → Type ℓ'
  _≡[_]_ {a} {b} {x} {y} f' p g' = PathP (λ i → Hom[ p i ] x y) f' g'

  infix 30 _≡[_]_
```

Finally, the laws. These are mostly what one would expect, just done
over the equalities in the base.

```agda
  field
    idr' : ∀ {a b x y} {f : Hom a b} → (f' : Hom[ f ] x y) → (f' ∘' id') ≡[ idr f ] f'
    idl' : ∀ {a b x y} {f : Hom a b} → (f' : Hom[ f ] x y) → (id' ∘' f') ≡[ idl f ] f'
    assoc' : ∀ {a b c d w x y z} {f : Hom c d} {g : Hom b c} {h : Hom a b}
           → (f' : Hom[ f ] y z) → (g' : Hom[ g ] x y) → (h' : Hom[ h ] w x)
           → f' ∘' (g' ∘' h') ≡[ assoc f g h ] ((f' ∘' g') ∘' h')
```

For convenience, we also introduce displayed analogues for equational chain reasoning:

```agda
  _∙[]_ : ∀ {a b x y} {f g h : Hom a b} {p : f ≡ g} {q : g ≡ h}
        → {f' : Hom[ f ] x y} {g' : Hom[ g ] x y} {h' : Hom[ h ] x y}
        → f' ≡[ p ] g' → g' ≡[ q ] h' → f' ≡[ p ∙ q ] h'
  _∙[]_ {x = x} {y = y} p' q' = _∙P_ {B = λ f → Hom[ f ] x y} p' q'

  ∙[-]-syntax : ∀ {a b x y} {f g h : Hom a b} (p : f ≡ g) {q : g ≡ h}
        → {f' : Hom[ f ] x y} {g' : Hom[ g ] x y} {h' : Hom[ h ] x y}
        → f' ≡[ p ] g' → g' ≡[ q ] h' → f' ≡[ p ∙ q ] h'
  ∙[-]-syntax {x = x} {y = y} p p' q' = _∙P_ {B = λ f → Hom[ f ] x y} p' q'

  ≡[]⟨⟩-syntax : ∀ {a b x y} {f g h : Hom a b} {p : f ≡ g} {q : g ≡ h}
               → (f' : Hom[ f ] x y) {g' : Hom[ g ] x y} {h' : Hom[ h ] x y}
               → g' ≡[ q ] h' → f' ≡[ p ] g' → f' ≡[ p ∙ q ] h'
  ≡[]⟨⟩-syntax f' q' p' = p' ∙[] q'

  ≡[-]⟨⟩-syntax : ∀ {a b x y} {f g h : Hom a b} (p : f ≡ g) {q : g ≡ h}
               → (f' : Hom[ f ] x y) {g' : Hom[ g ] x y} {h' : Hom[ h ] x y}
               → g' ≡[ q ] h' → f' ≡[ p ] g' → f' ≡[ p ∙ q ] h'
  ≡[-]⟨⟩-syntax f' p q' p' = p' ∙[] q'

  _≡[]˘⟨_⟩_ : ∀ {a b x y} {f g h : Hom a b} {p : g ≡ f} {q : g ≡ h}
            → (f' : Hom[ f ] x y) {g' : Hom[ g ] x y} {h' : Hom[ h ] x y}
            → g' ≡[ p ] f' → g' ≡[ q ] h' → f' ≡[ sym p ∙ q ] h'
  f' ≡[]˘⟨ p' ⟩ q' = symP p' ∙[] q'

  syntax ∙[-]-syntax p p' q' = p' ∙[ p ] q'
  syntax ≡[]⟨⟩-syntax f' q' p' = f' ≡[]⟨ p' ⟩ q'
  syntax ≡[-]⟨⟩-syntax p f' q' p' = f' ≡[ p ]⟨ p' ⟩ q'

  infixr 30 _∙[]_ ∙[-]-syntax
  infixr 2 ≡[]⟨⟩-syntax ≡[-]⟨⟩-syntax _≡[]˘⟨_⟩_
```

<!--
```agda
open hlevel-projection

private
  Hom[]-set
    : ∀ {o ℓ o' ℓ'} {B : Precategory o ℓ} (E : Displayed B o' ℓ') {x y} {f : B .Precategory.Hom x y} {x' y'}
    → is-set (E .Displayed.Hom[_] f x' y')
  Hom[]-set E = E .Displayed.Hom[_]-set _ _ _

instance
  Hom[]-hlevel-proj : hlevel-projection (quote Displayed.Hom[_])
  Hom[]-hlevel-proj .has-level   = quote Hom[]-set
  Hom[]-hlevel-proj .get-level _ = pure (lit (nat 2))
  Hom[]-hlevel-proj .get-argument (_ ∷ _ ∷ _ ∷ _ ∷ _ ∷ arg _ t ∷ _) =
    pure t
  {-# CATCHALL #-}
  Hom[]-hlevel-proj .get-argument _ =
    typeError []

module _ {o ℓ o' ℓ'} {B : Precategory o ℓ} {E : Displayed B o' ℓ'} where
  _ : ∀ {x y} {f : B .Precategory.Hom x y} {x' y'} → is-set (E .Displayed.Hom[_] f x' y')
  _ = hlevel 2
```
-->
