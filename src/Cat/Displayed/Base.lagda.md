<!--
```agda
open import 1Lab.Reflection.HLevel
open import 1Lab.Inductive
open import 1Lab.Path.IdentitySystem
open import 1Lab.HLevel.Closure
open import 1Lab.Reflection
open import 1Lab.HLevel
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
```

<!--
```agda
  hom[_] : ∀ {a b x y} {f g : Hom a b} → f ≡ g → Hom[ f ] x y → Hom[ g ] x y
  hom[ p ] f' = subst (λ h → Hom[ h ] _ _) p f'

  hom[_]⁻ : ∀ {a b x y} {f g : Hom a b} → g ≡ f → Hom[ f ] x y → Hom[ g ] x y
  hom[ p ]⁻ f' = hom[ sym p ] f'

  cast[]
    : ∀ {a b x y} {f g : Hom a b} {f' : Hom[ f ] x y} {g' : Hom[ g ] x y}
    → {p q : f ≡ g}
    → f' ≡[ p ] g'
    → f' ≡[ q ] g'
  cast[] {f = f} {g = g} {f' = f'} {g' = g'} {p = p} {q = q} r =
    coe0→1 (λ i → f' ≡[ Hom-set _ _ f g p q i ] g') r

```
-->

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

# Total categories

```agda
module _ {o ℓ o' ℓ'} {B : Precategory o ℓ} (E : Displayed B o' ℓ') where
  open Precategory B
  open Displayed E

  Total : Type (o ⊔ o')
  Total = Σ[ Carrier ∈ Ob ] Ob[ Carrier ]

  record Total-hom (X Y : Total) : Type (ℓ ⊔ ℓ') where
    constructor total-hom
    field
      hom       : Hom (X .fst) (Y .fst)
      preserves : Hom[ hom ] (X .snd) (Y .snd)

open Total-hom

unquoteDecl H-Level-Total-hom = declare-record-hlevel 2 H-Level-Total-hom (quote Total-hom)

module _ {o ℓ o' ℓ'} {B : Precategory o ℓ} {E : Displayed B o' ℓ'} where
  open Precategory B
  open Displayed E

  total-hom-pathp
    : ∀ {X X' Y Y' : Total E} {f : Total-hom E X Y} {g : Total-hom E X' Y'}
    → (p : X ≡ X') (q : Y ≡ Y')
    → (r : PathP (λ z → Hom (p z .fst) (q z .fst)) (f .hom) (g .hom))
    → PathP (λ z → Hom[ r z ] (p z .snd) (q z .snd)) (f .preserves) (g .preserves)
    → PathP (λ i → Total-hom E (p i) (q i)) f g
  total-hom-pathp p q r s i .hom = r i
  total-hom-pathp p q r s i .preserves = s i

  total-hom-path
    : ∀ {X Y : Total E} {f g : Total-hom E X Y}
    → (p : f .hom ≡ g .hom) → f .preserves ≡[ p ] g .preserves → f ≡ g
  total-hom-path p q = total-hom-pathp refl refl p q

  instance
    Inductive-total-hom-path
      : ∀ {ℓm} {X' Y'} {f g : Total-hom E X' Y'}
      → {p : f .hom ≡ g .hom}
      → ⦃ _ : Inductive (PathP (λ i → Hom[ p i ] (X' .snd) (Y' .snd)) (f .preserves) (g .preserves)) ℓm ⦄
      → Inductive (f ≡ g) ℓm
    Inductive-total-hom-path {p = p} ⦃ ind ⦄ .Inductive.methods = Inductive.methods ind
    Inductive-total-hom-path {p = p} ⦃ ind ⦄ .Inductive.from mthds =
      total-hom-path p (ind .Inductive.from mthds)

    {-# OVERLAPPABLE Inductive-total-hom-path #-}

module _ {o ℓ o' ℓ'} {B : Precategory o ℓ} (E : Displayed B o' ℓ') where
  open Precategory B
  open Displayed E

  ∫ : Precategory (o ⊔ o') (ℓ ⊔ ℓ')
  ∫ .Precategory.Ob = Total E
  ∫ .Precategory.Hom = Total-hom E
  ∫ .Precategory.Hom-set _ _ = hlevel 2
  ∫ .Precategory.id .hom = id
  ∫ .Precategory.id .preserves = id'
  ∫ .Precategory._∘_ f g .hom = f .hom ∘ g .hom
  ∫ .Precategory._∘_ f g .preserves = f .preserves ∘' g .preserves
  ∫ .Precategory.idr _ = total-hom-path (idr _) (idr' _)
  ∫ .Precategory.idl _ = total-hom-path (idl _) (idl' _)
  ∫ .Precategory.assoc _ _ _ = total-hom-path (assoc _ _ _) (assoc' _ _ _)
```
