```agda
open import Cat.Prelude
open import Cat.Displayed.Base
open import Cat.Displayed.Cartesian
open import Cat.Displayed.Instances.Family
open import Cat.Displayed.Instances.Pullback
open import Cat.Displayed.Total

open import Data.List

module Theories.Signature where
```

# Multi-Sorted Signatures

A signature is a specification for a "base theory" that we construct
another theory atop of. A signature consists of a type of sorts `S`,
along with a type of "operation symbols" `List S → S → Type`. As an
example, we may have the signature of [groups] with a single sort
$G$, and operation symbols $\cdot : G \times G \to G$, $\epsilon : G$,
and $inv : G \to G$, or the signature of [group actions] which has
an additional sort $X$, and extra operation symbol $G \times X \to X$.

[groups]: Algebra.Group.html
[group actions]: Algebra.Group.Action.html

Note that signatures do *not* include any equations; they simply
describe the the types of formal operations available to us for a given
theory. Signatures form the raw materials for constructing syntax,  and
nothing more.

We take a fibred perspective on signatures, following [@Jacobs].
We first note that signatures are a special type of [family], where
the family is defined over `List S × S` instead of `S`. This situation
can be captured by performing a [change of base] along the functor
`S ↦ List S × S`. We call this functor the context functor, though
this is a bit of a misnomer as it also specifies the return type.

[family]: Cat.Displayed.Instances.Family.html
[change of base]: Cat.Displayed.Instances.Pullback.html

```agda
Ctx : ∀ {ℓ} → Functor (Sets ℓ) (Sets ℓ)
Ctx .Functor.F₀ S = el! (List ∣ S ∣ × ∣ S ∣)
Ctx .Functor.F₁ f (ctx , tp) = map f ctx , f tp
Ctx .Functor.F-id = funext λ t →
  map-id (t .fst) ,ₚ refl
Ctx .Functor.F-∘ f g = funext λ t →
  map-∘ f g (t .fst) ,ₚ refl
```

The (displayed) category of signatures then becomes a one-liner.

```agda
Signatures : ∀ ℓ → Displayed (Sets ℓ) _ _
Signatures ℓ = Change-of-base Ctx (Family (Sets ℓ))
```

Using change of base allows us to easily show that `Signatures`{.Agda}
is a cartesian fibration.

```agda
Signatures-fibration : ∀ {ℓ} → Cartesian-fibration (Signatures ℓ)
Signatures-fibration =
  Change-of-base-fibration Ctx (Family (Sets _)) (Family-is-cartesian (Sets _))
```

## Notation

Constructing signatures using this formulation can be a bit clumsy, so
we define a helper for constructing them.

```agda
private
  module Signatures ℓ = Precategory (∫ (Signatures ℓ))

Sign : ∀ ℓ → Type (lsuc ℓ)
Sign ℓ = Signatures.Ob ℓ

{-# DISPLAY Signatures.Ob ℓ = Sign ℓ #-}

signature : ∀ {ℓ} → (S : Set ℓ) → (Ops : List ∣ S ∣  → ∣ S ∣ → Set ℓ) → Sign ℓ
signature S Ops .fst = S
signature S Ops .snd ctx = Ops (fst ctx) (snd ctx)

module Sign {ℓ} (Sg : Sign ℓ) where
  Sort : Set ℓ
  Sort = fst Sg
  
  Op : List ∣ Sort ∣ → ∣ Sort ∣ → Set ℓ
  Op Γ X = snd Sg (Γ , X)
```

## Single-Sorted Signatures

Those familiar with universal algebra may not be used to this
presentation of signatures. The common approach taken in the literature
is to focus on "single-sorted" signatures, where we only have a single
sort, and the operations have an arity instead a list of input types
and output type. We can recover this notion of signature directly
by using `⊤`{.Agda} as our type of sorts, and then taking the
length of the list of input types as the arity.

```agda
single-sorted : ∀ {ℓ} → (Nat → Set ℓ) → Sign ℓ
single-sorted arity .fst = el! (Lift _ ⊤)
single-sorted arity .snd ctx = arity (length (fst ctx))
```
