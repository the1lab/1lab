```agda
open import Cat.Functor.Adjoint
open import Cat.Functor.Base
open import Cat.Prelude

open Functor
open _=>_

module Cat.Monad {o h : _} {C : Precategory o h} where

import Cat.Reasoning C as C
```

# Monads

A **monad on a category** $\ca{C}$ is one way of categorifying the
concept of [monoid]. Specifically, rather than living in a monoidal
category, a monad lives in a bicategory. Here, we concern ourselves with
the case of monads in the bicategory of categories, so that we may say:
A monad is an endofunctor $M$, equipped with a `unit`{.Agda} natural
transformation $\mathrm{Id} \To M$, and a `multiplication`{.Agda
ident=mult} $(M \circ M) \To M$.

[monoid]: Algebra.Monoid.html

```
record Monad : Type (o ⊔ h) where
  no-eta-equality
  field
    M    : Functor C C
    unit : Id => M
    mult : (M F∘ M) => M
  
  module unit = _=>_ unit
  module mult = _=>_ mult
  
  M₀ = F₀ M
  M₁ = F₁ M
  M-id = F-id M
  M-∘ = F-∘ M
```

Furthermore, these natural transformations must satisfy identity and
associativity laws exactly analogous to those of a monoid.

```
  field
    left-ident  : ∀ {x} → mult.η x C.∘ M₁ (unit.η x) ≡ C.id
    right-ident : ∀ {x} → mult.η x C.∘ unit.η (M₀ x) ≡ C.id
  
  field
    mult-assoc : ∀ {x} → mult.η x C.∘ M₁ (mult.η x) ≡ mult.η x C.∘ mult.η (M₀ x)
```

# Algebras over a monad

One way of interpreting a monad $M$ is as giving a _signature_ for an
algebraic theory. For instance, the free monoid monad describes the 
signature for the theory of monoids, and the [free group] monad
describes the theory of groups. 

Under this light, an **algebra over a monad** is a way of _evaluating_
the abstract operations given by a monadic expression to a concrete
value. Formally, an algebra for $M$ is given by a choice of object $A$
and a morphism $\nu : M(A) \to A$.

[free group]: Algebra.Group.Free.html

```agda
record AlgebraOn (M : Monad) (ob : C.Ob) : Type (o ⊔ h) where
  no-eta-equality
  open Monad M

  field
    ν : C.Hom (M₀ ob) ob
```

This morphism must satisfy equations categorifying those which define a
monoid action. If we think of $M$ as specifying a signature of
_effects_, then `v-unit`{.Agda} says that the `unit`{.Agda} has no
effects, and `v-mult`{.Agda} says that, given two layers $M(M(A))$, it
doesn't matter whether you first join then evaluate, or evaluate twice.

```
    ν-unit : ν C.∘ unit.η ob ≡ C.id
    ν-mult : ν C.∘ M₁ ν ≡ ν C.∘ mult.η ob

Algebra : Monad → Type (o ⊔ h)
Algebra M = Σ (AlgebraOn M)
```

# Eilenberg-Moore Category

There is a natural definition of $M$-algebra homomorphism: It is a map
of the underlying objects of each algebra which commutes with the
evaluation operation.

```agda
record AlgebraHom (M : Monad) (X Y : Algebra M) : Type (o ⊔ h) where
  no-eta-equality
  private
    module X = AlgebraOn (X .snd)
    module Y = AlgebraOn (Y .snd)

  open Monad M

  field
    morphism : C.Hom (X .fst) (Y .fst)
    commutes : morphism C.∘ X.ν ≡ Y.ν C.∘ M₁ morphism

open AlgebraHom
```

Since `commutes`{.Agda} is an inhabitant of a proposition, it suffices
to test equality of the underlying morphisms to conclude that two
algebra homomorphisms are equal.

```
AlgebraHom-path : {M : Monad} {X Y : Algebra M} {F G : AlgebraHom M X Y}
                → morphism F ≡ morphism G
                → F ≡ G
AlgebraHom-path x i .morphism = x i
AlgebraHom-path {M = M} {X} {Y} {F} {G} x i .commutes = 
  isProp→PathP (λ i → C.Hom-set _ _ (x i C.∘ X .snd .AlgebraOn.ν) 
                                    (Y .snd .AlgebraOn.ν C.∘ Monad.M₁ M (x i)))
    (F .commutes) (G .commutes) i
```

These naturally assemble into a category, the `Eilenberg-Moore`{.Agda}
category of $M$, denoted $C^M$.

```agda
module _ (M : Monad) where
  private
    module M = Monad M
  open M hiding (M)
  open Precategory
  open AlgebraOn

  Eilenberg-Moore : Precategory _ _
  Eilenberg-Moore .Ob = Algebra M
  Eilenberg-Moore .Hom X Y = AlgebraHom M X Y

  Eilenberg-Moore .id {o , x} =
    record
      { morphism = C.id
      ; commutes = C.id C.∘ ν x     ≡⟨ C.id-comm-sym ⟩
                   ν x C.∘ C.id     ≡⟨ ap (C._∘_ _) (sym M-id) ⟩
                   ν x C.∘ M₁ C.id  ∎
      }

  Eilenberg-Moore ._∘_ {_ , x} {_ , y} {_ , z} F G =
    record 
      { morphism = morphism F C.∘ morphism G
      ; commutes = (morphism F C.∘ morphism G) C.∘ ν x            ≡⟨ C.extendr (commutes G) ⟩
                   (morphism F C.∘ ν y) C.∘ M₁ (morphism G)       ≡⟨ ap₂ C._∘_ (commutes F) refl ⟩
                   (ν z C.∘ M₁ (morphism F)) C.∘ M₁ (morphism G)  ≡⟨ C.pullr (sym (M-∘ _ _)) ⟩
                   ν z C.∘ M₁ (morphism F C.∘ morphism G)         ∎
      }

  Eilenberg-Moore .idr f = AlgebraHom-path (C.idr (morphism f))
  Eilenberg-Moore .idl f = AlgebraHom-path (C.idl (morphism f))
  Eilenberg-Moore .assoc f g h = AlgebraHom-path (C.assoc _ _ _)
  Eilenberg-Moore .Hom-set X Y = hl where abstract
    module X = AlgebraOn (X .snd)
    module Y = AlgebraOn (Y .snd)

    T : Type h
    T = Σ[ h ∈ _ ] (h C.∘ X.ν ≡ Y.ν C.∘ M₁ h)

    unpack : T → AlgebraHom M X Y
    unpack (h , x) .morphism = h
    unpack (h , x) .commutes = x

    pack : AlgebraHom M X Y → T
    pack x = x .morphism , x .commutes

    unpack∘pack : isLeftInverse unpack pack
    unpack∘pack x i .morphism = x .morphism
    unpack∘pack x i .commutes = x .commutes

    hl : isSet (AlgebraHom M X Y)
    hl = isHLevel-retract 2 unpack pack unpack∘pack 
      (isHLevelΣ 2 (C.Hom-set _ _) λ _ → isProp→isSet (C.Hom-set _ _ _ _))
```

There is an evident functor from $C^M$ back into C.

```
  Forget : Functor Eilenberg-Moore C
  Forget .F₀ = fst
  Forget .F₁ = AlgebraHom.morphism
  Forget .F-id = refl
  Forget .F-∘ f g = refl
```

This functor is faithful exactly by our characterisation of equality of
algebra homomorphisms.

```
  Forget-faithful : isFaithful Forget
  Forget-faithful proof = AlgebraHom-path proof
```

## Free Algebras

For every object $A$, there is a _free_ $M$-algebra, where the
underlying object is $M(A)$ and the action is multiplication.

```
  Free : Functor C Eilenberg-Moore
  Free .F₀ A = M₀ A ,
    record
      { ν      = mult.η A
      ; ν-mult = mult-assoc
      ; ν-unit = right-ident
      }
```

The functorial action of the free $M$-algebra construction is given by
the action of $M$, which commutes with the action since $M$'s
multiplication is a natural transformation.

```
  Free .F₁ f =
    record
      { morphism = M₁ f
      ; commutes = sym (mult.is-natural _ _ _)
      }
  Free .F-id = AlgebraHom-path M-id
  Free .F-∘ f g = AlgebraHom-path (M-∘ f g)
```

This is a free construction in the precise sense of the word: it's left
adjoint to a forgetful functor.

```
  open _⊣_

  Free⊣Forget : Free ⊣ Forget
  Free⊣Forget .unit = NT (λ x → M.unit.η x) λ x y f → M.unit.is-natural _ _ _
  Free⊣Forget .counit .η x =
    record { morphism = x .snd .ν
           ; commutes = sym (x .snd .ν-mult)
           }
  Free⊣Forget .counit .is-natural x y f = AlgebraHom-path (sym (commutes f)) 
  Free⊣Forget .zig = AlgebraHom-path left-ident
  Free⊣Forget .zag {x} = x .snd .ν-unit
```
