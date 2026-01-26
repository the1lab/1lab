<!--
```agda
open import Prim.Type
```
-->

```agda
module Prim.Interval where
```

# Primitives: The interval

The interval type, and its associated operations, are also very magical.

```agda
{-# BUILTIN CUBEINTERVALUNIV IUniv #-} -- IUniv : SSet₁
{-# BUILTIN INTERVAL I  #-}            -- I : IUniv
```

Note that the interval (as of Agda 2.6.3) is in its own sort, `IUniv`.
The reason for this is that the interval can serve as the _domain_ of
fibrant types:

```agda
_ : Type → Type
_ = λ A → (I → A)
```

The interval has two endpoints, the builtins `IZERO` and `IONE`:

```agda
{-# BUILTIN IZERO    i0 #-}
{-# BUILTIN IONE     i1 #-}
```

It also supports a De Morgan algebra structure. Unlike the other
built-in symbols, the operations on the interval are defined as
`primitive`{.Agda}, so we must use `renaming`{.Agda} to give them usable
names.

```agda
private module X where
  infix  30 primINeg
  infixr 20 primIMin primIMax
  primitive
    primIMin : I → I → I
    primIMax : I → I → I
    primINeg : I → I
open X public
  renaming ( primIMin       to _∧_
           ; primIMax       to _∨_
           ; primINeg       to ~_
           )
```

## The IsOne predicate

To specify the shape of composition problems, Cubical Agda gives us the
predicate `IsOne`{.Agda}, which can be thought of as an embedding
$\bb{I} \mono \Omega$ of the interval object into the subobject
classifier. Of course, we have that `IsOne i0` is uninhabited (since 0
is not 1), but note that [assuming a term in `IsOne i0` collapses the
judgemental equality][sr].

[sr]: https://github.com/agda/agda/issues/6016

```agda
{-# BUILTIN ISONE IsOne #-}  -- IsOne : I → SSet

postulate
  1=1 : IsOne i1
  leftIs1  : ∀ i j → IsOne i → IsOne (i ∨ j)
  rightIs1 : ∀ i j → IsOne j → IsOne (i ∨ j)

{-# BUILTIN ITISONE 1=1  #-}
{-# BUILTIN ISONE1 leftIs1  #-}
{-# BUILTIN ISONE2 rightIs1 #-}
```

The `IsOne`{.Agda} proposition is used as the domain of the type
`Partial`{.Agda}, where `Partial φ A` is a refinement of the type
`.(IsOne φ) → A`, where inhabitants `p, q : Partial φ A` are equal iff
they agree on a decomposition of `φ` into DNF.

```agda
{-# BUILTIN PARTIAL  Partial  #-}
{-# BUILTIN PARTIALP PartialP #-}

postulate
  isOneEmpty : ∀ {ℓ} {A : Partial i0 (Type ℓ)} → PartialP i0 A

primitive
  primPOr : ∀ {ℓ} (i j : I) {A : Partial (i ∨ j) (Type ℓ)}
          → (u : PartialP i (λ z → A (leftIs1 i j z)))
          → (v : PartialP j (λ z → A (rightIs1 i j z)))
          → PartialP (i ∨ j) A

{-# BUILTIN ISONEEMPTY isOneEmpty #-}

syntax primPOr φ ψ u v = [ φ ↦ u , ψ ↦ v ]
```

Note that the type of `primPOr` is incomplete: it looks like the
eliminator for a coproduct, but `i ∨ j` behaves more like a pushout. We
can represent the accurate type with [extension
types](Prim.Extension.html).

<!--
```agda
Partial-map
  : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} {φ : I}
  → (A → B)
  → Partial φ A → Partial φ B
Partial-map f p o = f (p o)
```
-->
