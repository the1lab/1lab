pattern [_] z = z ∷ []
pattern [_,_] y z = y ∷ z ∷ []
pattern [_,_,_] x y z = x ∷ y ∷ z ∷ []
pattern [_,_,_,_] w x y z = w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_] v w x y z = v ∷ w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_,_] u v w x y z = u ∷ v ∷ w ∷ x ∷ y ∷ z ∷ []
```agda
module 1Lab.Prim.Type where
```

# Primitives: Sorts

This module defines bindings for the primitive sorts in Agda. These are
_very magic_ symbols since they bootstrap everything about the type
system. For more details about the use of universes, see
[`1Lab.Type`](1Lab.Type.html).

```agda
{-# BUILTIN TYPE Type #-}
{-# BUILTIN PROP Prop #-}
{-# BUILTIN SETOMEGA Typeω #-}
{-# BUILTIN STRICTSET SSet #-}
{-# BUILTIN STRICTSETOMEGA SSetω #-}
```

Additionally, we have the `Level` type, of _universe levels_. The
universe levels are an algebra containing 0, closed under successor and
maximum. The difference between this and e.g. the natural numbers is
that `Level` isn't _initial_, i.e. you can't pattern-match on it.

```agda
postulate
  Level : Type
  lzero : Level
  lsuc  : Level → Level
  _⊔_   : Level → Level → Level
infixl 6 _⊔_

{-# BUILTIN LEVEL Level #-}
{-# BUILTIN LEVELZERO lzero #-}
{-# BUILTIN LEVELSUC lsuc #-}
{-# BUILTIN LEVELMAX _⊔_ #-}
```
