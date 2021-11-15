```
module 1Lab.Type where
```

# Universes

A **universe** is a type whose inhabitants are types. In Agda, there is
a family of universes, which, by default, is called `Set`. Rather
recently, Agda gained [a flag] to make `Set` not act like a keyword, and
allow renaming it by an import declaration from the [Agda
primitives] module.

[Agda primitives]: agda://Agda.Primitive

[a flag]: https://agda.readthedocs.io/en/v2.6.2/language/built-ins.html?highlight=no-import-sorts#sorts

```
open import Agda.Primitive renaming (Set to Type) public
```

`Type`{.Agda} is, of course, a type itself, so it's a natural question
to ask: does it belong to a universe? The answer is _yes_. However, Type
can not belong to itself, or we could reproduce Russell's Paradox, as is
done [in this module].

[in this module]: agda://1Lab.Counterexamples.Russell

To prevent this, the universes are parametrised by a _`Level`{.Agda}_,
where the collection of all `ℓ`-sized types is `Type (lsuc ℓ)`:

```
_ : (ℓ : Level) → Type (lsuc ℓ)
_ = λ ℓ → Type ℓ

level-of : {ℓ : Level} → Type ℓ → Level
level-of {ℓ} _ = ℓ
```

## Built-in Types

Agda comes with built-in definitions for a bunch of types:

```
open import Agda.Builtin.Sigma hiding (Σ) public
open import Agda.Builtin.Unit public
open import Agda.Builtin.Bool public
open import Agda.Builtin.Nat public
```

It does not, however, come with a built-in definition of the empty type:

```
data ⊥ {ℓ : _} : Type ℓ where

absurd : {ℓ ℓ₁ : _} {A : Type ℓ₁} → ⊥ {ℓ} → A
absurd ()
```

The dependent sum of a family of types is notated by `Σ`{.Agda}. The
domain of the family is left implicit. We use a notation for when it
must be made explicit.

```
Σ : {a b : _} {A : Type a} (B : A → Type b) → Type _
Σ = Agda.Builtin.Sigma.Σ _

Σ-syntax = Σ
syntax Σ-syntax {A = A} (λ x → B) = Σ[ x ∈ A ] B
```