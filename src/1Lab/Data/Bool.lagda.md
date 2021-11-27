```agda
open import 1Lab.Univalence
open import 1Lab.Data.Dec
open import 1Lab.HLevel
open import 1Lab.Equiv
open import 1Lab.Path
open import 1Lab.Type

open import Agda.Builtin.Bool

open isEquiv
open isContr
open isIso

module 1Lab.Data.Bool where

open Agda.Builtin.Bool public
```

# The Booleans

The type of booleans is interesting in homotopy type theory because it
is the simplest type where its automorphisms in `Type`{.Agda} are
non-trivial. In particular, there are two: negation, and the identity.

But first, true isn't false.

```agda
true≠false : true ≡ false → ⊥
true≠false p = subst P p tt where
  P : Bool → Type
  P false = ⊥
  P true = ⊤
```

It's worth noting how to prove two things are **not** equal. We write a
predicate that distinguishes them by mapping one to `⊤`{.Agda}, and one
to `⊥`{.Agda}. Then we can substitute under P along the claimed equality
to get an element of `⊥`{.Agda} - a contradiction.

## Discreteness

It's quite easy to tell whether two booleans are equal:

```agda
Discrete-Bool : Discrete Bool
Discrete-Bool false false = yes refl
Discrete-Bool false true = no (λ p → true≠false (sym p))
Discrete-Bool true false = no true≠false
Discrete-Bool true true = yes refl
```

Furthermore, if we know we're not looking at true, then we must be
looking at false, and vice-versa:

```agda
x≠true→x≡false : (x : Bool) → (x ≡ true → ⊥) → x ≡ false
x≠true→x≡false false p = refl
x≠true→x≡false true p = absurd (p refl)

x≠false→x≡true : (x : Bool) → (x ≡ false → ⊥) → x ≡ true
x≠false→x≡true false p = absurd (p refl)
x≠false→x≡true true p = refl
```

## The "not" equivalence

```agda
not : Bool → Bool
not true = false
not false = true
```

The construction of `not`{.Agda} as an equivalence factors through
showing that `not` is an isomorphism. In particular, `not`{.Agda} is its
own inverse, so we just need a proof that it's involutive:

```agda
not-involutive : (x : Bool) → not (not x) ≡ x
not-involutive false i = false
not-involutive true i = true
```

With this, we can get a proof that it's an equivalence:

```agda
isEquiv-not : isEquiv not
isEquiv-not = isIso→isEquiv (iso not not-involutive not-involutive)
```

## Aut(Bool)

We characterise the type `Bool ≡ Bool`. There are exactly two paths, and
we can decide which path we're looking at by seeing how it acts on the
element `true`{.Agda}.

First, two small lemmas: we can tell whether we're looking at the
identity equivalence or the "not" equivalence by seeing how it acts on
the constructors.

```agda
private
  idLemma : (p : Bool ≃ Bool)
          → p .fst true ≡ true
          → p .fst false ≡ false
          → p ≡ (_ , idEquiv)
  idLemma p p1 p2 = Σ-Path (funext lemma) (isProp-isEquiv _ _ _) where
    lemma : (x : Bool) → _
    lemma false = p2
    lemma true = p1
```

If it quacks like the identity equivalence, then it must be. Otherwise
we're looking at the `not`{.Agda} equivalence.

```agda
  notLemma : (p : Bool ≃ Bool)
           → p .fst true ≡ false
           → p .fst false ≡ true
           → p ≡ (not , isEquiv-not)
  notLemma p p1 p2 = Σ-Path (funext lemma) (isProp-isEquiv _ _ _) where
    lemma : (x : Bool) → _
    lemma false = p2
    lemma true = p1
```

With these two lemmas, we can proceed to classify the automorphisms of
`Bool`{.Agda}. For this, we'll need another lemma: If a function `Bool →
Bool` _doesn't_ map `f x ≡ x`, then it maps `f x ≡ not x`.

```agda
AutBool≡2 : (Bool ≡ Bool) ≡ Lift _ Bool
AutBool≡2 = Iso→path the-iso where
  lemma : (f : Bool → Bool) {x : Bool} → (f x ≡ x → ⊥) → f x ≡ not x
  lemma f {false} x with Discrete-Bool (f false) true
  lemma f {false} x | yes p = p
  lemma f {false} x | no ¬p = absurd (¬p (x≠false→x≡true _ x))

  lemma f {true} x with Discrete-Bool (f true) false
  lemma f {true} x | yes p = p
  lemma f {true} x | no ¬p = absurd (¬p (x≠true→x≡false _ x))
```

This lemma is slightly annoying to prove, but it's not too complicated.
It's essentially two case splits: first on the boolean, and second on
whether we're looking at `f x ≡ not x`. If we are, then it's fine (those
are the `yes p = p` cases) - otherwise that contradicts what we've been told.

```agda
  the-iso : Iso (Bool ≡ Bool) (Lift _ Bool)

  fst the-iso path with Discrete-Bool (transport path true) true
  ... | yes path = lift false
  ... | no ¬path = lift true
```

Now we classify the isomorphism by looking at what it does to
`true`{.Agda}. We arbitrarily map `refl`{.Agda} to `false`{.Agda} and
`not`{.Agda} to `true`{.Agda}.

```agda
  g (snd the-iso) (lift false) = refl
  g (snd the-iso) (lift true)  = ua (not , isEquiv-not)
```

The inverse is determined by the same rule, just backwards. That's why
it's an inverse! Everything computes in a way that lines up to this
function being a `right-inverse`{.Agda} on the nose.

```agda
  right-inverse (snd the-iso) (lift false) = refl
  right-inverse (snd the-iso) (lift true) = refl
```

The left inverse is a lot more complicated to prove. We examine how the
path acts on both `true` and `false`. There are four cases:

```agda
  left-inverse (snd the-iso) path with Discrete-Bool (transport path true) true
                                     | Discrete-Bool (transport path false) false
  ... | yes true→true | yes false→false =
    refl                  ≡⟨ sym (univalence-Iso .snd .left-inverse _) ⟩
    ua (pathToEquiv refl) ≡⟨ ap ua pathToEquiv-refl ⟩
    ua (_ , idEquiv)      ≡⟨ ap ua (sym (idLemma _ true→true false→false)) ⟩
    ua (pathToEquiv path) ≡⟨ univalence-Iso .snd .left-inverse _ ⟩
    path                  ∎
```

In the case where the path quacks like reflexivity, we use the
univalence axiom to show that we must be looking at the reflexivity
path. For this, we use `idLemma` to show that `pathToEquiv path` must be
the identity equivalence.

```agda
  ... | yes true→true | no false→true' =
    let
      false→true = lemma (transport path) false→true'
      fibres = isContr→isProp (pathToEquiv path .snd .isEqv true)
                              (true , true→true) (false , false→true)
    in absurd (true≠false (ap fst fibres))
```

The second case is when both booleans map to `true`{.Agda}. This is a
contradiction - transport along a path is an equivalence, and
equivalences have contractible fibres; Since we have two fibres over
`true`{.Agda}, that means we must have `true ≡ false`.

```agda
  ... | no true→false' | yes false→false =
    let
      true→false = lemma (transport path) true→false'
      fibres = isContr→isProp (pathToEquiv path .snd .isEqv false)
                              (true , true→false) (false , false→false)
    in absurd (true≠false (ap fst fibres))
```

The other case is analogous.

```agda
  ... | no x  | no x₁  =
    ua (not , isEquiv-not) ≡⟨ ap ua (sym (notLemma _ (lemma (transport path) x)
                                                     (lemma (transport path) x₁)))
                            ⟩
    ua (pathToEquiv path)  ≡⟨ univalence-Iso .snd .left-inverse _ ⟩
    path                   ∎
```

The last case is when the path quacks like `ua (not, _)` - in that case,
we use the `notLemma`{.Agda} to show it _must_ be `ua (not, _)`, and the
univalence axiom finishes the job.
