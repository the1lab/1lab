```agda
open import 1Lab.HLevel.Sets
open import 1Lab.Univalence
open import 1Lab.Type.Dec
open import 1Lab.HLevel
open import 1Lab.Equiv
open import 1Lab.Path
open import 1Lab.Type

open import Agda.Builtin.Bool

open is-equiv
open is-contr
open is-iso

module Data.Bool where

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

## Basic algebraic properties

The booleans form a [Boolean algebra][1], as one might already expect,
given its name. The operations required to define such a structure are
straightforward to define using pattern matching:

```agda
not : Bool → Bool
not true = false
not false = true

and or : Bool → Bool → Bool
and false y = false
and true y = y

or false y = y
or true y = true
```

Pattern matching on only the first argument might seem like a somewhat inpractical choice
due to its asymmetry - however, it shortens a lot of proofs since we get a lot of judgemental
equalities for free. For example, see the following statements:

```agda
and-associative : (x y z : Bool) → and x (and y z) ≡ and (and x y) z
and-associative false y z = refl
and-associative true y z = refl

or-associative : (x y z : Bool) → or x (or y z) ≡ or (or x y) z
or-associative false y z = refl
or-associative true y z = refl

and-commutative : (x y : Bool) → and x y ≡ and y x
and-commutative false false = refl
and-commutative false true = refl
and-commutative true false = refl
and-commutative true true = refl

or-commutative : (x y : Bool) → or x y ≡ or y x
or-commutative false false = refl
or-commutative false true = refl
or-commutative true false = refl
or-commutative true true = refl

and-truer : (x : Bool) → and x true ≡ x
and-truer false = refl
and-truer true = refl

and-falser : (x : Bool) → and x false ≡ false
and-falser false = refl
and-falser true = refl

and-truel : (x : Bool) → and true x ≡ x
and-truel x = refl

or-falser : (x : Bool) → or x false ≡ x
or-falser false = refl
or-falser true = refl

or-truer : (x : Bool) → or x true ≡ true
or-truer false = refl
or-truer true = refl

or-falsel : (x : Bool) → or false x ≡ x
or-falsel x = refl

and-absorbs-orr : (x y : Bool) → and x (or x y) ≡ x
and-absorbs-orr false y = refl
and-absorbs-orr true y = refl

or-absorbs-andr : (x y : Bool) → or x (and x y) ≡ x
or-absorbs-andr false y = refl
or-absorbs-andr true y = refl

and-distrib-orl : (x y z : Bool) → and x (or y z) ≡ or (and x y) (and x z)
and-distrib-orl false y z = refl
and-distrib-orl true y z = refl

or-distrib-andl : (x y z : Bool) → or x (and y z) ≡ and (or x y) (or x z)
or-distrib-andl false y z = refl
or-distrib-andl true y z = refl

and-idempotent : (x : Bool) → and x x ≡ x
and-idempotent false = refl
and-idempotent true = refl

or-idempotent : (x : Bool) → or x x ≡ x
or-idempotent false = refl
or-idempotent true = refl
```

All the properties above hold both in classical and constructive mathematics, even in
*[minimal logic][2]* that fails to validate both the law of the excluded middle as well
as the law of noncontradiction. However, the boolean operations satisfy both of these laws:

```agda
not-involutive : (x : Bool) → not (not x) ≡ x
not-involutive false i = false
not-involutive true i = true

not-and≡or-not : (x y : Bool) → not (and x y) ≡ or (not x) (not y)
not-and≡or-not false y = refl
not-and≡or-not true y = refl

not-or≡and-not : (x y : Bool) → not (or x y) ≡ and (not x) (not y)
not-or≡and-not false y = refl
not-or≡and-not true y = refl

or-complementl : (x : Bool) → or (not x) x ≡ true
or-complementl false = refl
or-complementl true = refl

and-complementl : (x : Bool) → and (not x) x ≡ false
and-complementl false = refl
and-complementl true = refl
```

[1]: <https://en.wikipedia.org/wiki/Boolean_algebra_(structure)> "Boolean algebra"
[2]: <https://en.wikipedia.org/wiki/Minimal_logic> "Minimal logic"

Exclusive disjunction (usually known as *XOR*) also yields additional structure -
in particular, it can be viewed as an addition operator in a ring whose multiplication
is defined by conjunction:

```agda
xor : Bool → Bool → Bool
xor false y = y
xor true y = not y

xor-associative : (x y z : Bool) → xor x (xor y z) ≡ xor (xor x y) z
xor-associative false y z = refl
xor-associative true false z = refl
xor-associative true true z = not-involutive z

xor-commutative : (x y : Bool) → xor x y ≡ xor y x
xor-commutative false false = refl
xor-commutative false true = refl
xor-commutative true false = refl
xor-commutative true true = refl

xor-falser : (x : Bool) → xor x false ≡ x
xor-falser false = refl
xor-falser true = refl

xor-truer : (x : Bool) → xor x true ≡ not x
xor-truer false = refl
xor-truer true = refl

xor-inverse-self : (x : Bool) → xor x x ≡ false
xor-inverse-self false = refl
xor-inverse-self true = refl

and-distrib-xorr : (x y z : Bool) → and (xor x y) z ≡ xor (and x z) (and y z)
and-distrib-xorr false y z = refl
and-distrib-xorr true y false = and-falser (not y) ∙ sym (and-falser y)
and-distrib-xorr true y true = (and-truer (not y)) ∙ ap not (sym (and-truer y))
```

Material implication between booleans also interacts nicely with many of the other operations:

```agda
imp : Bool → Bool → Bool
imp false y = true
imp true y = y

imp-truer : (x : Bool) → imp x true ≡ true
imp-truer false = refl
imp-truer true = refl
```


## Discreteness

Using pattern matching, and the fact that `true isn't false`{.Agda
ident=true≠false}, one can write an algorithm to tell whether or not two
booleans are the same:

```agda
Discrete-Bool : Discrete Bool
Discrete-Bool false false = yes refl
Discrete-Bool false true = no (λ p → true≠false (sym p))
Discrete-Bool true false = no true≠false
Discrete-Bool true true = yes refl

Bool-is-set : is-set Bool
Bool-is-set = Discrete→is-set Discrete-Bool
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

The construction of `not`{.Agda} as an equivalence factors through
showing that `not` is an isomorphism. In particular, `not`{.Agda} is its
own inverse, so we need a proof that it's involutive, as is proven in
`not-involutive`{.Agda}.  With this, we can get a proof that it's an
equivalence:

```agda
not-is-equiv : is-equiv not
not-is-equiv = is-iso→is-equiv (iso not not-involutive not-involutive)
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
          → p ≡ (_ , id-equiv)
  idLemma p p1 p2 = Σ-path (funext lemma) (is-equiv-is-prop _ _ _) where
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
           → p ≡ (not , not-is-equiv)
  notLemma p p1 p2 = Σ-path (funext lemma) (is-equiv-is-prop _ _ _) where
    lemma : (x : Bool) → _
    lemma false = p2
    lemma true = p1
```

With these two lemmas, we can proceed to classify the automorphisms of
`Bool`{.Agda}. For this, we'll need another lemma: If a function `Bool →
Bool` _doesn't_ map `f x ≡ x`, then it maps `f x ≡ not x`.

```agda
Bool-aut≡2 : (Bool ≡ Bool) ≡ Lift _ Bool
Bool-aut≡2 = Iso→Path the-iso where
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
  the-iso .snd .is-iso.inv (lift false) = refl
  the-iso .snd .is-iso.inv (lift true)  = ua (not , not-is-equiv)
```

The inverse is determined by the same rule, but backwards. That's why
it's an inverse! Everything computes in a way that lines up to this
function being a `right inverse`{.Agda ident=is-iso.rinv} on the nose.

```agda
  the-iso .snd .is-iso.rinv (lift false) = refl
  the-iso .snd .is-iso.rinv (lift true) = refl
```

The left inverse is a lot more complicated to prove. We examine how the
path acts on both `true` and `false`. There are four cases:

```agda
  the-iso .snd .is-iso.linv path with Discrete-Bool (transport path true) true
                                     | Discrete-Bool (transport path false) false
  ... | yes true→true | yes false→false =
    refl                  ≡⟨ sym (Path≃Equiv .snd .linv _) ⟩
    ua (path→equiv refl) ≡⟨ ap ua path→equiv-refl ⟩
    ua (_ , id-equiv)      ≡⟨ ap ua (sym (idLemma _ true→true false→false)) ⟩
    ua (path→equiv path) ≡⟨ Path≃Equiv .snd .linv _ ⟩
    path                  ∎
```

In the case where the path quacks like reflexivity, we use the
univalence axiom to show that we must be looking at the reflexivity
path. For this, we use `idLemma` to show that `path→equiv path` must be
the identity equivalence.

```agda
  ... | yes true→true | no false→true' =
    let
      false→true = lemma (transport path) false→true'
      fibres = is-contr→is-prop (path→equiv path .snd .is-eqv true)
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
      fibres = is-contr→is-prop (path→equiv path .snd .is-eqv false)
                              (true , true→false) (false , false→false)
    in absurd (true≠false (ap fst fibres))
```

The other case is analogous.

```agda
  ... | no true→false' | no false→true' =
    ua (not , not-is-equiv) ≡⟨ ap ua (sym (notLemma _
                                            (lemma (transport path) true→false')
                                            (lemma (transport path) false→true')))
                            ⟩
    ua (path→equiv path)  ≡⟨ Path≃Equiv .snd .linv _ ⟩
    path                   ∎
```

The last case is when the path quacks like `ua (not, _)` - in that case,
we use the `notLemma`{.Agda} to show it _must_ be `ua (not, _)`, and the
univalence axiom finishes the job.

<!--
```agda
if : ∀ {ℓ} {A : Type ℓ} → A → A → Bool → A
if x y false = y
if x y true = x

if_then_else_ : ∀ {ℓ} {A : Type ℓ} → Bool → A → A → A
if false then t else f = f
if true then t else f = t
```
-->
