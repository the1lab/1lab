<!--
```agda
open import 1Lab.Prelude

open import Data.Dec.Base
open import Data.Sum.Base
open import Data.Id.Base

open is-equiv
open is-contr
open is-iso
```
-->

```agda
module Data.Bool where
```

# The booleans {defines="boolean"}

```agda
open import Data.Bool.Base public
```

Pattern matching on only the first argument might seem like a somewhat impractical choice
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

and-distrib-orr : (x y z : Bool) → and (or x y) z ≡ or (and x z) (and y z)
and-distrib-orr true y z =
  sym (or-absorbs-andr z y) ∙ ap (or z) (and-commutative z y)
and-distrib-orr false y z = refl

or-distrib-andr : (x y z : Bool) → or (and x y) z ≡ and (or x z) (or y z)
or-distrib-andr true y z = refl
or-distrib-andr false y z =
  sym (and-absorbs-orr z y) ∙ ap (and z) (or-commutative z y)
```

<!--
```agda
and-reflect-true-l : ∀ {x y} → and x y ≡ true → x ≡ true
and-reflect-true-l {x = true} p = refl
and-reflect-true-l {x = false} p = p

and-reflect-true-r : ∀ {x y} → and x y ≡ true → y ≡ true
and-reflect-true-r {x = true} {y = true} p = refl
and-reflect-true-r {x = false} {y = true} p = refl
and-reflect-true-r {x = true} {y = false} p = p
and-reflect-true-r {x = false} {y = false} p = p

or-reflect-true : ∀ {x y} → or x y ≡ true → x ≡ true ⊎ y ≡ true
or-reflect-true {x = true} {y = y} p = inl refl
or-reflect-true {x = false} {y = true} p = inr refl
or-reflect-true {x = false} {y = false} p = absurd (true≠false (sym p))

or-reflect-false-l : ∀ {x y} → or x y ≡ false → x ≡ false
or-reflect-false-l {x = true} p = absurd (true≠false p)
or-reflect-false-l {x = false} p = refl

or-reflect-false-r : ∀ {x y} → or x y ≡ false → y ≡ false
or-reflect-false-r {x = true} {y = true} p = absurd (true≠false p)
or-reflect-false-r {x = true} {y = false} p = refl
or-reflect-false-r {x = false} {y = true} p = absurd (true≠false p)
or-reflect-false-r {x = false} {y = false} p = refl

and-reflect-false : ∀ {x y} → and x y ≡ false → x ≡ false ⊎ y ≡ false
and-reflect-false {x = true} {y = y} p = inr p
and-reflect-false {x = false} {y = y} p = inl refl
```
-->

All the properties above hold both in classical and constructive mathematics, even in
*[minimal logic][2]* that fails to validate both the law of the excluded middle as well
as the law of noncontradiction. However, the boolean operations satisfy both of these laws:

```agda

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

Furthermore, note that `not`{.Agda} has no fixed points.

```agda
not-no-fixed : ∀ {x} → x ≡ not x → ⊥
not-no-fixed {x = true} p = absurd (true≠false p)
not-no-fixed {x = false} p = absurd (true≠false (sym p))
```

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

Furthermore, material implication is equivalent to the classical definition.

```agda
imp-not-or : ∀ x y → or (not x) y ≡ imp x y
imp-not-or false y = refl
imp-not-or true y = refl
```

<!--
```agda
not-inj : ∀ {x y} → not x ≡ not y → x ≡ y
not-inj {x = true}  {y = true}  p = refl
not-inj {x = true}  {y = false} p = sym p
not-inj {x = false} {y = true}  p = sym p
not-inj {x = false} {y = false} p = refl

ne→is-not : ∀ {x y} → x ≠ y → x ≡ not y
ne→is-not {true}  {true}  p = absurd (p refl)
ne→is-not {true}  {false} p = refl
ne→is-not {false} {true}  p = refl
ne→is-not {false} {false} p = absurd (p refl)
```
-->

## Aut(Bool)

We characterise the type `Bool ≡ Bool`. There are exactly two paths, and
we can decide which path we're looking at by seeing how it acts on the
element `true`{.Agda}.

First, two small lemmas: we can tell whether we're looking at the
identity equivalence or the "not" equivalence by seeing how it acts on
the constructors.

```agda
module _ (e : Bool ≃ Bool) where
  private module e = Equiv e

  bool-equiv-id : ∀ x y → e.to x ≡ x → e.to y ≡ y
  bool-equiv-id true  true  α = α
  bool-equiv-id false false α = α
  bool-equiv-id true  false α with e.to false in β
  ... | false = refl
  ... | true  = absurd (true≠false (e.injective₂ α (Id≃path.to β)))
  bool-equiv-id false true α with e.to true in β
  ... | false = absurd (false≠true (e.injective₂ α (Id≃path.to β)))
  ... | true  = refl

  bool-equiv-not : ∀ x y → e.to x ≡ not x → e.to y ≡ not y
  bool-equiv-not true  true  α = α
  bool-equiv-not false false α = α
  bool-equiv-not true  false α with e.to false in β
  ... | true  = refl
  ... | false = absurd (true≠false (e.injective₂ α (Id≃path.to β)))
  bool-equiv-not false true  α with e.to true in β
  ... | false = refl
  ... | true  = absurd (false≠true (e.injective₂ α (Id≃path.to β)))

  bool-equiv-not' : ∀ x y → e.to x ≠ x → e.to y ≡ not y
  bool-equiv-not' x y α = bool-equiv-not x y (ne→is-not α)
```

```agda
private
  classify : Bool ≃ Bool → Bool
  classify e with e .fst true ≡? true
  ... | yes _ = true
  ... | no  _ = false

  named : Bool → Bool ≃ Bool
  named = if_then id≃ else not≃

  classify-named : (x : Bool) → classify (named x) ≡ x
  classify-named true  = refl
  classify-named false = refl

  named-classify : (e : Bool ≃ Bool) → ∀ x → named (classify e) .fst x ≡ e .fst x
  named-classify e x with e .fst true ≡? true
  ... | yes p = sym (bool-equiv-id e true x p)
  ... | no ¬p = sym (bool-equiv-not e true x (ne→is-not ¬p))


Bool-automorphisms : (Bool ≃ Bool) ≃ Bool
Bool-automorphisms .fst = classify
Bool-automorphisms .snd = is-iso→is-equiv record
  { from = named
  ; rinv = classify-named
  ; linv = λ e → Σ-pathp (funext (named-classify e))
    (is-prop→pathp (λ _ → is-equiv-is-prop _) _ _)
  }

Bool-equiv-elim : ∀ {ℓ} (P : Bool ≃ Bool → Type ℓ) → P id≃ → P not≃ → ∀ e → P e
Bool-equiv-elim P pid pnot e with inspect (e .fst true)
... | true  , p = subst P (ext λ x → sym (bool-equiv-id  e true x p))  pid
... | false , p = subst P (ext λ x → sym (bool-equiv-not e true x p)) pnot
```
