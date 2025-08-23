<!--
```agda
open import 1Lab.Prelude

open import Data.Partial.Total
open import Data.Partial.Base
open import Data.Fin.Base hiding (_<_ ; _≤_)
open import Data.Vec.Base

open import Realisability.PCA
```
-->

```agda
module Realisability.PCA.Combinatorial where
```

# Combinatorial bases for PCAs {defines="combinatorially-complete"}

<!--
```agda
private variable
  ℓ : Level
  A : Type ℓ
  n : Nat
```
-->

Traditional introductions to realisability (e.g. de Jong's
[-@deJong:Realisability] or Bauer's [-@Bauer:Realisability]) introduce
[[partial combinatory algebras]] in terms of *combinators*, elements
$\tt{K}$ and $\tt{S}$ satisfying the rules $\tt{K}\ a\ b = a$ and
$\tt{S}\ f\ g\ x = f\ x\ (g\ x)$. Unfortunately, working with this
notion of pca in Agda is very inconvenient:

* To start with, we have to explicitly write out the requirements
  that the constants $\tt{K}$ and $\tt{S}$ are defined; and that the
  application $\tt{K}\ a$ is defined when $a$ is defined, and similarly
  for $\tt{S}\ f$, $\tt{S}\ g$, and $\tt{S}\ f\ g$.

* Because we generally write programs using [[functional
  notation|syntax sugar for pcas]], it is important that the normal form
  of a program like $\langle x \rangle \langle y \rangle\ y$
  is compact, both for performance reasons and so that we can actually
  work with them. However, the normal forms of programs in terms of
  combinators are huge monsters.

* On a more technical point, it's good for type inference if, when
  working against an abstract PCA $\bA$, we have that the application
  function `_%_` *and* the abstraction function `abs` are both
  *definitionally injective* --- which, if they are record fields, they
  will be; but a concrete implementation of `abs`{.Agda}, like below,
  will generally fail this.

  This could be solved by making `abs`{.Agda} into an `opaque`{.kw}
  function, but then Agda would be unable to compute how `abs`{.Agda}
  and `inst`{.Agda} interact, making it hard to apply the computation
  rule for an abstraction.

Therefore, we prefer to define pcas to have an abstraction elimination
function. But the $\tt{S}$ and $\tt{K}$ combinators are still important,
for example when equipping a type with a pca structure. This module is
dedicated to proving that if we *have* the combinators $\tt{S}$ and
$\tt{K}$, then we can get out a pca structure. First, we write out the
actual battery of conditions lined out in our first complaint:

```agda
record has-ski (_%_ : ↯ A → ↯ A → ↯ A) : Type (level-of A) where
  field
    K S : ↯ A

    K↓ : ⌞ K ⌟
    S↓ : ⌞ S ⌟

    K↓₁ : ∀ {x}   → ⌞ x ⌟ → ⌞ K % x ⌟
    K-β : ∀ {x y} → ⌞ x ⌟ → ⌞ y ⌟ → (K % x) % y ≡ x

    S↓₁ : ∀ {f}     → ⌞ f ⌟                 → ⌞ S % f ⌟
    S↓₂ : ∀ {f g}   → ⌞ f ⌟ → ⌞ g ⌟         → ⌞ (S % f) % g ⌟
    S-β : ∀ {f g x} → ⌞ f ⌟ → ⌞ g ⌟ → ⌞ x ⌟ → ((S % f) % g) % x ≡ ((f % x) % (g % x))
```

Note that this isn't the only set of combinators that results in a pca,
and keep in mind that the combinators themselves need not be unique. We
say that a set of combinators which can be used to build an abstraction
procedure is **combinatorially complete**.

<!--
```agda
module _ {A : Type ℓ} {_%_ : ↯ A → ↯ A → ↯ A} (pca : has-ski _%_) (let infixl 8 _%_; _%_ = _%_) where
  open has-ski pca
  open eval _%_
```
-->

We start by naming some useful terms. First, since $\tt{K}$ and $\tt{S}$
are both defined, we can make them into terms; Furthermore, we can show
that $\tt{S}\ \tt{K}\ \tt{K}$ is defined, and we make *it* into a term
we refer to as $\tt{I}$.

```agda
  private
    i : ↯ A
    i = (S % K) % K

    `K `S `I : ∀ {n} → Term A n
    `K = const (K , K↓)
    `S = const (S , S↓)
    `I = const (i , S↓₂ K↓ K↓)
```

Now suppose that we have a term in $n + 1$ variables, say $\{x, ...\}$,
and we want to abstract over $x$, making it into a term of $n$ variables
which is a "function of $x$". We do this by cases. First, abstracting
over $x$ in $x$ itself gives the identity function, while other
variables are shifted down by one position and guarded by the $\tt{K}$
combinator.

```agda
    abs : Term A (suc n) → Term A n
    abs (var n) with fin-view n
    ... | zero  = `I
    ... | suc i = app `K (var i)
```

These satisfy $\tt{I}\ x = x$ and $\tt{K}\ y\ x = a$, as required.
Arbitrary constants $t$ are also guarded by the $\tt{K}$ combinator,
since they are independent of the new argument. Finally, for a complex
term like $f\ y$, we first abstract over $x$ in the subterms $f$ and
$y$, and combine the results using $\tt{S}$:

```agda
    abs (const t) = app `K (const t)
    abs (app f x) = app (app `S (abs f)) (abs x)
```

This last case shows that the $\tt{S}$ combinator serves to "share" the
new variable among the subterms. We've already argued that the result of
abstracting over $x$ in a variable is defined; these latter two cases
are similarly easy.

```agda
    abs↓ : (t : Term A (suc n)) (ρ : Vec (↯⁺ A) n) → ⌞ eval (abs t) ρ ⌟
    abs↓ (var n) ρ with fin-view n
    ... | zero  = S↓₂ K↓ K↓
    ... | suc i = K↓₁ (lookup ρ i .snd)
    abs↓ (const x) ρ = K↓₁ (x .snd)
    abs↓ (app f x) ρ = S↓₂ (abs↓ f ρ) (abs↓ x ρ)
```

Finally, we must prove that `abs`{.Agda} satisfies $\beta$-reduction;
this is entirely calculational, and we write out all the cases for
clarity.

```agda
    abs-β
      : (t : Term A (suc n)) (ρ : Vec (↯⁺ A) n) (a : ↯⁺ A)
      → eval (abs t) ρ % a .fst ≡ eval (inst t (const a)) ρ
    abs-β (var x) ρ a with fin-view x
    ... | zero  =
      S % K % K % a .fst        ≡⟨ S-β K↓ K↓ (a .snd) ⟩
      K % a .fst % (K % a .fst) ≡⟨ K-β (a .snd) (K↓₁ (a .snd)) ⟩
      a .fst                    ∎
    ... | suc i =
      K % eval (var i) ρ % a .fst  ≡⟨ K-β (lookup ρ i .snd) (a .snd) ⟩
      eval (var i) ρ               ∎

    abs-β (const x) ρ a =
      K % eval (const x) ρ % a .fst ≡⟨ K-β (x .snd) (a .snd) ⟩
      eval (const x) ρ              ∎

    abs-β (app f x) ρ a =
      S % eval (abs f) ρ % eval (abs x) ρ % a .fst             ≡⟨ S-β (abs↓ f ρ) (abs↓ x ρ) (a .snd) ⟩
      (eval (abs f) ρ % a .fst % (eval (abs x) ρ % a .fst))    ≡⟨ ap₂ _%_ (abs-β f ρ a) (abs-β x ρ a) ⟩
      (eval (inst f (const a)) ρ % eval (inst x (const a)) ρ)  ∎
```

We're thus free to provide a combinatorial basis, instead of an
abstraction procedure, when constructing a PCA.

```agda
  has-ski→is-pca : is-pca _%_
  {-# INLINE has-ski→is-pca #-}
  has-ski→is-pca = record { abs = abs ; abs↓ = abs↓ ; abs-β = abs-β }
```
