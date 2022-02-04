```agda
open import 1Lab.Reflection
open import 1Lab.Prelude hiding (id ; _∘_)

open import Category.Base

open import Data.Bool

module Category.Solver where
```

<!--
```agda
private variable
  o h : Level
```
-->

# Solver for Categories

This module is split pretty cleanly into two halves: the first half
implements an algorithm for reducing, in a systematic way, problems
involving associativity and identity of composition in a precategory.
The latter half, significantly more cursed, uses this infrastructure to
automatically solve equality goals of this form.

With a precategory in hand, we by defining a language of composition.

```agda
module _ (C : Precategory o h) where
  open Precategory C

  data Expr : Ob → Ob → Type (o ⊔ h) where
    `id  : {A : _}     → Expr A A
    _`∘_ : {A B C : _} → Expr B C → Expr A B → Expr A C
    _↑   : {A B : _}   → Hom A B → Expr A B
  
  infixr 40 _`∘_
  infix 50 _↑
```

A term of type `Expr`{.Agda} represents, in a symbolic way, a composite
of morphisms in our category $C$. What this means is that, while $f
\circ g$ is some unknowable inhabitant of `Hom`{.Agda}, $f `\circ g$
represents an inhabitant of `Hom`{.Agda} which is _known_ to be a
composition of (the trees that represent) $f$ and $g$. We can now define
"two" ways of computing the morphism that an `Expr`{.Agda} represents.
The first is a straightforward `embed`{.Agda}ding:

```agda
  embed : {A B : _} → Expr A B → Hom A B
  embed `id      = id
  embed (f ↑)    = f
  embed (f `∘ g) = embed f ∘ embed g
```

The second computation is a bit less obvious. If you're a programmer, it
should be familiar under the name "continuation passing style".
Categorically, it can be seen as embedding into the presheaf category of
$C$. In either case, the difference is that instead of computing a
single morphism, we compute a _transformation of hom-spaces_:

```agda
  eval : {A B C : _} → Expr B C → Hom A B → Hom A C
  eval `id f      = f
  eval (f ↑) g    = f ∘ g
  eval (f `∘ g) h = eval f (eval g h)
```

Working this out in a back-of-the-envelope calculation, one sees that
`eval f id` should compute the same morphism as `embed f`. Indeed,
that's the case! Since embed is the "intended semantics", and eval is an
"optimised evaluator", we call this result _soundness_. We can prove it
by induction on the expression. Here are the two straightforward cases,
and why they work:

```agda
  eval-sound : {A B : _} (e : Expr A B) → eval e id ≡ embed e
  eval-sound `id   = refl  -- eval `id computes away
  eval-sound (x ↑) = idr _ -- must show f = f ∘ id
```

Now comes the complicated part. First, we'll factor out proving that
nested `eval`{.Agda} is the same as `eval`{.Agda} of a composition to a
helper lemma. Then comes the actual inductive argument: We apply our
lemma (still to be defined!), then we can apply the induction
hypothesis, getting us to our goal.

```agda
  eval-sound (f `∘ g) =
    eval f (eval g id)    ≡⟨ sym (lemma f (eval g id)) ⟩
    eval f id ∘ eval g id ≡⟨ ap₂ _∘_ (eval-sound f) (eval-sound g) ⟩
    embed (f `∘ g)        ∎
    where
```

The helper lemma is a bit more general than I had promised, but it's
also an argument by induction on expressions. It shows that we can
replace "precomposition with `eval ... id`" with an application of
`eval`{.Agda}.

```agda
      lemma : {A B C : _} (e : Expr B C) (f : Hom A B) → eval e id ∘ f ≡ eval e f
      lemma `id f = idl _
      lemma (x ↑) f = ap (_∘ f) (idr x) 
      lemma (f `∘ g) h =
        eval f (eval g id) ∘ h      ≡⟨ ap (_∘ h) (sym (lemma f (eval g id))) ⟩
        (eval f id ∘ eval g id) ∘ h ≡⟨ sym (assoc _ _ _) ⟩
        eval f id ∘ eval g id ∘ h   ≡⟨ ap (_ ∘_) (lemma g h) ⟩
        eval f id ∘ eval g h        ≡⟨ lemma f (eval g h) ⟩
        eval (f `∘ g) h             ∎
```

We now have a general theorem for solving associativity and identity
problems! If two expressions compute the same transformation of
hom-sets, then they represent the same morphism.

```agda
  associate : {A B : _} (f g : Expr A B) → eval f id ≡ eval g id → embed f ≡ embed g
  associate f g p = sym (eval-sound f) ·· p ·· eval-sound g
```

# The cursed part

Now we hook up `associate`{.Agda} to an Agda macro. Like all
metaprogramming, it's not pretty, but I've written comments around it to
hopefully explain things a bit.

```agda
record CategoryNames : Type where
  field
    is-∘  : Name → Bool
    is-id : Name → Bool

buildMatcher : Name → Maybe Name → Name → Bool
buildMatcher n nothing  x = n name=? x
buildMatcher n (just m) x = or (n name=? x) (m name=? x)

findGenericNames : Name → Name → Term → TC CategoryNames
findGenericNames star id mon = do
  ∘-altName ← normalise (def star (unknown h∷ unknown h∷ mon v∷ []))
  ε-altName ← normalise (def id  (unknown h∷ unknown h∷ mon v∷ []))
  -- typeError (termErr ∘-altName ∷ termErr ε-altName ∷ [])
  returnTC record
    { is-∘  = buildMatcher star (getName ∘-altName)
    ; is-id = buildMatcher id  (getName ε-altName)
    }

findCategoryNames : Term → TC CategoryNames
findCategoryNames = findGenericNames (quote Precategory._∘_) (quote Precategory.id)
```

The trick above was stolen from the Agda standard library [monoid
solver]. Given the term representing the category, we _evaluate_ the
projections (that's the `-altNames`) in case they compute away to
something else. This lets us not miss solutions when working with a
concrete category, that might have names other than
`Precategory._∘_`{.Agda} and `Precategory.id`{.Agda}.

[monoid solver]: https://github.com/agda/agda-stdlib/blob/master/src/Tactic/MonoidSolver.agda

Now we can turn to building an `Expr`{.Agda} (well, a `Term`{.Agda}
representing an `Expr`{.Agda}: a representation of a representation of
an arrow!) given a `Term`{.Agda}. We do this with mutual recursion, to
make stuff even more complicated.

```agda
private
  module _ (names : CategoryNames) where
    open CategoryNames names

    build-expr : Term → Term
    build-∘ : List (Arg Term) → Term

    ``id : Term -- Constant representation of `id
    ``id = con (quote `id) []

    build-expr (def x as) with is-∘ x | is-id x
    ... | false | false = con (quote _↑) (def x as v∷ [])
    ... | false | true = ``id
    ... | true  | q = build-∘ as
```

If we're looking at a `def`{.Agda} (an applied defined function) or a
`con`{.Agda} (an applied co/inductive constructor). If we're looking at
some random old term, then we lift it (with `_↑`{.Agda}). If it's the
identity map, then we use our constant repr. of id, otherwise we're
looking at a composition.

```agda
    build-expr (con x as) with is-∘ x | is-id x
    ... | false | false = con (quote _↑) (def x as v∷ [])
    ... | false | true = ``id
    ... | true  | q = build-∘ as

    build-expr x = con (quote _↑) (x v∷ [])

    build-∘ (x v∷ y v∷ []) = con (quote _`∘_) 
      (build-expr x v∷ build-expr y v∷ [])
    build-∘ (_ ∷ xs) = build-∘ xs
    build-∘ _ = unknown

  getBoundary : Term → TC (Maybe (Term × Term))
  getBoundary tm@(def (quote PathP) (_ h∷ T v∷ x v∷ y v∷ [])) = do
    unify tm (def (quote _≡_) (x v∷ y v∷ []))
    returnTC (just (x , y))
  getBoundary _ = returnTC nothing
```

Then you essentially slap all of that together into a little macro.

```agda
solveGeneric : (Term → TC CategoryNames) → (Term → Term) → Term → Term → TC ⊤
solveGeneric find mkcat category hole = do
  goal ← inferType hole >>= normalise
  names ← find category

  just (lhs , rhs) ← getBoundary goal
    where nothing → typeError (strErr "Can't solve: " ∷ termErr goal ∷ [])

  let rep = build-expr names

  unify hole (def (quote associate) 
    (mkcat category v∷ rep lhs v∷ rep rhs v∷ def (quote refl) [] v∷ []))

macro
  solve : Term → Term → TC ⊤
  solve = solveGeneric findCategoryNames (λ x → x)
```

## Demo

As a quick demonstration (and sanity check/future proofing/integration
testing/what have you):

```
module _ (C : Precategory o h) where private
  module C = Precategory C
  variable
    A B : C.Ob
    a b c d : C.Hom A B

  test : a C.∘ (b C.∘ (c C.∘ C.id) C.∘ C.id C.∘ (d C.∘ C.id)) 
       ≡ a C.∘ b C.∘ c C.∘ d
  test = solve C
```
