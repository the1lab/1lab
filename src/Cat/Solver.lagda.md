```agda
open import 1Lab.Reflection
open import 1Lab.Prelude hiding (id ; _∘_)

open import Cat.Base

open import Data.Bool
open import Data.List

module Cat.Solver where
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
module _ (Cat : Precategory o h) where
  open Precategory Cat
```
<!--
```agda
  private variable
    A B C : Ob
```
-->
```agda
  data Expr : Ob → Ob → Type (o ⊔ h) where
    `id  : Expr A A
    _`∘_ : Expr B C → Expr A B → Expr A C
    _↑   : Hom A B → Expr A B

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
  embed : Expr A B → Hom A B
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
  eval : Expr B C → Hom A B → Hom A C
  eval `id f      = f
  eval (f ↑) g    = f ∘ g
  eval (f `∘ g) h = eval f (eval g h)

  nf : Expr A B → Hom A B
  nf e = eval e id

  eval-sound-k : (e : Expr B C) (f : Hom A B) → eval e id ∘ f ≡ eval e f
  eval-sound-k `id f = idl _
  eval-sound-k (x ↑) f = ap (_∘ f) (idr x)
  eval-sound-k (f `∘ g) h =
    eval f (eval g id) ∘ h      ≡⟨ ap (_∘ h) (sym (eval-sound-k f (eval g id))) ⟩
    (eval f id ∘ eval g id) ∘ h ≡⟨ sym (assoc _ _ _) ⟩
    eval f id ∘ eval g id ∘ h   ≡⟨ ap (_ ∘_) (eval-sound-k g h) ⟩
    eval f id ∘ eval g h        ≡⟨ eval-sound-k f _ ⟩
    eval (f `∘ g) h             ∎
```

Working this out in a back-of-the-envelope calculation, one sees that
`eval f id` should compute the same morphism as `embed f`. Indeed,
that's the case! Since embed is the "intended semantics", and eval is an
"optimised evaluator", we call this result _soundness_. We can prove it
by induction on the expression. Here are the two straightforward cases,
and why they work:

```agda
  eval-sound : (e : Expr A B) → eval e id ≡ embed e
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
    eval f (eval g id)    ≡⟨ sym (eval-sound-k f (eval g id)) ⟩
    eval f id ∘ eval g id ≡⟨ ap₂ _∘_ (eval-sound f) (eval-sound g) ⟩
    embed (f `∘ g)        ∎
```

We now have a general theorem for solving associativity and identity
problems! If two expressions compute the same transformation of
hom-sets, then they represent the same morphism.

```agda
  abstract
    solve : (f g : Expr A B) → eval f id ≡ eval g id → embed f ≡ embed g
    solve f g p = sym (eval-sound f) ·· p ·· (eval-sound g)

    solve-filler : (f g : Expr A B) → (p : eval f id ≡ eval g id) → Square (eval-sound f) p (solve f g p) (eval-sound g)
    solve-filler f g p j i = ··-filler (sym (eval-sound f)) p (eval-sound g) j i
```

# The cursed part

```agda
module Reflection where

  pattern category-args xs =
    _ h0∷ _ h0∷ _ v∷ xs

  pattern “id” =
    def (quote Precategory.id) (category-args (_ h∷ []))

  pattern “∘” f g =
    def (quote Precategory._∘_) (category-args (_ h∷ _ h∷ _ h∷ f v∷ g v∷ []))

  mk-category-args : Term → List (Arg Term) → List (Arg Term)
  mk-category-args cat xs = unknown h∷ unknown h∷ cat v∷ xs

  “solve” : Term → Term → Term → Term
  “solve” cat lhs rhs = def (quote solve) (mk-category-args cat $ infer-hidden 2 $ lhs v∷ rhs v∷ def (quote refl) [] v∷ [])

  “nf” : Term → Term → Term
  “nf” cat e = def (quote nf) (mk-category-args cat $ infer-hidden 2 $ e v∷ [])

  build-expr : Term → Term
  build-expr “id” = con (quote `id) []
  build-expr (“∘” f g) = con (quote _`∘_) (build-expr f v∷ build-expr g v∷ [] )
  build-expr f = con (quote _↑) (f v∷ [])

  dont-reduce : List Name
  dont-reduce = quote Precategory.id ∷ quote Precategory._∘_ ∷ []

  repr-macro : Term → Term → Term → TC ⊤
  repr-macro cat f hole =
    withNormalisation false $
    dontReduceDefs dont-reduce $ do
      let e = build-expr f
      nf ← normalise $ “nf” cat e
      typeError $ strErr "The expression\n  " ∷
                    termErr f ∷
                  strErr "\nIs represented by the expression\n  " ∷
                    termErr e ∷
                  strErr "\nAnd has normal form\n  " ∷
                    termErr nf ∷ []

  simplify-macro : Term → Term → Term → TC ⊤
  simplify-macro cat f hole =
    withNormalisation false $
    dontReduceDefs dont-reduce $ do
      let e = build-expr f
      nf ← normalise (“nf” cat e)
      unify hole nf

  solve-macro : Term → Term → TC ⊤
  solve-macro cat hole =
    withNormalisation false $
    dontReduceDefs dont-reduce $ do
    goal ← inferType hole >>= reduce
    just (lhs , rhs) ← get-boundary goal
      where nothing → typeError $ strErr "Can't determine boundary: " ∷
                                  termErr goal ∷ []
    let elhs = build-expr lhs
    let erhs = build-expr rhs
    (noConstraints $ unify hole (“solve” cat elhs erhs)) <|> do
      nf-lhs ← normalise (“nf” cat elhs)
      nf-rhs ← normalise (“nf” cat erhs)
      typeError (strErr "Could not solve the following goal:\n  " ∷
                   termErr lhs ∷ strErr " ≡ " ∷ termErr rhs ∷
                 strErr "\nComputed normal forms:\n  LHS: " ∷
                   termErr nf-lhs ∷
                 strErr "\n  RHS: " ∷
                   termErr nf-rhs ∷ [])


macro
  repr! : Term → Term → Term → TC ⊤
  repr! cat f = Reflection.repr-macro cat f

  simplify! : Term → Term → Term → TC ⊤
  simplify! cat f = Reflection.simplify-macro cat f

  solve! : Term → Term → TC ⊤
  solve! = Reflection.solve-macro
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
  test = solve! C
```
