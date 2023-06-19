open import Cat.Base

open import 1Lab.Prelude hiding (_∘_; id)
open import 1Lab.Reflection

module Cat.Reflection where

--------------------------------------------------------------------------------
-- Helpers for constructing reflected fields.

category-args : Term → List (Arg Term) → List (Arg Term)
category-args cat xs = infer-hidden 2 $ cat v∷ xs

“id” : Term → Term → Term
“id” cat x =
  def (quote Precategory.id) (category-args cat (x h∷ []))

“∘” : Term → Term → Term → Term
“∘” cat f g =
  def (quote Precategory._∘_) (category-args cat (infer-hidden 3 (f v∷ g v∷ [])))

“Ob” : Term → Term
“Ob” cat =
  def (quote Precategory.Ob) (category-args cat [])

“Hom” : Term → Term → Term → Term
“Hom” cat x y =
  def (quote Precategory.Hom) (category-args cat (x v∷ y v∷ []))

functor-args : Term → List (Arg Term) → List (Arg Term)
functor-args functor xs = infer-hidden 6 $ functor v∷ xs

“F₀” : Term → Term → Term
“F₀” functor x =
  def (quote Functor.F₀) (functor-args functor (x v∷ []))

“F₁” : Term → Term → Term
“F₁” functor f =
  def (quote Functor.F₁) (functor-args functor (infer-hidden 2 (f v∷ [])))

“Id” : Term → Term
“Id” cat =
  def (quote Id) (infer-hidden 2 $ cat h∷ [])

_“F∘”_ : Term → Term → Term
F “F∘” G =
  def (quote _F∘_) (infer-hidden 9 $ F v∷ G v∷ [])

nat-trans-args : Term → List (Arg Term) → List (Arg Term)
nat-trans-args nat-trans xs = infer-hidden 8 $ nat-trans v∷ xs

“η” : Term → Term → Term
“η” nat-trans x =
  def (quote _=>_.η) (nat-trans-args nat-trans (x v∷ []))

--------------------------------------------------------------------------------
-- Term Bundles

record Functor-terms : Type where
  field
    c-cat : Term
    d-cat : Term
    functor : Term

quote-functor-terms
  : ∀ {o ℓ o' ℓ'} {C : Precategory o ℓ} {D : Precategory o' ℓ'}
  → Functor C D
  → TC Functor-terms
quote-functor-terms {C = C} {D = D} F = do
  c-cat ← quoteTC C
  d-cat ← quoteTC D
  functor ← quoteTC F
  pure (record { c-cat = c-cat ; d-cat = d-cat ; functor = functor })
  where open Functor-terms

record Nat-trans-terms : Type where
  field
    c-cat : Term
    d-cat : Term
    F-functor : Term
    G-functor : Term
    nat-trans : Term

  F-terms : Functor-terms
  F-terms = record { c-cat = c-cat ; d-cat = d-cat ; functor = F-functor }

  G-terms : Functor-terms
  G-terms = record { c-cat = c-cat ; d-cat = d-cat ; functor = G-functor }

quote-nat-trans-terms
  : ∀ {o ℓ o' ℓ'} {C : Precategory o ℓ} {D : Precategory o' ℓ'}
  → {F G : Functor C D}
  → F => G
  → TC Nat-trans-terms
quote-nat-trans-terms {C = C} {D = D} {F = F} {G = G} α = do
  c-cat ← quoteTC C
  d-cat ← quoteTC D
  F-functor ← quoteTC F
  G-functor ← quoteTC G
  nat-trans ← quoteTC α
  pure (record
         { c-cat = c-cat
         ; d-cat = d-cat
         ; F-functor = F-functor
         ; G-functor = G-functor
         ; nat-trans = nat-trans
         })

--------------------------------------------------------------------------------
-- Term Matchers

data Precategory-fields : Type where
  id-field : Precategory-fields
  ∘-field  : Term → Term → Precategory-fields

match-id : Term → Term → TC ⊤
match-id cat tm = do
  id ← normalise (“id” cat unknown)
  unify tm id
  debugPrint "tactic" 50 [ "Matched id for " , termErr tm ]

match-∘ : Term → Term → TC (Term × Term)
match-∘ cat tm = do
  f-meta ← new-meta (“Hom” cat unknown unknown)
  g-meta ← new-meta (“Hom” cat unknown unknown)
  comp ← normalise (“∘” cat f-meta g-meta)
  unify tm comp
  debugPrint "tactic" 50 [ "Matched ∘ for " , termErr tm ]
  f-meta ← reduce f-meta
  g-meta ← reduce g-meta
  pure (f-meta , g-meta)

match-F₀ : Functor-terms → Term → TC Term
match-F₀ func tm = do
  x-meta ← new-meta (“Ob” c-cat)
  F₀ ← normalise (“F₀” functor x-meta)
  unify tm F₀
  debugPrint "tactic" 50 [ "Matched F₀ for " , termErr tm ]
  reduce x-meta
  where open Functor-terms func

match-F₁ : Functor-terms → Term → TC Term
match-F₁ func tm = do
  f-meta ← new-meta (“Hom” c-cat unknown unknown)
  F₁ ← normalise (“F₁” functor f-meta)
  unify tm F₁
  debugPrint "tactic" 50 [ "Matched F₁ for " , termErr tm ]
  reduce f-meta
  where open Functor-terms func

match-η : Nat-trans-terms → Term → TC Term
match-η nt tm = do
  x-meta ← new-meta (“Ob” d-cat)
  η ← normalise (“η” nat-trans x-meta)
  unify tm η
  debugPrint "tactic" 50 [ "Matched η for " , termErr tm ]
  reduce x-meta
  where open Nat-trans-terms nt

--------------------------------------------------------------------------------
-- Extracting Objects

-- Get the source and target of a 'Hom' for a given category 'cat'.
get-hom-objects : Term → Term → TC (Term × Term)
get-hom-objects cat tm = do
  tm ← normalise tm
  x ← new-meta (“Ob” cat)
  y ← new-meta (“Ob” cat)
  unify tm (“Hom” cat x y)
  x ← reduce x
  y ← reduce y
  pure (x , y)
