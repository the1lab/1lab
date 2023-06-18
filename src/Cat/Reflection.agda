open import Cat.Base

open import 1Lab.Prelude hiding (_∘_; id)
open import 1Lab.Reflection

module Cat.Reflection where

--------------------------------------------------------------------------------
-- Patterns for Category Reflection

pattern category-args cat xs =
  _ hm∷ _ hm∷ cat v∷ xs

mk-category-args : Term → List (Arg Term) → List (Arg Term)
mk-category-args cat xs = infer-hidden 2 $ cat v∷ xs

pattern “id” cat =
  def (quote Precategory.id) (category-args cat (_ h∷ []))

pattern “∘” cat f g =
  def (quote Precategory._∘_) (category-args cat (_ h∷ _ h∷ _ h∷ f v∷ g v∷ []))

pattern “Hom” C x y =
  def (quote Precategory.Hom) (category-args C (x v∷ y v∷ []))

pattern functor-args functor xs =
  _ hm∷ _ hm∷ _ hm∷ _ hm∷ _ hm∷ _ hm∷ functor v∷ xs

mk-functor-args : Term → List (Arg Term) → List (Arg Term)
mk-functor-args functor xs = infer-hidden 6 $ functor v∷ xs

pattern “F₀” functor x =
  def (quote Functor.F₀) (functor-args functor (x v∷ []))

pattern “F₁” functor f =
  def (quote Functor.F₁) (functor-args functor (_ h∷ _ h∷ f v∷ []))

“Id” : Term → Term
“Id” cat = def (quote Id) (infer-hidden 2 $ cat h∷ [])

_“F∘”_ : Term → Term → Term
F “F∘” G = def (quote _F∘_) (infer-hidden 9 $ F v∷ G v∷ [])

pattern nat-trans-args nt args =
  _ hm∷ _ hm∷ _ hm∷ _ hm∷
  _ hm∷ _ hm∷
  _ hm∷ _ hm∷
  nt v∷ args

mk-nat-trans-args : Term → List (Arg Term) → List (Arg Term)
mk-nat-trans-args nat-trans xs = infer-hidden 8 $ nat-trans v∷ xs

pattern “η” nat-trans x =
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
-- Name Matchers

new-ob-meta : Term → TC Term
new-ob-meta cat =
  new-meta (def (quote Precategory.Ob) (mk-category-args cat []))

new-hom-meta : Term → Term → Term → TC Term
new-hom-meta cat x y =
  new-meta (def (quote Precategory.Hom) (mk-category-args cat (x v∷ y v∷ [])))

data Precategory-fields : Type where
  id-field : Precategory-fields
  ∘-field  : Term → Term → Precategory-fields

match-id : Term → Term → TC ⊤
match-id cat tm = do
  id ← normalise (def (quote Precategory.id) (mk-category-args cat (infer-hidden 1 [])))
  unify tm id
  debugPrint "tactic" 50 [ "Matched id for " , termErr tm ]

match-∘ : Term → Term → TC (Term × Term)
match-∘ cat tm = do
  f-meta ← new-hom-meta cat unknown unknown
  g-meta ← new-hom-meta cat unknown unknown
  comp ← normalise (def (quote Precategory._∘_) (mk-category-args cat (infer-hidden 3 $ f-meta v∷ g-meta v∷ [])))
  unify tm comp
  debugPrint "tactic" 50 [ "Matched ∘ for " , termErr tm ]
  f-meta ← reduce f-meta
  g-meta ← reduce g-meta
  pure (f-meta , g-meta)

match-F₀ : Functor-terms → Term → TC Term
match-F₀ func tm = do
  x-meta ← new-ob-meta c-cat
  F₀ ← normalise (def (quote Functor.F₀) (mk-functor-args functor (x-meta v∷ [])))
  unify tm F₀
  debugPrint "tactic" 50 [ "Matched F₀ for " , termErr tm ]
  reduce x-meta
  where open Functor-terms func

match-F₁ : Functor-terms → Term → TC Term
match-F₁ func tm = do
  f-meta ← new-hom-meta c-cat unknown unknown
  F₁ ← normalise (def (quote Functor.F₁) (mk-functor-args functor (infer-hidden 2 $ f-meta v∷ [])))
  unify tm F₁
  debugPrint "tactic" 50 [ "Matched F₁ for " , termErr tm ]
  reduce f-meta
  where open Functor-terms func

match-η : Nat-trans-terms → Term → TC Term
match-η nt tm = do
  x-meta ← new-ob-meta d-cat
  η ← normalise (def (quote _=>_.η) (mk-nat-trans-args nat-trans (x-meta v∷ [])))
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
  x ← new-meta (def (quote Precategory.Ob) (infer-hidden 2 (cat v∷ [])))
  y ← new-meta (def (quote Precategory.Ob) (infer-hidden 2 (cat v∷ [])))
  unify tm (def (quote Precategory.Hom) (infer-hidden 2 (cat v∷ x v∷ y v∷ [])))
  pure (x , y)
