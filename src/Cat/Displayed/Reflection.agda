open import 1Lab.Prelude hiding (_∘_; id)
open import 1Lab.Reflection

open import Cat.Displayed.Base
import Cat.Displayed.Reasoning as Dr

open import Cat.Base
open import Cat.Reflection

module Cat.Displayed.Reflection where

displayed-args : Term → List (Arg Term) → List (Arg Term)
displayed-args disp xs = infer-hidden 5 $ disp v∷ xs

“Ob[]” : Term → Term → Term
“Ob[]” disp x =
  def (quote Displayed.Ob[_]) (displayed-args disp (x v∷ []))

“Hom[]” : Term → Term → Term → Term → Term
“Hom[]” disp f x y =
    def (quote Displayed.Hom[_]) (displayed-args disp (infer-hidden 2 (f v∷ x v∷ y v∷ [])))

“id′” : Term → Term → Term → Term
“id′” disp x x′ =
  def (quote Displayed.id′) (displayed-args disp (x h∷ x′ h∷ []))

“∘′” : Term → Term → Term → Term → Term → Term
“∘′” disp f g f′ g′ =
  def (quote Displayed._∘′_) (displayed-args disp (infer-hidden 6 (f h∷ g h∷ f′ v∷ g′ v∷ [])))

“hom[]” : Term → Term → Term → Term → Term → Term
“hom[]” disp f g p f′ =
  def (quote Dr.hom[_]) (displayed-args disp (infer-hidden 4 (f h∷ g h∷ p v∷ f′ v∷ [])))

record Displayed-terms : Type where
  field
    cat : Term
    disp : Term

open Displayed-terms

quote-displayed-terms
  : ∀ {o′ ℓ′ o′′ ℓ′′} {B : Precategory o′ ℓ′}
  → Displayed B o′′ ℓ′′
  → TC Displayed-terms
quote-displayed-terms {B = B} E = do
  cat ← quoteTC B
  disp ← quoteTC E
  pure (record { cat = cat ; disp = disp })

match-id′ : Displayed-terms → Term → TC ⊤
match-id′ dtm tm = do
  id′ ← normalise (“id′” (dtm .disp) unknown unknown)
  unify tm id′
  debugPrint "tactic" 50 [ "Matched id′ for " , termErr tm ]

match-∘′ : Displayed-terms → Term → TC (Term × Term × Term × Term)
match-∘′ dtm tm = do
  f-meta ← new-meta (“Hom” (dtm .cat) unknown unknown)
  g-meta ← new-meta (“Hom” (dtm .cat) unknown unknown)
  f′-meta ← new-meta (“Hom[]” (dtm .disp) f-meta unknown unknown)
  g′-meta ← new-meta (“Hom[]” (dtm .disp) g-meta unknown unknown)
  ∘′ ← normalise (“∘′” (dtm .disp) f-meta g-meta f′-meta g′-meta)
  unify tm ∘′
  debugPrint "tactic" 50 [ "Matched ∘′ for " , termErr tm ]
  f-meta ← reduce f-meta
  g-meta ← reduce g-meta
  f′-meta ← reduce f′-meta
  g′-meta ← reduce g′-meta
  pure (f-meta , g-meta , f′-meta , g′-meta)

match-hom[] : Displayed-terms → Term → TC (Term × Term × Term × Term)
match-hom[] dtm tm = do
  f-meta ← new-meta (“Hom” (dtm .cat) unknown unknown)
  g-meta ← new-meta (“Hom” (dtm .cat) unknown unknown)
  p-meta ← new-meta (“Path” (“Hom” (dtm .cat) unknown unknown) f-meta g-meta)
  f′-meta ← new-meta (“Hom[]” (dtm .disp) f-meta unknown unknown)
  let hom[] = “hom[]” (dtm .disp) f-meta g-meta p-meta f′-meta
  unify tm hom[]
  f-meta ← reduce f-meta
  g-meta ← reduce g-meta
  p-meta ← reduce p-meta
  f′-meta ← reduce f′-meta
  debugPrint "tactic" 50
    [ "Matched hom[] for " , termErr tm
    , "\n  f  : " , termErr f-meta
    , "\n  g  : " , termErr g-meta
    , "\n  p  : " , termErr p-meta
    , "\n  f′ : " , termErr f′-meta
    ]
  pure (f-meta , g-meta , p-meta , f′-meta)

get-hom[]-objects : Displayed-terms → Term → TC (Term × Term × Term)
get-hom[]-objects dtm tm = do
  tm ← normalise tm
  x ← new-meta (“Ob” (dtm .cat))
  y ← new-meta (“Ob” (dtm .cat))
  f ← new-meta (“Hom” (dtm .cat) x y)
  x′ ← new-meta (“Ob[]” (dtm .disp) x)
  y′ ← new-meta (“Ob[]” (dtm .disp) y)
  unify tm (“Hom[]” (dtm .disp) f x′ y′)
  f ← reduce f
  x′ ← reduce x′
  y′ ← reduce y′
  pure (f , x′ , y′)
