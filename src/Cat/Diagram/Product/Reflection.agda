
open import 1Lab.Prelude hiding (_∘_; id)
open import 1Lab.Reflection

open import Cat.Base
open import Cat.Reflection
open import Cat.Diagram.Product

module Cat.Diagram.Product.Reflection where

record Product-terms : Type where
  field
    cat : Term
    prod : Term -- Proof of 'has-products'

open Product-terms

quote-product-terms
  : ∀ {o ℓ} (C : Precategory o ℓ) (has-prods : has-products C)
  → TC Product-terms
quote-product-terms C has-prods = do
  cat ← quoteTC C
  prod ← quoteTC has-prods
  pure (record { cat = cat ; prod = prod })

product-args : Product-terms → List (Arg Term) → List (Arg Term)
product-args ptm args =
  category-args (ptm .cat) (ptm .prod v∷ args)

“⊗₀” : Product-terms → Term → Term → Term
“⊗₀” ptm x y =
  def (quote Binary-products._⊗₀_) (product-args ptm (x v∷ y v∷ []))

“π₁” : Product-terms → Term
“π₁” ptm =
  def (quote Binary-products.π₁) (product-args ptm [])

“π₂” : Product-terms → Term
“π₂” ptm =
  def (quote Binary-products.π₂) (product-args ptm [])


“⟨⟩” : Product-terms → Term → Term → Term
“⟨⟩” ptm f g =
  def (quote Binary-products.⟨_,_⟩) (product-args ptm (infer-hidden 3 (f v∷ g v∷ [])))

match-⊗₀ : Product-terms → Term → TC (Term × Term)
match-⊗₀ ptm tm = do
  x ← new-meta (“Ob” (ptm .cat))
  y ← new-meta (“Ob” (ptm .cat))
  unify tm (“⊗₀” ptm x y)
  debugPrint "tactic" 50 [ "Matched ⊗₀ for " , termErr tm ]
  x ← reduce x
  y ← reduce y
  pure (x , y)

match-π₁ : Product-terms → Term → TC ⊤
match-π₁ ptm tm = do
  unify tm (“π₁” ptm)
  debugPrint "tactic" 50 [ "Matched π₁ for " , termErr tm ]

match-π₂ : Product-terms → Term → TC ⊤
match-π₂ ptm tm = do
  unify tm (“π₂” ptm)
  debugPrint "tactic" 50 [ "Matched π₂ for " , termErr tm ]

match-⟨⟩ : Product-terms → Term → TC (Term × Term)
match-⟨⟩ ptm tm = do
  f ← new-meta (“Hom” (ptm .cat) unknown unknown)
  g ← new-meta (“Hom” (ptm .cat) unknown unknown)
  debugPrint "tactic" 100
    [ "Attempting to match ⟨⟩: " , termErr tm
    , "\n  Unifying against: " , termErr (“⟨⟩” ptm f g)
    ]
  unify tm (“⟨⟩” ptm f g)
  debugPrint "tactic" 50 [ "Matched ⟨⟩ for " , termErr tm ]
  f ← reduce f
  g ← reduce g
  pure (f , g)
