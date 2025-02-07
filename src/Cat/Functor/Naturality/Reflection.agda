open import 1Lab.Reflection.Subst
open import 1Lab.Reflection

open import Cat.Instances.Shape.Terminal
open import Cat.Functor.Naturality
open import Cat.Reasoning
open import Cat.Prelude

module Cat.Functor.Naturality.Reflection where

module _ {o ℓ o' ℓ'} {C : Precategory o ℓ} {D : Precategory o' ℓ'} where

  -- Tactic worker for filling in trivial natural isomorphisms F ≅ⁿ G.
  --
  -- The assumptions are:
  -- 1. ∀ x, F .F₀ x is definitionally equal to G .F₀ x
  -- 2. ∀ f, F .F₁ f is extensionally equal (by `trivial!`) to G .F₁ f
  --    OR C = ⊤Cat
  --
  -- The functor arguments are only used for type inference.
  trivial-isoⁿ : (F G : Functor C D) → Term → TC ⊤
  trivial-isoⁿ _ _ hole = do
    `C ← quoteTC C
    `D ← quoteTC D
    wait-just-a-bit `C >>= unify hole ⊙ λ where
      (def₀ (quote ⊤Cat)) → def₀ (quote !const-isoⁿ)
        ##ₙ (def₀ (quote id-iso) ##ₙ `D)
      _ → def₀ (quote iso→isoⁿ)
        ##ₙ vlam "" (def₀ (quote id-iso) ##ₙ raise 1 `D)
        ##ₙ vlam ""
          (def₀ (quote _··_··_)
            ##ₙ (def₀ (quote idr) ##ₙ raise 1 `D ##ₙ unknown)
            ##ₙ def₀ (quote trivial!)
            ##ₙ (def₀ (quote sym)
              ##ₙ (def₀ (quote idl) ##ₙ raise 1 `D ##ₙ unknown)))

  trivial-isoⁿ!
    : ∀ {F G : Functor C D}
    → {@(tactic trivial-isoⁿ F G) is : F ≅ⁿ G}
    → F ≅ⁿ G
  trivial-isoⁿ! {is = is} = is

-- Tests

module _ {o ℓ} {C : Precategory o ℓ} where

  _ : ∀ {F : Functor C C} → F ≅ⁿ F
  _ = trivial-isoⁿ!

  _ : ∀ {K : Functor ⊤Cat C} → !Const (K .Functor.F₀ _) ≅ⁿ K
  _ = trivial-isoⁿ!
