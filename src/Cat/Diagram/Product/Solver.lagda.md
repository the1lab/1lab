<!--
```agda
open import 1Lab.Reflection
open import 1Lab.Reflection.Solver

open import Cat.Diagram.Product
open import Cat.Diagram.Product.Reflection
open import Cat.Reflection
open import Cat.Prelude

open import Data.List

import Cat.Reasoning
```
-->

```agda
module Cat.Diagram.Product.Solver where
```

# A Solver for Categories with Binary Products

Much like the [category solver], this module is split into two halves.
The first implements an algorithm for normalizing expressions in the
language of a category with binary products. The latter half consists
of the usual reflection hacks required to transform Agda expressions
into our internal expression type.

[category solver]: Cat.Solver.html

```agda
module NbE {o ℓ} (𝒞 : Precategory o ℓ) (cartesian : ∀ A B → Product 𝒞 A B) where
  open Cat.Reasoning 𝒞
  open Binary-products 𝒞 cartesian
```

## Expressions

We begin by defining an expression type for a category with binary
products. Mathematically, this /almost/ corresponds to the free
category with binary products over a quiver, but we are working
with un-quotiented syntax.

```agda
  data ‶Ob‶ : Type (o ⊔ ℓ) where
    _‶⊗‶_ : ‶Ob‶ → ‶Ob‶ → ‶Ob‶
    ‶_‶   : Ob → ‶Ob‶

  ⟦_⟧ₒ : ‶Ob‶ → Ob
  ⟦ X ‶⊗‶ Y ⟧ₒ =  ⟦ X ⟧ₒ ⊗₀ ⟦ Y ⟧ₒ
  ⟦ ‶ X ‶ ⟧ₒ = X

  data Expr : ‶Ob‶ → ‶Ob‶ → Type (o ⊔ ℓ) where
    ‶id‶    : ∀ {X} → Expr X X
    _‶∘‶_   : ∀ {X Y Z} → Expr Y Z → Expr X Y → Expr X Z
    ‶π₁‶    : ∀ {X Y} → Expr (X ‶⊗‶ Y) X
    ‶π₂‶    : ∀ {X Y} → Expr (X ‶⊗‶ Y) Y
    ‶⟨_,_⟩‶ : ∀ {X Y Z} → Expr X Y → Expr X Z → Expr X (Y ‶⊗‶ Z)
    ‶_‶     : ∀ {X Y} → Hom ⟦ X ⟧ₒ ⟦ Y ⟧ₒ → Expr X Y
```

Note that we also define a syntax for products of objects
in this free category, even though the ambient category
`𝒞`{.Agda} already has binary products. The reason for this is two-fold.
The first, more mundane reason is that the unifier will get very confused
if we don't do this. The second reason is much more mathematically
interesting, as it pertains to our choice of normalization algorithm.

Much like the aforementioned [category solver], we are going to be
using a variant of *Normalization By Evaluation* (NbE for short).
This class of normalization algorithms operates by constructing a
domain of "values", which are meant to denote the semantics of some
expression. Normalization then occurs in 2 phases: an "evaluation"
phase where we transform expressions into values, and a "quotation"
phase where we reflect values back into expressions. As the values are
meant to represent the _semantics_ of an expression, each equivalence
class of expressions ought to be mapped to the same value during
evaluation. The quotation phase then plucks out a canonical
representative for each one of these equivalence classes, which
then becomes our normal form.

The particular variant of NbE that we are using is known as *Typed NbE*.
What distinguishes it from *Untyped NbE* is the treatment of quotation.
In Untyped NbE, quotation proceeds in a syntax-directed manner, which
makes the enaction of η-laws[^eta] more difficult. On the other hand,
if we quote in a type directed manner, we can perform η-expansion
at every possible opportunity, which simplifies the implementation
considerably. This will result in larger normal forms, but the
expressions the solver needs to deal with are small, so this isn't
a pressing issue.

[category solver]: Cat.Solver.html
[^eta]: In our context, an η-law is something like `
⟨ π₁ ∘ f , π₂ ∘ f ⟩ ≡ f`, where we have an introduction form
wrapping a bunch of eliminators applied to the same expression.

Next, we define an interpretation of expressions back into morphisms.
This will be used to state the all-important soundness theorem.

```agda
  ⟦_⟧ₑ : ∀ {X Y} → Expr X Y → Hom ⟦ X ⟧ₒ ⟦ Y ⟧ₒ
  ⟦ ‶id‶ ⟧ₑ = id
  ⟦ e1 ‶∘‶ e2 ⟧ₑ = ⟦ e1 ⟧ₑ ∘ ⟦ e2 ⟧ₑ
  ⟦ ‶π₁‶ ⟧ₑ = π₁
  ⟦ ‶π₂‶ ⟧ₑ = π₂
  ⟦ ‶⟨ e1 , e2 ⟩‶ ⟧ₑ = ⟨ ⟦ e1 ⟧ₑ , ⟦ e2 ⟧ₑ ⟩
  ⟦ ‶ f ‶ ⟧ₑ = f
```

## Values

Next, we define a type of *Values*. The goal here is to ensure that we
can't have any eliminators (in our case, projections) applied to
introduction forms (in our case, `⟨_,_⟩`{.Agda}). We also need to handle
the normal associativity/identity equations, but those will be handled
by evaluating our expressions into presheaves.

```agda
  data Value : ‶Ob‶ → ‶Ob‶ → Type (o ⊔ ℓ) where
    vhom  : ∀ {X Y} → Hom ⟦ X ⟧ₒ ⟦ Y ⟧ₒ → Value X Y
    vpair : ∀ {X Y Z} → Value X Y → Value X Z → Value X (Y ‶⊗‶ Z)
```

We now define our eliminators for values.

```agda
  vfst : ∀ {X Y Z} → Value X (Y ‶⊗‶ Z) → Value X Y
  vfst (vhom f) = vhom (π₁ ∘ f)
  vfst (vpair v1 v2) = v1

  vsnd : ∀ {X Y Z} → Value X (Y ‶⊗‶ Z) → Value X Z
  vsnd (vhom f) = vhom (π₂ ∘ f)
  vsnd (vpair v1 v2) = v2

  vid : ∀ {X} → Value X X
  vid = vhom id
```

## Quotation

As noted above, our quotation is type-directed to make applying η-laws
easier. When we encounter a `v : Value X (Y ‶⊗‶ Z)`, we will always
η-expand it using the eliminators defined above. If `v` is a
`vpair`{.Agda}, then the eliminators will compute away, and we will be
left with the same value we started with. If `v` is a `vhom`{.Agda},
then we will have η-expanded it, so all of our normal forms will be
/fully/ η-expanded.

As a terminological note, we call this function `reflect` because
`quote` is a reserved keyword in Agda.

```agda
  reflect : ∀ X Y → Value X Y → Hom ⟦ X ⟧ₒ ⟦ Y ⟧ₒ
  reflect X (Y ‶⊗‶ Z) v = ⟨ (reflect X Y (vfst v)) , reflect X Z (vsnd v) ⟩
  reflect X ‶ Y ‶ (vhom f) = f
```


## Evaluation

Evaluation operates in much the same way as the [category solver],
where we evaluate to `Value X Y → Value X Z` instead of just `Value Y Z`.
This allows us to apply the associativity/identity equations, as well
as the equation that `⟨ f , g ⟩ ∘ h ≡ ⟨ f ∘ h , g ∘ h ⟩`.

[category solver]: Cat.Solver.html

```agda
  eval : ∀ {X Y Z} → Expr Y Z → Value X Y → Value X Z
  eval ‶id‶ v = v
  eval (e1 ‶∘‶ e2) v = eval e1 (eval e2 v)
  eval ‶π₁‶ v = vfst v
  eval ‶π₂‶ v = vsnd v
  eval ‶⟨ e1 , e2 ⟩‶ v = vpair (eval e1 v) (eval e2 v)
  eval ‶ f ‶ v = vhom (f ∘ reflect _ _ v)
```

As noted earlier, we obtain normal forms by evaluating then quoting.

```agda
  nf : ∀ X Y → Expr X Y → Hom ⟦ X ⟧ₒ ⟦ Y ⟧ₒ
  nf X Y e = reflect X Y (eval e vid)
```

## Soundness

Before proving soundness, we need to prove the normal battery of random
lemmas. The first states that quoting a `vhom f` gives us back `f`.

```agda
  vhom-sound : ∀ X Y → (f : Hom ⟦ X ⟧ₒ ⟦ Y ⟧ₒ) → reflect X Y (vhom f) ≡ f
  vhom-sound X (Y ‶⊗‶ Z) f =
    ⟨ reflect X Y (vhom (π₁ ∘ f)) , reflect X Z (vhom (π₂ ∘ f)) ⟩ ≡⟨ ap₂ ⟨_,_⟩ (vhom-sound X Y (π₁ ∘ f)) (vhom-sound X Z (π₂ ∘ f)) ⟩
    ⟨ π₁ ∘ f , π₂ ∘ f ⟩                                           ≡˘⟨ ⟨⟩-unique f refl refl ⟩
    f                                                             ∎
  vhom-sound X ‶ x ‶ f = refl
```

Next, some soundless lemmas for our eliminators. We want to show that
applying each eliminator to a value corresponds to the correct thing
once interpreted into our category `𝒞`.

```agda
  vfst-sound : ∀ X Y Z → (v : Value X (Y ‶⊗‶ Z)) → reflect X Y (vfst v) ≡ π₁ ∘ reflect X (Y ‶⊗‶ Z) v
  vfst-sound X Y Z (vhom f) =
    reflect X Y (vhom (π₁ ∘ f))       ≡⟨ vhom-sound X Y (π₁ ∘ f) ⟩
    π₁ ∘ f                            ≡˘⟨ refl⟩∘⟨ vhom-sound X (Y ‶⊗‶ Z) f ⟩
    π₁ ∘ reflect X (Y ‶⊗‶ Z) (vhom f) ∎
  vfst-sound X Y Z (vpair v1 v2) =
    reflect X Y v1                               ≡˘⟨ π₁∘⟨⟩ ⟩
    π₁ ∘ ⟨ (reflect X Y v1) , (reflect X Z v2) ⟩ ∎

  vsnd-sound : ∀ X Y Z → (v : Value X (Y ‶⊗‶ Z)) → reflect X Z (vsnd v) ≡ π₂ ∘ reflect X (Y ‶⊗‶ Z) v
  vsnd-sound X Y Z (vhom f) =
    reflect X Z (vhom (π₂ ∘ f))       ≡⟨ vhom-sound X Z (π₂ ∘ f) ⟩
    π₂ ∘ f                            ≡˘⟨ refl⟩∘⟨ vhom-sound X (Y ‶⊗‶ Z) f ⟩
    π₂ ∘ reflect X (Y ‶⊗‶ Z) (vhom f) ∎
  vsnd-sound X Y Z (vpair v1 v2) =
    reflect X Z v2                               ≡˘⟨ π₂∘⟨⟩ ⟩
    π₂ ∘ ⟨ (reflect X Y v1) , (reflect X Z v2) ⟩ ∎
```

We handle composition of values by interpreting expressions as functions
/between/ values. So in a sense, this following lemma is a proof of
soundness for our interpretation of composition.

```agda
  sound-k : ∀ X Y Z → (e : Expr Y Z) → (v : Value X Y)
          → reflect X Z (eval e v) ≡ ⟦ e ⟧ₑ ∘ reflect X Y v
  sound-k X Y Y ‶id‶ v = sym (idl _)
  sound-k X Y Z (e1 ‶∘‶ e2) v =
    reflect X Z (eval e1 (eval e2 v)) ≡⟨ sound-k X _ Z e1 (eval e2 v) ⟩
    ⟦ e1 ⟧ₑ ∘ reflect X _ (eval e2 v) ≡⟨ refl⟩∘⟨ sound-k X Y _ e2 v ⟩
    ⟦ e1 ⟧ₑ ∘ ⟦ e2 ⟧ₑ ∘ reflect X Y v ≡⟨ assoc _ _ _ ⟩
    ⟦ e1 ‶∘‶ e2 ⟧ₑ ∘ reflect X Y v    ∎
  sound-k X (Y ‶⊗‶ Z) Y ‶π₁‶ v = vfst-sound X Y Z v
  sound-k X (Y ‶⊗‶ Z) Z ‶π₂‶ v = vsnd-sound X Y Z v
  sound-k X Y (Z1 ‶⊗‶ Z2) ‶⟨ e1 , e2 ⟩‶ v =
    ⟨ reflect X Z1 (eval e1 v) , reflect X Z2 (eval e2 v) ⟩ ≡⟨ ap₂ ⟨_,_⟩ (sound-k X Y Z1 e1 v) (sound-k X Y Z2 e2 v) ⟩
    ⟨ ⟦ e1 ⟧ₑ ∘ reflect X Y v , ⟦ e2 ⟧ₑ ∘ reflect X Y v ⟩   ≡˘⟨ ⟨⟩∘ _ ⟩
    ⟨ ⟦ e1 ⟧ₑ , ⟦ e2 ⟧ₑ ⟩ ∘ reflect X Y v                   ∎
  sound-k X Y Z ‶ x ‶ v = vhom-sound X Z _
```

The final soundness proof: normalizing an expression gives us the same
morphism as naively interpreting the expression.

```agda
  sound : ∀ X Y → (e : Expr X Y) → nf X Y e ≡ ⟦ e ⟧ₑ
  sound X Y e = sound-k X X Y e vid ∙ elimr (vhom-sound X X id)
```

## Solver Interface

In order to make the reflection easier later, we bundle up the soundness
proof. Marking this as abstract is *very important*. This prevents
agda from unfolding into an absolutely enormous proof when used as
a macro, which is critical for performance.

```agda
  abstract
    solve : ∀ {X Y} → (e1 e2 : Expr X Y) → nf X Y e1 ≡ nf X Y e2 → ⟦ e1 ⟧ₑ ≡ ⟦ e2 ⟧ₑ
    solve e1 e2 p = sym (sound _ _ e1) ·· p ·· sound _ _ e2
```

# Reflection

As per usual, this is the hard part. Reflection is normally quite tricky, but the
situation here is even harder than the category solver, as we need to reflect
on objects as well as morphisms.

```agda
module Reflection where

  {-# TERMINATING #-}
  build-object-expr : Product-terms → Term → TC Term
  build-object-expr ptm tm =
    (do
       x , y ← match-⊗₀ ptm tm
       x ← build-object-expr ptm x
       y ← build-object-expr ptm y
       pure (con (quote NbE._‶⊗‶_) (x v∷ y v∷ [])))
    <|>
    pure (con (quote NbE.‶Ob‶.‶_‶) (tm v∷ []))
    where open Product-terms ptm

  build-neu-hom-expr : Product-terms → Term → TC Term
  build-neu-hom-expr ptm tm = do
    x , y ← get-hom-objects cat =<< inferType tm
    x ← build-object-expr ptm x
    y ← build-object-expr ptm y
    debugPrint "tactic" 50
      [ "Building neutral hom expression: " , termErr tm
      , "\n  Has type: Hom (" , termErr x , ") (" , termErr y , ")"
      ]
    pure (con (quote NbE.Expr.‶_‶) (infer-hidden 4 $ x h∷ y h∷ tm v∷ []))
    where open Product-terms ptm

  {-# TERMINATING #-}
  build-hom-expr : Product-terms → Term → TC Term
  build-hom-expr ptm tm =
    (do
       match-id cat tm
       pure (con (quote NbE.‶id‶) []))
    <|>
    (do
       f , g ← match-∘ cat tm
       f ← build-hom-expr ptm f
       g ← build-hom-expr ptm g
       pure (con (quote NbE._‶∘‶_) (f v∷ g v∷ [])))
    <|>
    (do
       match-π₁ ptm tm
       pure (con (quote NbE.‶π₁‶) []))
    <|>
    (do
       match-π₂ ptm tm
       pure (con (quote NbE.‶π₂‶) []))
    <|>
    (do
       f , g ← match-⟨⟩ ptm tm
       f ← build-hom-expr ptm f
       g ← build-hom-expr ptm g
       pure (con (quote NbE.‶⟨_,_⟩‶) (f v∷ g v∷ [])))
    <|>
    (build-neu-hom-expr ptm tm)
    where open Product-terms ptm

  invoke-solver : Product-terms → Term → Term → Term
  invoke-solver ptm lhs rhs =
    def (quote NbE.solve) (infer-hidden 2 $ cat v∷ prod v∷ lhs v∷ rhs v∷ “refl” v∷ [])
    where open Product-terms ptm

  invoke-normaliser : Product-terms → Term → Term
  invoke-normaliser ptm e =
    def (quote NbE.solve) (infer-hidden 2 $ cat v∷ prod v∷ e v∷ [])
    where open Product-terms ptm

  product-solver
    : ∀ {o ℓ} (C : Precategory o ℓ) (has-prods : has-products C)
    → TC Simple-solver
  product-solver C has-prods = do
    ptm ← quote-product-terms C has-prods
    pure (simple-solver [] (build-hom-expr ptm) (invoke-solver ptm) (invoke-normaliser ptm))
```

Finally, we define the user-facing interface as a series of macros.

```agda
macro
  repr-products! : ∀ {o ℓ}
                   → (𝒞 : Precategory o ℓ) (cartesian : ∀ X Y → Product 𝒞 X Y)
                   → Term → Term → TC ⊤
  repr-products! C has-prods = mk-simple-repr (Reflection.product-solver C has-prods)

  simpl-products! : ∀ {o ℓ}
                    → (𝒞 : Precategory o ℓ) (cartesian : ∀ X Y → Product 𝒞 X Y)
                    → Term → Term → TC ⊤
  simpl-products! C has-prods = mk-simple-normalise (Reflection.product-solver C has-prods)

  products! : ∀ {o ℓ}
              → (𝒞 : Precategory o ℓ) (cartesian : ∀ X Y → Product 𝒞 X Y)
              → Term → TC ⊤
  products! C has-prods = mk-simple-solver (Reflection.product-solver C has-prods)
```

# Demo

Wow, that was a lot of hard work! Let's marvel at the fruits of our labor.

```agda
private module Tests {o ℓ} (𝒞 : Precategory o ℓ) (cartesian : ∀ X Y → Product 𝒞 X Y) where
  open Precategory 𝒞
  open Binary-products 𝒞 cartesian
  open NbE 𝒞 cartesian
  --
  --

  test-η : ∀ {X Y Z} → (f : Hom X (Y ⊗₀ Z))
           → f ≡ ⟨ π₁ ∘ f , π₂ ∘ f ⟩
  test-η f = products! 𝒞 cartesian

  test-β₁ : ∀ {X Y Z} → (f : Hom X Y) → (g : Hom X Z)
            → π₁ ∘ ⟨ f , g ⟩ ≡ f
  test-β₁ f g = products! 𝒞 cartesian

  test-β₂ : ∀ {X Y Z} → (f : Hom X Y) → (g : Hom X Z)
            → π₂ ∘ ⟨ f , g ⟩ ≡ g
  test-β₂ f g = products! 𝒞 cartesian

  test-⟨⟩∘ : ∀ {W X Y Z} → (f : Hom X Y) → (g : Hom X Z) → (h : Hom W X)
             → ⟨ f ∘ h , g ∘ h ⟩ ≡ ⟨ f , g ⟩ ∘ h
  test-⟨⟩∘ f g h = products! 𝒞 cartesian

  test-nested : ∀ {W X Y Z} → (f : Hom W X) → (g : Hom W Y) → (h : Hom W Z)
             → ⟨ ⟨ f , g ⟩ , h ⟩ ≡ ⟨ ⟨ f , g ⟩ , h ⟩
  test-nested {W} {X} {Y} {Z} f g h = products! 𝒞 cartesian


  test-big : ∀ {W X Y Z} → (f : Hom (W ⊗₀ X) (W ⊗₀ Y)) → (g : Hom (W ⊗₀ X) Z)
             → (π₁ ∘ ⟨ f , g ⟩) ∘ id ≡ id ∘ ⟨ π₁ , π₂ ⟩ ∘ f
  test-big f g = products! 𝒞 cartesian
```
-- 
