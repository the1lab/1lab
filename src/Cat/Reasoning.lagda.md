```agda
open import 1Lab.Path

open import Cat.Base

module Cat.Reasoning {o ℓ} (C : Precategory o ℓ) where

open import Cat.Morphism C public
```

# Reasoning Combinators for Categories

When doing category theory, we often have to perform many "trivial"
algebraic manipulations like reassociation, insertion of identity morphisms, etc.
On paper we can omit these steps, but Agda is a bit more picky!
We could just do these steps in our proofs one after another, but this
clutters things up. Instead, we provide a series of reasoning combinators
to make writing (and reading) proofs easier.

Most of these helpers were taken from `agda-categories`.

<!--
```agda
private variable
  x y : Ob
  a a′ a″ b b′ b″ c c′ c″ : Hom x y
  f g h i : Hom x y
```
-->

## Identity Morphisms

```agda
id-comm : ∀ {a b} {f : Hom a b} → f ∘ id ≡ id ∘ f
id-comm {f = f} = idr f ∙ sym (idl f)

id-comm-sym : ∀ {a b} {f : Hom a b} → id ∘ f ≡ f ∘ id
id-comm-sym {f = f} = idl f ∙ sym (idr f)

module _ (a≡id : a ≡ id) where

  eliml : a ∘ f ≡ f
  eliml {f = f} =
    a ∘ f ≡⟨ ap (_∘ f) a≡id ⟩
    id ∘ f ≡⟨ idl f ⟩
    f ∎

  elimr : f ∘ a ≡ f
  elimr {f = f} =
    f ∘ a ≡⟨ ap (f ∘_) a≡id ⟩
    f ∘ id ≡⟨ idr f ⟩
    f ∎

  introl : f ≡ a ∘ f
  introl = sym eliml

  intror : f ≡ f ∘ a
  intror = sym elimr
```

## Reassocations

We often find ourselves in situations where we have an equality
involving the composition of 2 morphisms, but the association
is a bit off. These combinators aim to address that situation.

```agda
module _ (ab≡c : a ∘ b ≡ c) where

  pulll : a ∘ (b ∘ f) ≡ c ∘ f
  pulll {f = f} =
    a ∘ b ∘ f   ≡⟨ assoc a b f ⟩
    (a ∘ b) ∘ f ≡⟨ ap (_∘ f) ab≡c ⟩
    c ∘ f ∎

  pullr : (f ∘ a) ∘ b ≡ f ∘ c
  pullr {f = f} =
    (f ∘ a) ∘ b ≡˘⟨ assoc f a b ⟩
    f ∘ (a ∘ b) ≡⟨ ap (f ∘_) ab≡c ⟩
    f ∘ c ∎

module _ (c≡ab : c ≡ a ∘ b) where

  pushl : c ∘ f ≡ a ∘ (b ∘ f)
  pushl = sym (pulll (sym c≡ab))

  pushr : f ∘ c ≡ (f ∘ a) ∘ b
  pushr = sym (pullr (sym c≡ab))

module _ (p : f ∘ h ≡ g ∘ i) where
  extendl : f ∘ (h ∘ b) ≡ g ∘ (i ∘ b)
  extendl {b = b} =
    f ∘ (h ∘ b) ≡⟨ assoc f h b ⟩
    (f ∘ h) ∘ b ≡⟨ ap (_∘ b) p ⟩
    (g ∘ i) ∘ b ≡˘⟨ assoc g i b ⟩
    g ∘ (i ∘ b) ∎

  extendr : (a ∘ f) ∘ h ≡ (a ∘ g) ∘ i
  extendr {a = a} =
    (a ∘ f) ∘ h ≡˘⟨ assoc a f h ⟩
    a ∘ (f ∘ h) ≡⟨ ap (a ∘_) p ⟩
    a ∘ (g ∘ i) ≡⟨ assoc a g i ⟩
    (a ∘ g) ∘ i ∎

  extend-inner : a ∘ f ∘ h ∘ b ≡ a ∘ g ∘ i ∘ b
  extend-inner {a = a} = ap (a ∘_) extendl
```

## Cancellation

These lemmas do 2 things at once: rearrange parenthesis, and also remove
things that are equal to `id`.

```agda
module _ (inv : h ∘ i ≡ id) where

  cancell : h ∘ (i ∘ f) ≡ f
  cancell {f = f} =
    h ∘ (i ∘ f) ≡⟨ pulll inv ⟩
    id ∘ f ≡⟨ idl f ⟩
    f ∎

  cancelr : (f ∘ h) ∘ i ≡ f
  cancelr {f = f} =
    (f ∘ h) ∘ i ≡⟨ pullr inv ⟩
    f ∘ id ≡⟨ idr f ⟩
    f ∎

  insertl : f ≡ h ∘ (i ∘ f)
  insertl = sym cancell

  insertr : f ≡ (f ∘ h) ∘ i
  insertr = sym cancelr

  cancel-inner : (f ∘ h) ∘ (i ∘ g) ≡ f ∘ g
  cancel-inner = pulll cancelr
```

## Isomorphisms

These lemmas are useful for proving that partial inverses to an
isomorphism are unique. There's a helper for proving uniqueness of left
inverses, of right inverses, and for proving that any left inverse must
match any right inverse.

```agda
module _ {y z} (f : y ≅ z) where
  open _≅_

  left-inv-unique
    : ∀ {g h}
    → g ∘ f .to ≡ id → h ∘ f .to ≡ id
    → g ≡ h
  left-inv-unique {g = g} {h = h} p q =
    g                   ≡⟨ intror (f .invl) ⟩
    g ∘ f .to ∘ f .from ≡⟨ extendl (p ∙ sym q) ⟩
    h ∘ f .to ∘ f .from ≡⟨ elimr (f .invl) ⟩
    h                   ∎

  left-right-inv-unique
    : ∀ {g h}
    → g ∘ f .to ≡ id → f .to ∘ h ≡ id
    → g ≡ h
  left-right-inv-unique {g = g} {h = h} p q =
    g                    ≡⟨ intror (f .invl) ⟩
    g ∘ f .to ∘ f .from  ≡⟨ cancell p ⟩
    f .from              ≡⟨ intror q ⟩
    f .from ∘ f .to ∘ h  ≡⟨ cancell (f .invr) ⟩
    h                    ∎

  right-inv-unique
    : ∀ {g h}
    → f .to ∘ g ≡ id → f .to ∘ h ≡ id
    → g ≡ h
  right-inv-unique {g = g} {h} p q =
    g                     ≡⟨ introl (f .invr) ⟩
    (f .from ∘ f .to) ∘ g ≡⟨ pullr (p ∙ sym q) ⟩
    f .from ∘ f .to ∘ h   ≡⟨ cancell (f .invr) ⟩
    h                     ∎
```

## Notation

When doing equational reasoning, it's often somewhat clumsy to have to write
`ap (f ∘_) p` when proving that `f ∘ g ≡ f ∘ h`. To fix this, we define steal
some cute mixfix notation from `agda-categories` which allows us to write
`≡⟨ refl⟩∘⟨ p ⟩` instead, which is much more aesthetically pleasing!

```agda
_⟩∘⟨_ : f ≡ h → g ≡ i → f ∘ g ≡ h ∘ i
_⟩∘⟨_ = ap₂ _∘_

refl⟩∘⟨_ : g ≡ h → f ∘ g ≡ f ∘ h
refl⟩∘⟨_ {f = f} p = ap (f ∘_) p

_⟩∘⟨refl : f ≡ h → f ∘ g ≡ h ∘ g
_⟩∘⟨refl {g = g} p = ap (_∘ g) p
```

