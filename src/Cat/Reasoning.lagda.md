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
```

## Cancellation

These lemmas do 2 things at once: rearrange parenthesis, and
also remove things that are equal to `id`.

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

  cancelInner : (f ∘ h) ∘ (i ∘ g) ≡ f ∘ g
  cancelInner = pulll cancelr
```
