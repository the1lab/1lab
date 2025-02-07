<!--
```agda
open import 1Lab.Prelude

open import Data.Partial.Base
```
-->

```agda
module Data.Partial.Properties where
```

<!--
```agda
private variable
  o o' ℓ : Level
  A B C : Type ℓ

abstract
```
-->

# Properties of partial elements

This module establishes some elementary properties of [[partial
elements]], and the [[information ordering]] on them. First, as long as
$A$ is a [[set]], the information ordering is an actual [[poset]]:

```agda
  ⊑-refl : {x : ↯ A} → x ⊑ x
  ⊑-refl .implies x-def = x-def
  ⊑-refl .refines _     = refl

  ⊑-trans : {x y z : ↯ A} → x ⊑ y → y ⊑ z → x ⊑ z
  ⊑-trans p q .implies = q .implies ∘ p .implies
  ⊑-trans {x = x} {y} {z} p q .refines x-def =
    z .elt _ ≡⟨ q .refines (p .implies x-def) ⟩
    y .elt _ ≡⟨ p .refines x-def ⟩
    x .elt _ ∎

  ⊑-antisym : {x y : ↯ A} → x ⊑ y → y ⊑ x → x ≡ y
  ⊑-antisym {x = x} {y = y} p q = part-ext (p .implies) (q .implies) λ xd yd →
    ↯-indep x ∙ q .refines yd
```

We actually have that `never`{.Agda} is the [[bottom element]], as
claimed:

```agda
  never-⊑ : {x : ↯ A} → never ⊑ x
  never-⊑ .implies ()
  never-⊑ .refines ()
```

Our mapping operation preserves ordering, is functorial, and preserves
the bottom element:

```agda
  part-map-⊑
    : ∀ {f : A → B} {x y : ↯ A}
    → x ⊑ y → part-map f x ⊑ part-map f y
  part-map-⊑         p .implies   = p .implies
  part-map-⊑ {f = f} p .refines d = ap f (p .refines d)

  part-map-id : ∀ (x : ↯ A) → part-map (λ a → a) x ≡ x
  part-map-id x = part-ext id id λ _ _ →
    ↯-indep x

  part-map-∘
    : ∀ (f : B → C) (g : A → B)
    → ∀ (x : ↯ A) → part-map (f ∘ g) x ≡ part-map f (part-map g x)
  part-map-∘ f g x = part-ext id id λ _ _ →
    ap (f ∘ g) (↯-indep x)

  part-map-never : ∀ {f : A → B} {x} → part-map f never ⊑ x
  part-map-never .implies ()
  part-map-never .refines ()
```

Finally, we can characterise the adjunction-unit-to-be, `always`{.Agda}.

```agda
  always-inj : {x y : A} → always x ≡ always y → x ≡ y
  always-inj {x = x} p =
    J (λ y p → (d : ⌞ y ⌟) → x ≡ y .elt d) (λ _ → refl) p tt

  always-⊑ : {x : ↯ A} {y : A} → (∀ d → x .elt d ≡ y) → x ⊑ always y
  always-⊑ p .implies _ = tt
  always-⊑ p .refines d = sym (p d)

  always-⊒ : {x : A} {y : ↯ A} → y ↓ x → always x ⊑ y
  always-⊒ (p , q) .implies _ = p
  always-⊒ (p , q) .refines _ = q

  always-natural : {x : A} (f : A → B) → part-map f (always x) ≡ always (f x)
  always-natural f = part-ext (λ _ → tt) (λ _ → tt) λ _ _ → refl
```
