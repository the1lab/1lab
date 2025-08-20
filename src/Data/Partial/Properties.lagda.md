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
  A B C X Y : Type ℓ

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

## Programming with partial elements

The partial element monad is quite odd from a programming perspective.
First, note that if $X$ is a proposition, then we can summon up an element
of $\zap X$ seemingly out of the void.

```agda
assume↯ : (X : Type ℓ) → is-prop X → ↯ X
assume↯ X X-prop .def = elΩ X
assume↯ X X-prop .elt = □-out X-prop
```

We can use a similar trick to create an element of $\zap X$ for an *arbitrary*
type $X$ by using `is-contr X` as our domain of definition. This gives rise
to a sort of definite description principle for $\zap$.

```agda
desc↯ : (X : Type ℓ) → ↯ X
desc↯ X .def = elΩ (is-contr X)
desc↯ X .elt □contr = □-out! □contr .centre
```



## Partial elements are injective types {defines=partial-elements-are-injective}

The type of partial elements $\zap X$ is an [[injective object]] for
every set $X$.

First, observe that we can extend a map $f : X \to \zap A$ along
an [[embedding]] $e : X \to Y$ by using `assume↯`{.Agda} to cook up
a fibre of $x$ that we can

```agda
extend↯ : (X → ↯ A) → (X ↪ Y) → Y → ↯ A
extend↯ f e y = do
  x ← assume↯ (fibre (apply e) y) (e .snd y)
  f (x .fst)
```

```agda
extends↯
  : ⦃ _ : H-Level A 2 ⦄
  → (f : X → ↯ A) (e : X ↪ Y)
  → ∀ (x : X) → extend↯ f e (e · x) ≡ f x
extends↯ f e x =
  part-ext
    (rec! (λ x' p fx'↓ → subst (λ x → ∣ f x .def ∣) (has-prop-fibres→injective (e .fst) (e .snd) p) fx'↓))
    (λ fx↓ → (pure (x , refl)) , fx↓)
    (elim! (λ x' p fx'↓ fx↓ → ap₂ (λ x fx↓ → f x .elt fx↓) (has-prop-fibres→injective (e .fst) (e .snd) p) prop!))
```
