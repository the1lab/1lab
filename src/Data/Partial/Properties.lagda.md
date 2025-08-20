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
every type $X$.

First, observe that we can extend a map $f : X \to \zap A$ along
an [[embedding]] $e : X \to Y$ by constructing a map
a fibre of $y$ that we can pass off to $f$.

```agda
extend↯ : (X → ↯ A) → (X ↪ Y) → Y → ↯ A
extend↯ f e y .def = elΩ (Σ[ y* ∈ fibre (e .fst) y ] ⌞ f (y* .fst) ⌟)
extend↯ f e y .elt =
  □-out-rec (Σ-is-hlevel 1 (e .snd y) (λ _ → hlevel 1))
    (λ ((x , _) , fx↓) → f x .elt fx↓)
```

Proving that the extension of $f$ along $e$ with $f$ is a bit of a chore
due to all of the propositional resizing required. The key idea is that
both $f$ and its extension have equivalent domains of definition, and
agree when both are defined essentially by definition.

```agda
extends↯
  : ⦃ _ : H-Level A 2 ⦄
  → (f : X → ↯ A) (e : X ↪ Y)
  → ∀ (x : X) → extend↯ f e (e · x) ≡ f x
```

<details>
<summary>Unfortunately, proof assistants. The domain of definition
of `extends↯ f e (e · x)` is always a proposition, but we need to
truncate it to resize it into `Ω`{.Agda}. This means that we need
to wrap our proofs in a bunch of eliminators, which makes them quite
ugly.
</summary>

```agda
extends↯ f e x =
  part-ext to from agree
  where
    to : ⌞ extend↯ f e (e · x) ⌟ → ⌞ f x ⌟
    to = rec! λ x' p fx'↓ →
      subst (λ x → ∣ f x .def ∣)
        (has-prop-fibres→injective (e .fst) (e .snd) p)
        fx'↓

    from : ⌞ f x ⌟ → ⌞ extend↯ f e (e · x) ⌟
    from fx↓ = pure ((x , refl) , fx↓)

    agree : (fex↓ : ⌞ extend↯ f e (e · x) ⌟) (fx↓ : ⌞ f x ⌟) → extend↯ f e (e · x) .elt fex↓ ≡ f x .elt fx↓
    agree =
      □-out-elim (Σ-is-hlevel 1 (e .snd (e · x)) (λ _ → hlevel 1)) λ where
        ((x' , ex'=ex) , fx'↓) fx↓ →
          ap₂ (λ x fx↓ → f x .elt fx↓) (has-prop-fibres→injective (e .fst) (e .snd) ex'=ex) prop!
```
</details>
