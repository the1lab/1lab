<!--
```agda
open import 1Lab.Function.Embedding
open import 1Lab.HLevel.Closure
open import 1Lab.Type.Pi
open import 1Lab.HLevel
open import 1Lab.Path
open import 1Lab.Type
```
-->

```agda
module Data.Wellfounded.Base where
```

# Well-founded relations {defines="well-founded"}

Well-founded relations are, in essence, orders over which _induction_ is
acceptable. A relation is well-founded if all of its chains have bounded
length, which we can summarize with the following inductive definition
of **accessibility**:

<!--
```agda
module _ {ℓ ℓ'} {A : Type ℓ} (_<_ : A → A → Type ℓ') where
```
-->

```agda
  data Acc (x : A) : Type (ℓ ⊔ ℓ') where
    acc : (∀ y → y < x → Acc y) → Acc x
```

That is, an element $x : A$ is accessible if every element $y < x$ under
it (by the relation $<$) is also accessible. Paraphrasing the HoTT book,
it may seem like such a definition can never get started, but the "base
case" is when there are _no_ elements $y < x$ --- for example, taking
$<$ to be the usual $<$ on the natural numbers, there are no numbers $y
< 0$, so $0$ is accessible.

A relation is **well-founded** if every $x : A$ is accessible.

```agda
  Wf : Type _
  Wf = ∀ x → Acc x
```

Being well-founded implies that we support induction, and conversely,
any relation supporting induction is well-founded, by taking the motive
$P$ to be the proposition "$x$ is accessible".

```agda
  Wf-induction'
    : ∀ {ℓ'} (P : A → Type ℓ')
    → (∀ x → (∀ y → y < x → P y) → P x)
    → ∀ x → Acc x → P x
  Wf-induction' P work = go where
    go : ∀ x → Acc x → P x
    go x (acc w) = work x (λ y y<x → go y (w y y<x))

  Wf-induction
    : Wf → ∀ {ℓ'} (P : A → Type ℓ')
    → (∀ x → (∀ y → y < x → P y) → P x)
    → ∀ x → P x
  Wf-induction wf P work x = Wf-induction' P work x (wf x)

  Induction-wf
    : (∀ {ℓ'} (P : A → Type ℓ') → (∀ x → (∀ y → y < x → P y) → P x) → ∀ x → P x)
    → Wf
  Induction-wf ind = ind Acc (λ _ → acc)
```

<!--
```agda
  Wf-induction₂
    : Wf → ∀ {ℓ'} (P : A → A → Type ℓ')
    → (∀ x y
       → (∀ a → a < x → P a y)
       → (∀ b → b < y → P x b)
       → (∀ a b → a < x → b < y → P a b)
       → P x y)
    → ∀ x y → P x y
  Wf-induction₂ wf P work x y = go x y (wf x) (wf y) where
    go : ∀ x y → Acc x → Acc y → P x y
    go x y (acc p) (acc q) =
      work x y
        (λ a a<x → go a y (p a a<x) (acc q))
        (λ b b<y → go x b (acc p) (q b b<y))
        (λ a b a<x b<y → go a b (p a a<x) (q b b<y))
```
-->

Somewhat surprisingly, being accessible is a proposition! We can prove
this via induction.

<!--
```agda
private variable
  ℓ : Level
  A B : Type ℓ
  R : A → A → Type ℓ
```
-->

```agda
Acc-is-prop : ∀ x → is-prop (Acc R x)
Acc-is-prop x (acc s) (acc t) =
  ap acc (funext (λ y → funext λ y<x → Acc-is-prop y (s y y<x) (t y y<x)))
```

This directly implies that being well-founded is also a proposition.

```agda
Wf-is-prop : is-prop (Wf R)
Wf-is-prop = Π-is-hlevel 1 Acc-is-prop
```

## Properties of well-founded relations

We can pull back any well-founded relation along an arbitrary function
$A \to B$.

```agda
pullback-wf
  : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'}
  → {R : B → B → Type ℓ''}
  → Wf R
  → (f : A → B)
  → Wf (R on f)
pullback-wf wf f x = go x (wf (f x)) where
  go : ∀ x → Acc R (f x) → Acc (R on f) x
  go x (acc w) = acc λ y r → go y (w (f y) r)
```
