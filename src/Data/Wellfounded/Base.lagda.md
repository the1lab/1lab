<!--
```agda
open import 1Lab.Path
open import 1Lab.Type
```
-->

```agda
module Data.Wellfounded.Base where
```

# Well-founded relations

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
