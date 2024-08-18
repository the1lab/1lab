---
description: |
  General properties of PCAs.
---
<!--
```agda
open import 1Lab.Prelude

open import Data.Fin
open import Data.Vec.Base

open import Realizability.PAS
open import Realizability.PCA
```
-->
```agda
module Realizability.PCA.Properties where
```

# Properties of PCAs

<!--
```agda
module _ {ℓ : Level} {A : Type ℓ} (pca : PCA-on A) where
  open PCA pca
```
-->

PCAs are algebraic structures equipped with a binary operation, so
we might hope that $\star$ obeys some normal algebraic equations.
Unfortunately, this is not the case, and imposing most laws actually
causes the PCA to be trivial!

First, note if $\star$ is associative, then then the PCA *must* be trivial!
The problem comes when we reassociate `“const”`{.Agda}, as we can turn
`“const” ⋆ (“const” ⋆ “const”)` into `(“const” ⋆ “const”) ⋆ “const”`,
which has *very* different computational behaviour!

```agda
  ⋆-assoc→trivial : (∀ a b c → a ⋆ (b ⋆ c) ≡ (a ⋆ b) ⋆ c) → is-contr Val
  ⋆-assoc→trivial ⋆-assoc = contr (value “const” const-def) λ (value x x↓) → ext $
    “const”                                         ≡˘⟨ const-eval “const” “const” const-def ⟩
    “const” ⋆ “const” ⋆ “const”                     ≡˘⟨ ap (_⋆ “const”) (const-eval (“const” ⋆ “const”) x x↓) ⟩
    ⌜ “const” ⋆ (“const” ⋆ “const”) ⌝ ⋆ x ⋆ “const” ≡⟨ ap! (⋆-assoc _ _ _ ∙ const-eval “const” “const” const-def) ⟩
    “const” ⋆ x ⋆ “const”                           ≡⟨ const-eval x “const” const-def ⟩
    x                                               ∎
```

In a similar vein, if $\star$ is commutative, then the PCA must be trivial.
We begin with a useful little lemma: if `“const”`{.Agda} is the same as
`“ignore”`{.Agda}, then the PCA is trivial[^1].

[^1]: We actually prove a more general result: if *any* two terms that
meet the computational specifications of `“const”`{.Agda} and `“ignore”`{.Agda}
are equal, then the PCA is trivial.

```agda
  const=ignore→trivial
    : ∀ k k'
    → (∀ x y → ∣ y ↓ ∣ → k ⋆ x ⋆ y ≡ x)
    → (∀ x y → ∣ x ↓ ∣ → k' ⋆ x ⋆ y ≡ y)
    → k ≡ k'
    → is-contr Val
  const=ignore→trivial k k' k-eval k'-eval k=k' =
    contr (value “const” const-def) λ (value x x↓) → ext $
    “const”                    ≡˘⟨ k'-eval x “const” x↓ ⟩
    ⌜ k' ⌝ ⋆ x ⋆ “const”       ≡⟨ ap! (sym k=k') ⟩
    k ⋆ x ⋆ “const”            ≡⟨ k-eval x “const” const-def ⟩
    x                          ∎
```

Commutativity implying triviality follows from a bit of easy algebra.

```agda
  ⋆-comm→trivial : (∀ a b → a ⋆ b ≡ b ⋆ a) → is-contr Val
  ⋆-comm→trivial ⋆-comm =
    const=ignore→trivial “const” “ignore” const-eval ignore-eval $
    “const”                          ≡˘⟨ ignore-eval “const” “const” const-def ⟩
    ⌜ “ignore” ⋆ “const” ⌝ ⋆ “const” ≡⟨ ap! (⋆-comm “ignore” “const”) ⟩
    “const” ⋆ “ignore” ⋆ “const”     ≡⟨ const-eval “ignore” “const” const-def ⟩
    “ignore” ∎
```

In the spirit of our previous lemma, if 2 terms that meet the computational
specifications of `“ignore”`{.Agda} and `“id”`{.Agda} are equal, then
the PCA is trivial.

```agda
  ignore=id→trivial
    : ∀ k' i
    → (∀ x y → ∣ x ↓ ∣ → k' ⋆ x ⋆ y ≡ y)
    → (∀ x → i ⋆ x ≡ x)
    → k' ≡ i
    → is-contr Val
  ignore=id→trivial k' i k'-eval i-eval ignore=id =
    contr (value “const” const-def) λ (value x x↓) → ext $
    “const”                          ≡˘⟨ k'-eval (“const” ⋆ x) “const” (const-def₁ x↓) ⟩
    ⌜ k' ⌝ ⋆ (“const” ⋆ x) ⋆ “const” ≡⟨ ap! ignore=id ⟩
    i ⋆ (“const” ⋆ x) ⋆ “const”      ≡⟨ ap (_⋆ “const”) (i-eval (“const” ⋆ x)) ⟩
    “const” ⋆ x ⋆ “const”            ≡⟨ const-eval x “const” const-def ⟩
    x                                ∎
```

This lets us show that if `“s”`{.Agda} and `“const”`{.Agda} are equal,
then the PCA is trivial. This result is of particular interest, as
these terms [[form a basis|completeness-of-s-and-k]] for PCAs.

```agda
  s=const→trivial
    : ∀ s k
    → (∀ x y → ∣ y ↓ ∣ → k ⋆ x ⋆ y ≡ x)
    → (∀ x y z → s ⋆ x ⋆ y ⋆ z ≡ x ⋆ z ⋆ (y ⋆ z))
    → s ≡ k
    → is-contr Val
  s=const→trivial s k k-eval s-eval s=k =
    ignore=id→trivial (“const” ⋆ “id”) “id” ki-eval id-eval $
    “const” ⋆ “id”                         ≡˘⟨ ap (_⋆ “id”) (k-eval “const” “const” const-def) ⟩
    ⌜ k ⌝ ⋆ “const” ⋆ “const” ⋆ “id”       ≡⟨ ap! (sym s=k) ⟩
    s ⋆ “const” ⋆ “const” ⋆ “id”           ≡⟨ s-eval “const” “const” “id” ⟩
    “const” ⋆ “id” ⋆ (“const” ⋆ “id”)      ≡⟨ const-eval “id” (“const” ⋆ “id”) (const-def₁ id-def) ⟩
    “id”                                   ∎
    where
      ki-eval : ∀ x y → ∣ x ↓ ∣ → “const” ⋆ “id” ⋆ x ⋆ y ≡ y
      ki-eval x y x↓ = ap (_⋆ y) (const-eval “id” x x↓) ∙ id-eval y
```
