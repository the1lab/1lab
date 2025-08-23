<!--
```agda
open import 1Lab.Prelude

open import Data.Partial.Total
open import Data.Partial.Base
open import Data.Fin.Base
open import Data.Vec.Base

open import Realisability.PCA

import Realisability.Data.Bool
import Realisability.PCA.Sugar
```
-->

```agda
module Realisability.PCA.Trivial where
```

# Trivial PCAs

The definition of [[partial combinatory algebra]], either in terms of an
abstraction elimination procedure or using a [[complete combinatorial
basis|combinatorially complete]], does not actually mandate that any
elements are distinct. Therefore, the unit type can be equipped with the
structure of a PCA.

```agda
⊤PCA : PCA lzero
⊤PCA .fst = el! ⊤
⊤PCA .snd .PCA-on.has-is-set = hlevel 2
⊤PCA .snd .PCA-on._%_ _ _ = pure tt
```

To implement the abstraction procedure, we can simply map every term to
the constant term containing the unit value.

```agda
⊤PCA .snd .PCA-on.has-is-pca = record where
  open eval (λ _ _ → pure tt) renaming (eval to ⊤ev ; inst to ⊤inst) using ()

  abs : ∀ {n} → Term ⊤ (suc n) → Term ⊤ n
  abs _ = const (pure tt , tt)

  rem : ∀ {n} (t : Term ⊤ n) (ρ : Vec (↯⁺ ⊤) n) → ⌞ ⊤ev t ρ  ⌟
  rem = λ where
    (var x)   ρ → lookup ρ x .snd
    (const x) ρ → x .snd
    (app f x) ρ → tt

  abs-β : {n : Nat} (t : Term ⊤ (suc n)) (ρ : Vec (↯⁺ ⊤) n) (a : ↯⁺ ⊤) → _
  abs-β t ρ a = part-ext
    (λ _ → rem (⊤inst t (const a)) ρ) (λ _ → tt) λ _ _ → refl
```

<!--
```agda
module _ {ℓ} (𝔸 : PCA ℓ) where
  open Realisability.Data.Bool 𝔸
  open Realisability.PCA.Sugar 𝔸
```
-->

However, we can actually define what it means for a pca to be trivial
purely in terms of the programs it implements: if the `` `true ``{.Agda}
and `` `false ``{.Agda} programs are identical, then the pca is actually
trivial. Following this, we define:

```agda
  is-trivial-pca : Type _
  is-trivial-pca = `true .fst ≡ `false .fst
```

:::{.definition #trivial-pca alias="nontrivial-pca"}
A [[partial combinatory algebra]] $\bA$ is **trivial** when the programs
`` `true ``{.Agda} and `` `false ``{.Agda} are identical in $\bA$; this
implies that the *type* $\bA$ is a [[proposition]].
:::

```agda
  is-trivial-pca→is-prop : is-trivial-pca → is-prop ⌞ 𝔸 ⌟
  is-trivial-pca→is-prop true=false x y = always-injective $
    pure x         ≡˘⟨ `true-β tt tt ⟩
    `true  ⋆ x ⋆ y ≡⟨ ap (λ e → e % pure x % pure y) true=false ⟩
    `false ⋆ x ⋆ y ≡⟨ `false-β tt tt ⟩
    pure y         ∎
```

We define *non*triviality to simply be the negation of triviality. Note
that $\bA$ is nontrivial as soon as it contains two distinct programs,
since if we are given $x, y : \bA$, then if $\bA$ were trivial in the
sense above we would have

$$
\begin{align*}
x &= \tt{true}\  x\ y \\
  &= \tt{false}\ x\ y \\
  &= y\text{,}
\end{align*}
$$

which contradicts $x \ne y$.

```agda
  is-nontrivial-pca : Type _
  is-nontrivial-pca = `true .fst ≠ `false .fst

  two-elements→is-nontrivial : {x y : ⌞ 𝔸 ⌟} → x ≠ y → is-nontrivial-pca
  two-elements→is-nontrivial x≠y triv = x≠y (is-trivial-pca→is-prop triv _ _)
```
