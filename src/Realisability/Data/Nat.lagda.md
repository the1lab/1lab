<!--
```agda
open import 1Lab.Prelude

open import Data.Partial.Total
open import Data.Partial.Base
open import Data.Vec.Base

open import Realisability.PCA

import Realisability.PCA.Fixpoint
import Realisability.Data.Bool
import Realisability.Data.Pair
import Realisability.PCA.Sugar
```
-->

```agda
module Realisability.Data.Nat {ℓ} (𝔸 : PCA ℓ) where
```

<!--
```agda
open Realisability.PCA.Fixpoint 𝔸
open Realisability.PCA.Sugar 𝔸
open Realisability.Data.Pair 𝔸
open Realisability.Data.Bool 𝔸
private variable
  f g x y z : ↯ ⌞ 𝔸 ⌟
```
-->

# Natural numbers in a PCA {defines="numbers-in-a-pca"}

We define an encoding of [[natural numbers]] in a [[partial combinatory
algebra]] using **Curry numerals**, which uses the encoding of
[[booleans in a PCA]] and [[pairs in a PCA]]. The number zero is simply
the identity function, and the successor of a number is given by pairing
`` `false ``{.Agda} with that number. The first component of the pair
thus encodes whether the number is zero.

```agda
`zero : ↯⁺ 𝔸
`zero = val ⟨ x ⟩ x

`suc : ↯⁺ 𝔸
`suc = val ⟨ x ⟩ `false `, x
```

Note that while the identity function may not *look like* a pair, since
in our encoding projection from $p$ is implemented by applying *$p$
itself* to either `` `true ``{.Agda} (for the first component) or ``
`false ``{.Agda} (for the second), the identity function actually
behaves extensionally like the pairing of `` `true ``{.Agda} and ``
`false ``{.Agda}.

```agda
`iszero : ↯⁺ 𝔸
`iszero = `fst
```

By recursion we can encode any number as a value of $\bA$.

```agda
`num : Nat → ↯⁺ 𝔸
`num zero    = `zero
`num (suc x) = record
  { fst = `pair ⋆ `false ⋆ `num x
  ; snd = `pair↓₂ (abs↓ _ _) (`num x .snd)
  }
```

We can define the predecessor function succinctly using a conditional:

```agda
`pred : ↯⁺ 𝔸
`pred = val ⟨ x ⟩ `if (`fst `· x) then `zero else (`snd `· x)
```

<details>
<summary>The usual arguments show that these functions all compute as expected.</summary>

```agda
abstract
  `num-suc : ∀ x → `num (suc x) .fst ≡ `suc ⋆ `num x
  `num-suc x = sym (abs-β _ _ (`num x))

  `suc↓₁ : ⌞ x ⌟ → ⌞ `suc ⋆ x ⌟
  `suc↓₁ ah = subst ⌞_⌟ (sym (abs-βₙ []v ((_ , ah) ∷v []v))) (`pair↓₂ (`false .snd) ah)

  `iszero-zero : `iszero ⋆ `zero ≡ `true .fst
  `iszero-zero = abs-β _ _ `zero ∙ abs-β _ _ (_ , abs↓ _ _)

  `iszero-suc : ⌞ x ⌟ → `iszero ⋆ (`suc ⋆ x) ≡ `false .fst
  `iszero-suc {x} xh =
    `iszero ⋆ (`suc ⋆ x)           ≡⟨ ap (`iszero ⋆_) (abs-β _ _ (_ , xh)) ⟩
    `iszero ⋆ (`pair ⋆ `false ⋆ x) ≡⟨ `fst-β (`false .snd) xh ⟩
    `false .fst                    ∎

  `pred-zero : `pred ⋆ `zero ≡ `zero .fst
  `pred-zero =
    `pred ⋆ `zero                             ≡⟨ abs-β _ _ `zero ⟩
    ⌜ `fst ⋆ `zero ⌝ ⋆ `zero ⋆ (`snd ⋆ `zero) ≡⟨ ap (λ e → e ⋆ `zero ⋆ (`snd ⋆ `zero)) (`iszero-zero) ⟩
    `true ⋆ `zero ⋆ (`snd ⋆ `zero)            ≡⟨ abs-βₙ []v ((_ , subst ⌞_⌟ (sym rem₁) (abs↓ _ _)) ∷v `zero ∷v []v) ⟩
    `zero .fst                                ∎
    where
      rem₁ : `snd ⋆ `zero ≡ `false .fst
      rem₁ = abs-β _ _ `zero ∙ abs-β _ _ `false

  `pred-suc : ⌞ x ⌟ → `pred ⋆ (`suc ⋆ x) ≡ x
  `pred-suc {x} xh =
    `pred ⋆ (`suc ⋆ x)                                   ≡⟨ abs-β _ _ (_ , `suc↓₁ xh) ⟩
    ⌜ `fst ⋆ (`suc ⋆ x) ⌝ ⋆ `zero ⋆ (`snd ⋆ (`suc ⋆ x))  ≡⟨ ap (λ e → e ⋆ `zero ⋆ (`snd ⋆ (`suc ⋆ x))) (ap (`fst ⋆_) (abs-β _ _ (_ , xh)) ∙ `fst-β (`false .snd) xh) ⟩
    `false ⋆ `zero ⋆ ⌜ `snd ⋆ (`suc ⋆ x) ⌝               ≡⟨ ap (λ e → (`false ⋆ `zero) ⋆ e) (ap (`snd ⋆_) (abs-β _ _ (_ , xh)) ∙ `snd-β (`false .snd) xh) ⟩
    `false ⋆ `zero ⋆ x                                   ≡⟨ abs-βₙ []v ((_ , xh) ∷v `zero ∷v []v) ⟩
    x                                                    ∎

```

</details>

## Primitive recursion

We define a recursor for natural numbers using the `` `Z ``{.Agda}
fixed-point combinator. This will be a program $\tt{primrec}$ which
satisfies

$$
\begin{align*}
\tt{primrec}\, z\, s\, \tt{zero}      =&\ z\\
\tt{primrec}\, z\, s\, (\tt{suc}\, x) =&\ s\ x\ (\tt{primrec}\, z\, s\, x)\text{.}
\end{align*}
$$

First we define a worker function which is parametrised over both the
'recursive reference' and all the arguments of the recursor (the zero
and successor "cases" and the number itself). We can then apply `` `Z
``{.Agda} to everything to 'tie the knot'.

Note that, to ensure everything is properly defined, our `` `worker
``{.Agda} function produces cases that take an extra dummy argument; and
our invocation of both its fixed point and its 'recursive reference'
pass `` `zero ``{.Agda} to get rid of this.

```agda
private
  `worker : ↯⁺ 𝔸
  `worker = val ⟨ rec ⟩ ⟨ zc ⟩ ⟨ sc ⟩ ⟨ num ⟩
    `if (`iszero `· num)
      then (`true `· zc)
      else (⟨ y ⟩ sc `· (`pred `· num) `· (rec `· zc `· sc `· (`pred `· num) `· `zero))

`primrec : ↯⁺ 𝔸
`primrec = val ⟨ z ⟩ ⟨ s ⟩ ⟨ n ⟩ `Z `· `worker `· z `· s `· n `· `zero
```

<details>
<summary>The typical PCA calculation fanfare shows us that `` `primrec
``{.Agda} is defined when applied to both one and two arguments, and
that it computes as stated.
</summary>

```agda
abstract
  `primrec↓₁ : ⌞ z ⌟ → ⌞ `primrec ⋆ z ⌟
  `primrec↓₁ zh = subst ⌞_⌟ (sym (abs-βₙ []v ((_ , zh) ∷v []v))) (abs↓ _ _)

  `primrec↓₂ : ⌞ z ⌟ → ⌞ f ⌟ → ⌞ `primrec ⋆ z ⋆ f ⌟
  `primrec↓₂ zh fh = subst ⌞_⌟ (sym (abs-βₙ []v ((_ , fh) ∷v (_ , zh) ∷v []v))) (abs↓ _ _)

  `primrec-zero : ⌞ z ⌟ → ⌞ f ⌟ → `primrec ⋆ z ⋆ f ⋆ `zero ≡ z
  `primrec-zero {z} {f} zh fh =
    `primrec ⋆ z ⋆ f ⋆ `zero                                     ≡⟨ abs-βₙ []v (`zero ∷v (_ , fh) ∷v (_ , zh) ∷v []v) ⟩
    ⌜ `Z ⋆ `worker ⋆ z ⌝ ⋆ f ⋆ `zero ⋆ `zero                     ≡⟨ ap (λ e → e ⋆ f ⋆ `zero ⋆ `zero) (`Z-β (`worker .snd) zh) ⟩
    ⌜ `worker ⋆ (`Z ⋆ `worker) ⋆ z ⋆ f ⋆ `zero ⌝ ⋆ `zero         ≡⟨ ap (λ e → e ⋆ `zero) (abs-βₙ []v (`zero ∷v (_ , fh) ∷v (_ , zh) ∷v (_ , `Z↓₁ (`worker .snd)) ∷v []v)) ⟩
    ⌜ `iszero ⋆ `zero ⋆ (`true ⋆ z) ⌝ % _ % `zero .fst           ≡⟨ ap₂ _%_ (ap₂ _%_ (ap₂ _%_ `iszero-zero refl) refl ∙ `true-β (`true↓₁ zh) (abs↓ _ _)) refl ⟩
    `true ⋆ z ⋆ `zero .fst                                       ≡⟨ `true-β zh (`zero .snd) ⟩
    z                                                            ∎

  `primrec-suc : ⌞ z ⌟ → ⌞ f ⌟ → ⌞ x ⌟ → `primrec ⋆ z ⋆ f ⋆ (`suc ⋆ x) ≡ f ⋆ x ⋆ (`primrec ⋆ z ⋆ f ⋆ x)
  `primrec-suc {z} {f} {x} zh fh xh =
    `primrec ⋆ z ⋆ f ⋆ (`suc ⋆ x)                                                 ≡⟨ abs-βₙ []v ((_ , `suc↓₁ xh) ∷v (_ , fh) ∷v (_ , zh) ∷v []v) ⟩
    ⌜ `Z ⋆ `worker ⋆ z ⌝ ⋆ f ⋆ (`suc ⋆ x) ⋆ `zero                                 ≡⟨ ap (λ e → e ⋆ f ⋆ (`suc ⋆ x) ⋆ `zero) (`Z-β (`worker .snd) zh) ⟩
    `worker ⋆ (`Z ⋆ `worker) ⋆ z ⋆ f ⋆ (`suc ⋆ x) ⋆ `zero                         ≡⟨ ap (λ e → e % `zero .fst) (abs-βₙ []v ((_ , `suc↓₁ xh) ∷v (_ , fh) ∷v (_ , zh) ∷v (_ , `Z↓₁ (`worker .snd)) ∷v []v)) ⟩
    `iszero ⋆ (`suc ⋆ x) ⋆ (`true ⋆ z) % _ % `zero .fst                           ≡⟨ ap₂ _%_ (ap₂ _%_ (ap₂ _%_ (`iszero-suc xh) refl) refl ∙ `false-β (`true↓₁ zh) (abs↓ _ _)) refl ∙ abs-βₙ ((`suc ⋆ x , `suc↓₁ xh) ∷v (f , fh) ∷v (z , zh) ∷v (`Z ⋆ `worker , `Z↓₁ (`worker .snd)) ∷v []v) (`zero ∷v []v) ⟩
    f % `pred ⋆ (`suc ⋆ x) % `Z ⋆ `worker ⋆ z ⋆ f ⋆ (`pred ⋆ (`suc ⋆ x)) ⋆ `zero  ≡⟨ ap (λ e → f % e % `Z ⋆ `worker ⋆ z ⋆ f ⋆ e ⋆ `zero) (`pred-suc xh) ⟩
    f ⋆ x ⋆ (`Z ⋆ `worker ⋆ z ⋆ f ⋆ x ⋆ `zero)                                    ≡⟨ ap₂ _%_ refl (sym (abs-βₙ []v ((_ , xh) ∷v (_ , fh) ∷v (_ , zh) ∷v []v))) ⟩
    f ⋆ x ⋆ (`primrec ⋆ z ⋆ f ⋆ x)                                                ∎
```

</details>
