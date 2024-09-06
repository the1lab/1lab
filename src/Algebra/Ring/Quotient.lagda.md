<!--
```agda
open import Algebra.Group.Cat.Base
open import Algebra.Group.Subgroup
open import Algebra.Ring.Ideal
open import Algebra.Group
open import Algebra.Ring

open import Cat.Prelude hiding (_*_ ; _+_)

open import Data.Power
open import Data.Dec

import Algebra.Ring.Reasoning as Kit
```
-->

```agda
module Algebra.Ring.Quotient {ℓ} (R : Ring ℓ) where
```

<!--
```agda
open Ring-on (R .snd)
private module R = Kit R
```
-->

# Quotient rings

Let $R$ be a [[ring]] and $I \sube R$ be an ideal. Because rings have an
underlying [[abelian group]], the ideal $I \sube R$ determines a normal
subgroup $I$ of $R$'s additive group, so that we may form the quotient
group $R/I$. And since ideals are closed under multiplication^[recall
that all our rings are commutative, so they're closed under
multiplication by a constant on either side], we can extend $R$'s
multiplication to a multiplication operation on $R/I$ in a canonical
way! In that case, we refer to $R/I$ as a **quotient ring**.

[quotient group]: Algebra.Group.Subgroup.html#representing-kernels

<!--
```agda
module _ {I : ℙ ⌞ R ⌟} (idl : is-ideal R I) where
  private module I = is-ideal idl
```
-->

Really, the bulk of the construction has already been done (in the
section about quotient groups), so all that remains is the following
construction: We want to show that $xy$ is invariant under equivalence
for both $x$ and $y$ (and we may treat them separately for
comprehensibility's sake).

<!--
```agda
  private
    quot-grp : Group _
    quot-grp = R.additive-group /ᴳ I.ideal→normal
    module R/I = Group-on (quot-grp .snd) hiding (magma-hlevel)
```
-->

```agda
    quot-mul : ⌞ quot-grp ⌟ → ⌞ quot-grp ⌟ → ⌞ quot-grp ⌟
    quot-mul =
      Coeq-rec₂ squash (λ x y → inc (x R.* y))
        (λ a (_ , _ , r) → p1 a r)
        (λ a (_ , _ , r) → p2 a r)
      where
```

On one side, we must show that $[ax] = [ay]$ supposing that $[x] = [y]$,
i.e. that $(x - y) \in I$. But since $I$ is an ideal, we have $(ax - ay)
\in I$, thus $[ax] = [ay]$. And on the other side, we have the same
thing: Since $(x - y) \in I$, also $(xa - ya) \in I$, so $[xa] = [ya]$.

```agda
      p1 : ∀ a {x y} (r : (x R.- y) ∈ I) → inc (x R.* a) ≡ inc (y R.* a)
      p1 a {x} {y} x-y∈I = quot $ subst (_∈ I)
        (R.*-distribr ∙ ap (x R.* a R.+_) R.*-negatel)
        (I.has-*ᵣ a x-y∈I)

      p2 : ∀ a {x y} (r : (x R.- y) ∈ I) → inc (a R.* x) ≡ inc (a R.* y)
      p2 a {x} {y} x-y∈I = quot $ subst (_∈ I)
        (R.*-distribl ∙ ap (a R.* x R.+_) R.*-negater)
        (I.has-*ₗ a x-y∈I)
```

<details>
<summary>Showing that this extends to a ring structure on $R/I$ is annoying, but
not non-trivial, so we keep in this `<details>`{.Agda} fold. Most of the proof is appealing to the elimination principle(s) for
quotients into propositions, then applying $R$'s laws.</summary>

```agda
  open make-ring
  make-R/I : make-ring ⌞ quot-grp ⌟
  make-R/I .ring-is-set = squash
  make-R/I .0R = inc 0r
  make-R/I ._+_ = R/I._⋆_
  make-R/I .-_ = R/I.inverse
  make-R/I .+-idl x = R/I.idl
  make-R/I .+-invr x = R/I.inverser {x}
  make-R/I .+-assoc x y z = R/I.associative {x} {y} {z}
  make-R/I .1R = inc R.1r
  make-R/I ._*_ = quot-mul
  make-R/I .+-comm = elim! λ x y → ap Coeq.inc R.+-commutes
  make-R/I .*-idl = elim! λ x → ap Coeq.inc R.*-idl
  make-R/I .*-idr = elim! λ x → ap Coeq.inc R.*-idr
  make-R/I .*-assoc = elim! λ x y z → ap Coeq.inc R.*-associative
  make-R/I .*-distribl = elim! λ x y z → ap Coeq.inc R.*-distribl
  make-R/I .*-distribr = elim! λ x y z → ap Coeq.inc R.*-distribr
```

</details>

```agda
  R/I : Ring ℓ
  R/I = to-ring make-R/I
```

As a quick aside, if $I$ is a complemented ideal (equivalently: a
decidable ideal), and $R$ is a discrete ring, then the quotient ring is
also discrete. This is a specialisation of a general result about
decidable quotient sets, but we mention it here regardless:

```agda
  Discrete-ring-quotient : (∀ x → Dec (x ∈ I)) → Discrete ⌞ R/I ⌟
  Discrete-ring-quotient dec∈I = Discrete-quotient
    (normal-subgroup→congruence R.additive-group I.ideal→normal)
    (λ x y → dec∈I (x R.- y))
```
