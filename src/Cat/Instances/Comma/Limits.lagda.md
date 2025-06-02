<!--
```agda
open import Cat.Instances.Shape.Terminal
open import Cat.Functor.Kan.Reflection
open import Cat.Diagram.Limit.Base
open import Cat.Functor.Kan.Unique
open import Cat.Functor.Naturality
open import Cat.Functor.Kan.Base
open import Cat.Instances.Comma
open import Cat.Prelude

import Cat.Functor.Reasoning as Fr
import Cat.Reasoning as Cat

open lifts-limit
```
-->

```agda
module Cat.Instances.Comma.Limits where
```

<!--
```agda
open make-is-limit
open ↓Obj
open ↓Hom
open _=>_
```
-->

# Limits in comma categories

This short note proves the following fact about [[limits]] in [[comma
categories]] of the form $d \swarrow F$: If $\cC$ has a limit $L$ for
$\operatorname{cod}\circ G$ and $F$ preserves limits the size of $G$'s
shape $\cJ$, then $L$ can be made into an object of $d \swarrow F$, and
this object is the limit of $J$.

<!--
```agda
module
  _ {o ℓ o' ℓ'} {C : Precategory o ℓ} {D : Precategory o' ℓ'} {d}
    (F : Functor C D) {lo lℓ} (F-cont : is-continuous lo lℓ F)
    {J : Precategory lo lℓ} {G : Functor J (d ↙ F)}
  where

  private
    module G = Functor G
    module D = Cat D
    module C = Cat C
    module F = Fr F
```
-->

```agda
  Cod-lift-limit : Limit (Cod _ F F∘ G) → Limit G
  Cod-lift-limit limf = to-limit (to-is-limit lim') where
    module limf = Limit limf

    flimf = F-cont limf.has-limit
    module flimf = is-limit flimf
```

The family of maps $d \to FL$ can be given componentwise, since $FL$ is
a limit in $\cD$: it suffices to give a family of maps $d \to FGj$, at
each $j : \cJ$. But $G$ sends objects of $\cJ$ to pairs which include a
map $d \to FGj$, and it does so in a way compatible with $F$, by
definition.

```agda
    apex : ⌞ d ↙ F ⌟
    apex .x = tt
    apex .y = limf.apex
    apex .map = flimf.universal (λ j → G.₀ j .map) λ f → sym (G.₁ f .sq) ∙ D.elimr refl
```

Similarly short calculations show that we can define maps in $d \swarrow
F$ into $L$ componentwise, and these satisfy the universal property.

```agda
    lim' : make-is-limit G apex
    lim' .ψ j .α = tt
    lim' .ψ j .β = limf.ψ j
    lim' .ψ j .sq = sym (flimf.factors _ _ ∙ D.intror refl)
    lim' .commutes f = ext (sym (limf.eps .is-natural _ _ _) ∙ C.elimr limf.Ext.F-id)
    lim' .universal eta p .α = tt
    lim' .universal eta p .β = limf.universal (λ j → eta j .β) λ f → ap β (p f)
    lim' .universal eta p .sq = D.elimr refl ∙ sym (flimf.unique _ _ _ λ j → F.pulll (limf.factors _ _) ∙ sym (eta j .sq) ∙ D.elimr refl)
    lim' .factors eta p = ext (limf.factors _ _)
    lim' .unique eta p other q = ext (limf.unique _ _ _ λ j → ap β (q j))
```

To summarise, the functor $\operatorname{cod} : d \swarrow F \to \cC$
[[lifts limits]].

<!--
```agda
module
  _ {o ℓ o' ℓ'} {C : Precategory o ℓ} {D : Precategory o' ℓ'} {d}
    (F : Functor C D) {lo lℓ} (F-cont : is-continuous lo lℓ F)
    {J : Precategory lo lℓ}
    where
  private
    module C = Cat C
```
-->

```agda
  Cod-lifts-limits : lifts-limits-of J (Cod (!Const d) F)
  Cod-lifts-limits lim .lifted = Cod-lift-limit F F-cont lim
  Cod-lifts-limits lim .preserved = trivial-is-limit! (Ran.has-ran lim)
```

As an easy corollary, we get: if $\cC$ is small-complete and $F$
small-continuous, then $d \swarrow F$ is small-complete as well.

<!--
```agda
module
  _ {o ℓ o' ℓ'} {C : Precategory o ℓ} {D : Precategory o' ℓ'}
    (F : Functor C D) (c-compl : is-complete ℓ ℓ C) (F-cont : is-continuous ℓ ℓ F)
    where
  private
    module C = Cat C
    module D = Cat D
    module F = Fr F
```
-->

```agda
  comma-is-complete : ∀ {d} → is-complete ℓ ℓ (d ↙ F)
  comma-is-complete = lifts-limits→complete (Cod _ F)
    (Cod-lifts-limits F F-cont) c-compl
```
