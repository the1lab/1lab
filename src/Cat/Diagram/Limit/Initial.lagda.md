<!--
```agda
open import Cat.Diagram.Limit.Base
open import Cat.Diagram.Initial
open import Cat.Prelude

import Cat.Reasoning as Cat

open make-is-limit
open Initial
```
-->

```agda
module Cat.Diagram.Limit.Initial where
```

# Initial objects as limits {defines="initial-objects-are-limits"}

This module provides a characterisation of [[initial objects]] as
[[*limits*]], rather than as [[colimits]]. Namely, while an initial
object is the *co*limit of the empty diagram, it is the *limit* of the
identity functor, considered as a diagram.

Since the identity functor on $\cC$ has $\cC$ itself as a domain,
computing its limit by general means is usually infeasible. However,
*if* we have such a limit handy, then we know that $\cC$ has an initial
object. Conversely, if $\cC$ has an initial object, then, as a
triviality, we can say that it admits at least one "large" limit.

<!--
```agda
module _ {o ℓ} {C : Precategory o ℓ} (L : Limit (Id {C = C})) where
  open Cat C
  private
    module L = Limit L
```
-->

```agda
    rem₁ : L.ψ L.apex ≡ id
    rem₁ = L.unique₂ (λ j → L.ψ j) (λ f → L.commutes f) (λ j → L.commutes _) (λ j → idr _)

  Id-limit→Initial : Initial C
  Id-limit→Initial .bot = L.apex
  Id-limit→Initial .has⊥ x = λ where
    .centre → L.ψ x
    .paths h → sym (intror rem₁ ∙ L.commutes h)
```

<!--
```agda
module _ {o ℓ} {C : Precategory o ℓ} (L : Initial C) where
  open Cat C
  private
    module L = Initial L
```
-->

```agda
  Initial→Id-limit : Limit (Id {C = C})
  Initial→Id-limit = to-limit (to-is-limit mk) where
    mk : make-is-limit Id L.bot
    mk .ψ j = L.¡
    mk .commutes f = L.¡-unique₂ _ _
    mk .universal eps x = eps L.bot
    mk .factors eps p = p _
    mk .unique eps p other x = introl (L.¡-unique₂ _ _) ∙ x L.bot
```
