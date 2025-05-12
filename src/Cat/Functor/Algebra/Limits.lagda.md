---
description: |
  Limits in categories of F-algebras.
---
<!--
```agda
open import Cat.Functor.Kan.Reflection
open import Cat.Functor.Conservative
open import Cat.Diagram.Limit.Base
open import Cat.Functor.Kan.Unique
open import Cat.Functor.Naturality
open import Cat.Functor.Kan.Base
open import Cat.Displayed.Total
open import Cat.Functor.Algebra
open import Cat.Prelude

import Cat.Functor.Reasoning
import Cat.Reasoning

open lifts-limit
```
-->
```agda
module Cat.Functor.Algebra.Limits where
```

# Limits in categories of F-algebras {defines="limits-of-f-algebras"}

This short note details the construction of [[limits]] in categories of
[[F-algebras]] from limits in the underlying category; it is similar
to the construction of [[limits in categories of algebras]] for a
[[monad]].

<!-- [TODO: Reed M, 17/10/2024]
This should really be about creation of limits/display, but I don't want to deal
with that at the moment!
-->

<!--
```agda
module _
  {o ℓ oj ℓj} {C : Precategory o ℓ}
  (F : Functor C C)
  {J : Precategory oj ℓj} (K : Functor J (FAlg F))
  where
  open Cat.Reasoning C
  private
    module J = Cat.Reasoning J
    module F = Cat.Functor.Reasoning F
    module K = Cat.Functor.Reasoning K
  open Total-hom
```
-->

Let $F : \cC \to \cC$ be an endofunctor, and $K : \cJ \to \FAlg{F}$ be a
diagram of $F$-algebras. If $\cC$ has a limit $L$ of $\pi \circ K$, then
$L$ can be equipped with an $F$-algebra structure that makes it the limit
of $K$ in $\FAlg{F}$.

```agda
  Forget-algebra-lifts-limit : Limit (πᶠ (F-Algebras F) F∘ K) → Limit K
  Forget-algebra-lifts-limit L = to-limit (to-is-limit L') where
    module L = Limit L
    open make-is-limit
```

As noted earlier, the underlying object of the limit is $L$. The algebra
$F(L) \to L$ is constructed via the universal property of $L$: to
give a map $F(L) \to L$, it suffices to give maps $F(L) \to K(j)$ for
every $j : \cJ$, which we can construct by composing the projection
$F(\psi_{j}) : F(L) \to F(K(j))$ with the algebra $F(K(j)) \to K(j)$.

```agda
    apex : FAlg.Ob F
    apex .fst = L.apex
    apex .snd = L.universal (λ j → K.₀ j .snd ∘ F.₁ (L.ψ j)) comm where abstract
      comm
        : ∀ {i j : J.Ob} (f : J.Hom i j)
        → K.₁ f .hom ∘ K.₀ i .snd ∘ F.₁ (L.ψ i) ≡ K.₀ j .snd ∘ F.₁ (L.ψ j)
      comm {i} {j} f =
        K.₁ f .hom ∘ K.₀ i .snd ∘ F.₁ (L.ψ i)         ≡⟨ pulll (K.₁ f .preserves) ⟩
        (K.₀ j .snd ∘ F.₁ (K.₁ f .hom)) ∘ F.₁ (L.ψ i) ≡⟨ F.pullr (L.commutes f) ⟩
        K.₀ j .snd ∘ F.₁ (L.ψ j)                      ∎
```

A short series of calculations shows that the projections and universal map
associated to $L$ are $F$-algebra homomorphisms.

```agda
    L' : make-is-limit K apex
    L' .ψ j .hom = L.ψ j
    L' .ψ j .preserves = L.factors _ _
    L' .universal eps p .hom =
      L.universal (λ j → eps j .hom) (λ f → ap hom (p f))
    L' .universal eps p .preserves =
      L.unique₂ (λ j → K.F₀ j .snd ∘ F.₁ (eps j .hom))
        (λ f → pulll (K.₁ f .preserves) ∙ F.pullr (ap hom (p f)))
        (λ j → pulll (L.factors _ _) ∙ eps j .preserves)
        (λ j → pulll (L.factors _ _) ∙ F.pullr (L.factors _ _))
```

Finally, equality of morphisms of $F$-algebras is given by equality on
the underlying morphisms, so all of the relevant diagrams in $\FAlg{F}$
commute.

```agda
    L' .commutes f =
      total-hom-path (F-Algebras F) (L.commutes f) prop!
    L' .factors eps p =
      total-hom-path (F-Algebras F) (L.factors _ _) prop!
    L' .unique eps p other q =
      total-hom-path (F-Algebras F) (L.unique _ _ _ λ j → ap hom (q j)) prop!
```

<!--
```agda
module _
  {o ℓ oj ℓj} {C : Precategory o ℓ}
  (F : Functor C C)
  {J : Precategory oj ℓj}
  where
```
-->

Packaging this together, we have that the forgetful functor from the
category of $F$-algebras to $C$ [[creates limits]].

```agda
  Forget-algebra-lifts-limits : lifts-limits-of J (πᶠ (F-Algebras F))
  Forget-algebra-lifts-limits lim .lifted = Forget-algebra-lifts-limit F _ lim
  Forget-algebra-lifts-limits lim .preserved = trivial-is-limit! (Ran.has-ran lim)

  Forget-algebra-creates-limits : creates-limits-of J (πᶠ (F-Algebras F))
  Forget-algebra-creates-limits = conservative→lifts→creates-limits
    Forget-algebra-is-conservative Forget-algebra-lifts-limits
```

<!--
```agda
module _
  {o ℓ oκ ℓκ} {C : Precategory o ℓ}
  (complete : is-complete oκ ℓκ C)
  where
```
-->

This gives us the following useful corollary: if $\cC$ is $\kappa$-complete,
then $\FAlg{F}$ is also $\kappa$ complete.

```agda
  FAlg-is-complete : (F : Functor C C) → is-complete oκ ℓκ (FAlg F)
  FAlg-is-complete F = lifts-limits→complete (πᶠ (F-Algebras F))
    (Forget-algebra-lifts-limits F) complete
```
