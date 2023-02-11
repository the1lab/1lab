```agda
open import Cat.Functor.Equivalence.Complete
open import Cat.Functor.Conservative
open import Cat.Functor.Equivalence
open import Cat.Functor.Kan.Base
open import Cat.Diagram.Limit.Base
open import Cat.Instances.Shape.Terminal
open import Cat.Diagram.Terminal
open import Cat.Diagram.Monad
open import Cat.Prelude

import Cat.Reasoning

module Cat.Diagram.Monad.Limits {o ℓ} {C : Precategory o ℓ} {M : Monad C} where
```

<!--
```agda
private
  module EM = Cat.Reasoning (Eilenberg-Moore C M)
  module C = Cat.Reasoning C
  module M = Monad M

open Algebra-hom
open Algebra-on
```
-->

# Limits in categories of algebras

Suppose that $\cC$ be a category, $M$ be a [monad] on $\cC$, and
$F$ be a $\cJ$-shaped diagram of [$M$-algebras][malg] (that is, a
functor $F : \cJ \to \cC^M$ into the [Eilenberg-Moore category] of
M). Suppose that an evil wizard has given you a [limit] for the diagram
in $\cC$ which underlies $F$, but they have not (being evil and all)
told you whether $\lim F$ admits an algebra structure at all.

[monad]: Cat.Diagram.Monad.html#monads
[malg]: Cat.Diagram.Monad.html#algebras-over-a-monad
[Eilenberg-Moore category]: Cat.Diagram.Monad.html#eilenberg-moore-category
[limit]: Cat.Diagram.Limit.Base.html

Perhaps we can make this situation slightly more concrete, by working in
a category _equivalent to_ an Eilenberg-Moore category: If we have two
groups $G$, $H$, considered as a discrete diagram, then the limit our
evil wizard would give us is the product $U(G) \times U(H)$ in $\Sets$.
But we [already know] we can equip this product with a "pointwise" group
structure! Does this result generalise?

[already know]: Algebra.Group.Cat.FinitelyComplete.html#direct-products

The answer is positive, though this is one of those cases where abstract
nonsense can not help us: gotta roll up our sleeves and calculate away.
Suppose we have a diagram as in the setup --- we'll show that the
functor $U : \cC^M \to \cC$ both preserves and _reflects_ limits,
in that $K$ is a limiting cone if, and only if, $U(K)$ is.

```agda
module _ {jo jℓ} {J : Precategory jo jℓ} (F : Functor J (Eilenberg-Moore C M)) where
  private
    module F = Functor F
    module FAlg j = Algebra-on (F.₀ j .snd)
```

We begin by showing the following key lemma: if the limit in the base has
an algebra structure, and the projections of the limit form monad algebra
morphisms, then we have a limit in the category of monad algebras.

```agda
  make-algebra-limit
    : ∀ {K : Functor ⊤Cat C} {eps : K F∘ !F => Forget C M F∘ F}
    → (lim : is-ran !F (Forget C M F∘ F) K eps)
    → (apex-alg : Algebra-on C M (Functor.F₀ K tt))
    → (∀ j → is-limit.ψ lim j C.∘ apex-alg .ν ≡ FAlg.ν j C.∘ M.M₁ (is-limit.ψ lim j))
    → make-is-limit F ((Functor.F₀ K tt) , apex-alg)
  make-algebra-limit lim apex-alg comm = em-lim where
      module lim = is-limit lim
      open make-is-limit
      module apex = Algebra-on apex-alg
      open _=>_

      em-lim : make-is-limit F _
      em-lim .ψ j .morphism =
        lim.ψ j
      em-lim .ψ j .commutes =
        comm j
      em-lim .commutes f =
        Algebra-hom-path C (lim.commutes f)
      em-lim .universal eta p .morphism =
        lim.universal (λ j → eta j .morphism) (λ f → ap morphism (p f))
      em-lim .universal eta p .commutes =
        lim.unique₂ _
          (λ f →
            C.pulll (F.F₁ f .commutes)
            ∙ C.pullr (sym (M.M-∘ _ _) ∙ ap M.M₁ (ap morphism (p f))))
          (λ j →
            C.pulll (lim.factors _ _)
            ∙ eta j .commutes)
          (λ j →
            C.pulll (comm j)
            ∙ C.pullr (sym (M.M-∘ _ _) ∙ ap M.M₁ (lim.factors _ _)))
      em-lim .factors eta p =
        Algebra-hom-path C (lim.factors _ _)
      em-lim .unique eta p other q =
        Algebra-hom-path C (lim.unique _ _ _ λ j → ap morphism (q j))
```

Reflection of limits follows directly, as we already had the structure
of an algebra upstairs!

```agda
  Forget-reflects-limits : reflects-limit (Forget C M) F
  Forget-reflects-limits {K} {eps} lim =
    to-is-limitp
      (make-algebra-limit lim (K.F₀ tt .snd) (λ j → eps .η j .commutes))
      (Algebra-hom-path C refl)
    where
      module K = Functor K
      open _=>_
```

I hope you like appealing to uniqueness of maps into limits, by the way.
We now relax the conditions on the theorem above, which relies on the
pre-existence of a cone $K$. In fact, what we have shown is that
`Forget` reflects the property of _being a limit_ --- what we now show
is that it reflects limit _objects_, too: if $U \circ F$ has a limit,
then so does $F$.

Using our lemma from before, it suffices to show that the apex of the
limit has the structure of an algebra.

```agda
  Forget-lift-limit : Limit (Forget C M F∘ F) → Limit F
  Forget-lift-limit lim-over =
    to-limit
    $ to-is-limit
    $ make-algebra-limit
        (Limit.has-limit lim-over)
        apex-algebra
        (λ j → lim-over.factors _ _)
    where
      module lim-over = Limit lim-over

      apex-algebra : Algebra-on C M lim-over.apex
      apex-algebra .ν =
        lim-over.universal
          (λ j → FAlg.ν j C.∘ M.M₁ (lim-over.ψ j))
          (λ f →
            C.pulll (F.F₁ f .commutes)
            ∙ C.pullr (sym (M.M-∘ _ _) ∙ ap M.M₁ (lim-over.commutes f)))
      apex-algebra .ν-unit =
        lim-over.unique₂ _ lim-over.commutes
          (λ j →
            C.pulll (lim-over.factors _ _)
            ·· C.pullr (sym $ M.unit.is-natural _ _ _)
            ·· C.cancell (FAlg.ν-unit j))
          (λ j → C.idr _)
      apex-algebra .ν-mult =
        lim-over.unique₂ _
          (λ f →
            C.pulll $
              C.pulll (F.₁ f .commutes)
              ∙ C.pullr (sym (M.M-∘ _ _) ∙ ap M.M₁ (lim-over.commutes f)))
          (λ j →
            C.pulll (lim-over.factors _ _)
            ·· C.pullr (sym (M.M-∘ _ _) ∙ ap M.M₁ (lim-over.factors _ _) ∙ M.M-∘ _ _)
            ·· C.extendl (FAlg.ν-mult j)
            ·· ap (FAlg.ν j C.∘_) (M.mult.is-natural _ _ _)
            ·· C.assoc _ _ _)
          (λ j → C.pulll (lim-over.factors _ _))
```

We conclude by saying that, if $\cC$ is a complete category, then so
is $\cC^M$, with no assumptions on $M$.

```agda
Eilenberg-Moore-is-complete
  : ∀ {a b} → is-complete a b C → is-complete a b (Eilenberg-Moore _ M)
Eilenberg-Moore-is-complete complete F = Forget-lift-limit F (complete _)
```
