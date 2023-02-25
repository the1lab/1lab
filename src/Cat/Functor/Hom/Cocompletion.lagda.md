```agda
open import Cat.Functor.Adjoint.Continuous
open import Cat.Diagram.Colimit.Base
open import Cat.Functor.Hom.Coyoneda
open import Cat.Instances.Elements
open import Cat.Instances.Functor
open import Cat.Functor.Kan.Base
open import Cat.Functor.Hom
open import Cat.Prelude

import Cat.Functor.Reasoning as Func
import Cat.Reasoning

module
  Cat.Functor.Hom.Cocompletion
    {κ o} (C : Precategory κ κ) (D : Precategory o κ)
    (colim : is-cocomplete κ κ D)
    where
```

<!--
```agda
private
  module C = Cat.Reasoning C
  module D = Cat.Reasoning D
open import Cat.Morphism Cat[ C , D ] using (_≅_)

open Func
open _=>_
open Element
open Element-hom
```
-->

# Free cocompletions

Let $\cC$ be a [$\kappa$-small] precategory. It, broadly speaking,
will not be cocomplete. Suppose that we're interested in passing from
$\cC$ to a cocomplete category; How might we go about this in a
universal way?

To substantiate this problem, it helps to picture a _geometric_ case.
We'll take $\cC = \Delta$, the category of non-empty finite ordinals
and monotonic functions. The objects and maps in this category satisfy
equations which let us, broadly speaking, think of its objects as
"abstract (higher-dimensional) triangles", or _simplices_. For instance,
there are (families) of maps $[n]\to[n+1]$, exhibiting an
$n$-dimensional simplex as a face in an $(n+1)$-dimensional simplex.

[$\kappa$-small]: 1Lab.intro.html#universes-and-size-issues

Now, this category does _not_ have all colimits. For example, we should
be able to the red and blue triangles in the diagram below to obtain a
"square", but you'll find no such object in $\Delta$.

~~~{.quiver}
\[\begin{tikzcd}
  \bullet && \bullet \\
  \\
  \bullet && \bullet
  \arrow[color={rgb,255:red,92;green,92;blue,214}, from=1-1, to=3-3]
  \arrow[color={rgb,255:red,92;green,92;blue,214}, from=3-1, to=1-1]
  \arrow[color={rgb,255:red,92;green,92;blue,214}, from=3-1, to=3-3]
  \arrow[color={rgb,255:red,214;green,92;blue,92}, from=1-1, to=1-3]
  \arrow[color={rgb,255:red,214;green,92;blue,92}, from=1-3, to=3-3]
  \arrow[shift left=1, color={rgb,255:red,214;green,92;blue,92}, from=1-1, to=3-3]
\end{tikzcd}\]
~~~

Universally embedding $\Delta$ in a cocomplete category should then
result in a "category of shapes built by gluing simplices"; Formally,
these are called _simplicial sets_. It turns out that the [Yoneda
embedding] satisfies the property we're looking for: Any functor $F :
\cC \to \cD$ into a cocomplete category $\cD$ factors as

$$
\cC \xto{\yo} \psh(\cC) \xto{\Lan_\yo F} \cD\text{,}
$$

where $\Lan_\yo F$ is the [left Kan extension] of $F$ along the Yoneda
embedding, and furthermore this extension preserves colimits. While this
may sound like a _lot_ to prove, it turns out that the tide has already
risen above it: Everything claimed above follows from the general theory
of Kan extensions.

[Yoneda embedding]: Cat.Functor.Hom.html#the-yoneda-embedding
[left Kan extension]: Cat.Functor.Kan.Base.html

```agda
よ-extension : (F : Functor C D) → Lan (よ C) F
よ-extension F = lan where

  module colim (P : Functor (C ^op) (Sets κ)) =
    Colimit (colim (F F∘ πₚ C P))
  module coyoneda (P : Functor (C ^op) (Sets κ)) =
    is-colimit (coyoneda C P)

  open Lan
  open is-lan

  extend : Functor (PSh κ C) D
  extend .F₀ = colim.coapex
  extend .F₁ {P} {Q} f =
    colim.universal _
      (λ j → colim.ψ Q (elem (j .ob) (f .η _ (j .section))))
      (λ g → colim.commutes Q
        (elem-hom (g .hom)
            (sym (f .is-natural _ _ _) $ₚ _
             ∙ ap (f .η _) (g .commute))))
  extend .F-id =
    sym $ colim.unique _ _ _ _ λ j →
      D.idl _
  extend .F-∘ f g =
    sym $ colim.unique _ _ _ _ λ j →
      D.pullr (colim.factors _ _ _)
      ∙ colim.factors _ _ _

  lan : Lan (よ C) F
  lan .Ext = extend
  lan .eta .η x = colim.ψ _ (elem x C.id)
  lan .eta .is-natural x y f =
    colim.commutes _ (elem-hom f C.id-comm-sym)
    ∙ sym (colim.factors _ _ _)
  lan .has-lan .σ {M = M} α .η P =
    colim.universal P
      (λ j → M .F₁ (coyoneda.ψ P j) D.∘ α .η (j .ob))
      λ f →
        D.pullr (α .is-natural _ _ _)
        ∙ pulll M (coyoneda.commutes P f)
  lan .has-lan .σ {M = M} α .is-natural P Q f =
    colim.unique₂ P _
      (λ g →
        D.pullr (α .is-natural _ _ _)
        ∙ pulll M (coyoneda.commutes _ (elem-hom (g .hom) (sym (f .is-natural _ _ _ $ₚ _) ∙ ap (f .η _) (g .commute)))))
      (λ j →
        D.pullr (colim.factors P _ _)
        ∙ colim.factors Q _ _)
      (λ j →
        D.pullr (colim.factors P _ _)
        ∙ pulll M (Nat-path (λ _ → funext λ x → f .is-natural _ _ _ $ₚ j .section)))
  lan .has-lan .σ-comm {M = M} = Nat-path λ _ →
    colim.factors _ _ _
    ∙ eliml M (Nat-path (λ _ → funext λ _ → C.idl _))
  lan .has-lan .σ-uniq {M = M} {α = α} {σ′ = σ′} p = Nat-path λ P →
    sym $ colim.unique _ _ _ _ λ j →
      σ′ .η _ D.∘ colim.ψ P j                                     ≡⟨ D.pushr (sym (colim.factors _ _ _ ∙ ap (colim.ψ _) (ap₂ elem refl (P .F-id $ₚ _)))) ⟩
      (σ′ .η _ D.∘ colim.universal _ _ _) D.∘ colim.ψ (よ₀ C _) _ ≡⟨ D.pushl (σ′ .is-natural _ _ _) ⟩
      M .F₁ (coyoneda.ψ P j) D.∘ σ′ .η _ D.∘ colim.ψ (よ₀ C _) _  ≡˘⟨ (D.refl⟩∘⟨ (p ηₚ _)) ⟩
      M .F₁ (coyoneda.ψ P j) D.∘ α .η _                           ∎
```
