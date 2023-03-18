```agda
open import Cat.Instances.Functor.Compose
open import Cat.Instances.Shape.Terminal
open import Cat.Diagram.Colimit.Base
open import Cat.Diagram.Limit.Base
open import Cat.Instances.Functor
open import Cat.Instances.Functor.Compose
open import Cat.Functor.Coherence
open import Cat.Functor.Hom
open import Cat.Functor.Hom.Representable
open import Cat.Functor.Kan.Base
open import Cat.Functor.Kan.Unique
open import Cat.Instances.Comma
open import Cat.Functor.Base
open import Cat.Prelude

import Cat.Functor.Reasoning as Func
import Cat.Reasoning

module Cat.Functor.Kan.Pointwise where
```

# Pointwise Kan Extensions

One useful perspective on [Kan extensions] is that they are
generalizations of (co)limits; in fact, we have defined (co)limits as a
special case of Kan extensions! This means that many theorems involving
(co)limits can be directly generalized to theorems of Kan extensions.
A concrete example of this phenomena is the fact that right adjoints don't
just preserve limits, they preserve *all* right extensions!

[Kan extensions]: Cat.Functor.Kan.Base.html

However, this pattern of generalization fails in one critical way:
[corepresentable functors preserve limits], but corepresentable functors
do **not** preserve kan extensions! This seemingly slight issue has
far-reaching consequences, to the point that some authors write off
general Kan extensions entirely. However, we can restrict our attention
to the class of Kan extensions that **are** preserved by (co)representables;
we call such extensions pointwise.

[corepresentable functors preserve limits]: Cat.Functor.Hom.Representable.html#corepresentable-functors-preserve-limits

<!--
```agda
module _
  {o o′ o″ ℓ ℓ′ ℓ″}
  {C : Precategory o ℓ} {C' : Precategory o′ ℓ′} {D : Precategory o″ ℓ″}
  {F : Functor C C'} {G : Functor C D} {E : Functor C' D}
  where

  private
    module C = Cat.Reasoning C
    module C' = Cat.Reasoning C'
    module D = Cat.Reasoning D
    module [C,D] = Cat.Reasoning (Cat[ C , D ])
    module [C',D] = Cat.Reasoning (Cat[ C' , D ])
    open Func
    open is-lan
    open _=>_
```
-->


```agda
  is-pointwise-lan : ∀ {eta : G => E F∘ F} → is-lan F G E eta → Type _
  is-pointwise-lan lan =
    ∀ (x : D.Ob) → preserves-lan (Functor.op (Hom-into D x)) lan

  is-pointwise-ran : ∀ {eps : E F∘ F => G} → is-ran F G E eps → Type _
  is-pointwise-ran ran =
    ∀ (x : D.Ob) → preserves-ran (Hom-from D x) ran
```

<!--
```agda
module _
  {o o′ ℓ ℓ′}
  {J : Precategory o′ ℓ′} {C : Precategory o ℓ}
  {Dia : Functor J C} {x : Precategory.Ob C} 
  where

  private
    module C = Cat.Reasoning C
    open Func
    open is-lan
    open _=>_
```
-->

As noted earlier, limits and colimits are pointwise Kan extensions.

```agda
  limit→pointwise
    : {eps : Const x => Dia}
    → (lim : is-limit Dia x eps)
    → is-pointwise-ran lim
  limit→pointwise lim x = Hom-from-preserves-limits x lim

  colimit→pointwise
    : {eta : Dia => Const x}
    → (colim : is-colimit Dia x eta)
    → is-pointwise-lan colim
  colimit→pointwise colim x = よ-reverses-colimits x colim
```

## Computing Pointwise Extensions

One useful fact about pointwise left/right Kan extensions is that they
can be computed via colimits/limits, though we shall focus our attention
on the case of left extensions for the momemnt.

Suppose we have functors $F : \cC \to \cC'$ and $G : \cC \to \cD$, and
we wish to extend $G$ along $F$. If $\cD$ has all
$\kappa$-small colimits, then such an extension exists, and it is
pointwise.

<!--
```agda
module _
  {o o′ ℓ ℓ′}
  {C : Precategory ℓ ℓ} {C' : Precategory o ℓ} {D : Precategory o′ ℓ′}
  (F : Functor C C') (G : Functor C D)
  where

  private
    module C = Cat.Reasoning C
    module C' = Cat.Reasoning C'
    module D = Cat.Reasoning D
    open Func
    open ↓Obj
    open ↓Hom
    open _=>_
    open is-lan
```
-->

The big idea of our construction is to
approximate $G$ by gluing together "all of the ways that $C$ is able to
see $C'$ through $G$"". Concretely, this means looking at the
[comma category] $F \searrow c'$ for a given $c' : \cC'$. The objects of
this category are pairs of an object $c$ in $C$ and a map
$\cC'(F(c), c')$ in $\cC'$. If apply the projection
$\mathit{Dom} : F \searrow c' \to \cC$, we obtain a diagram in $\cC$,
which encodes the hand-wavy intuition from before.

[comma category]: Cat.Instances.Comma.html

To finish the construction, we shall take our diagram in $\cC$, and
post-compose with $G$ to obtain a diagram in $\cD$. Crucially, this
diagram is $\kappa$-small, so we can take a colimit of it in $\cD$.

```agda
    ↓Dia : (c' : C'.Ob) → Functor (F ↘ c') D
    ↓Dia c' = G F∘ Dom F (Const c')
```

In fact, we don't even require that $\cD$ is cocomplete, just that it has
colimits of these comma-shaped diagrams.

```agda
  comma-colimits→lan
    : (∀ (c' : C'.Ob) → Colimit (↓Dia c'))
    → Lan F G
  comma-colimits→lan ↓colim = lan module comma-colimits→lan where
      module ↓colim c' = Colimit (↓colim c')
```

These colimits give us canonical choices of objects in $\cD$ for each
$c' : \cC$. Furthermore, we can readily construct maps between them,
allowing us to show that the assignment of objects to colimits is
functorial.

```agda
      F′ : Functor C' D
      F′ .F₀ c' = ↓colim.coapex c'
      F′ .F₁ f =
        ↓colim.universal _
          (λ j → ↓colim.ψ _ (↓obj (f C'.∘ j .map)))
          (λ f →
            ↓colim.commutes _ (↓hom {β = f .β} (C'.pullr (f .sq)
            ·· C'.elim-inner refl
            ·· sym (C'.idl _))))
      F′ .F-id =
        sym $ ↓colim.unique _ _ _ _ λ j →
          D.idl _
          ∙ ap (↓colim.ψ _) (↓Obj-path _ _ refl refl (sym (C'.idl _)))
      F′ .F-∘ f g =
        sym $ ↓colim.unique _ _ _ _ λ j →
          D.pullr (↓colim.factors _ _ _)
          ∙ ↓colim.factors _ _ _
          ∙ ap (↓colim.ψ _) (↓Obj-path _ _ refl refl (C'.assoc _ _ _))
```

Next, we need to show that the functor we constructed actually is a
left extension. The natural transformation $\eta : G \to F' \circ F$
can be readily constructed from colimit injections, as the objects of
$F'(F(x))$ are all colimits!

```agda
      eta : G => F′ F∘ F
      eta .η c = ↓colim.ψ (F .F₀ c) (↓obj C'.id)
      eta .is-natural x y f =
        ↓colim.commutes (F₀ F y) (↓hom (ap (C'.id C'.∘_) (sym (C'.idr _))))
        ∙ sym (↓colim.factors _ _ _)
```


The universal natural transformation $\sigma$ is constructed using
the universal property of the colimits; naturality is somewhat tedious
to prove, but follows from uniqueness of the universal map.

```agda
      has-lan : is-lan F G F′ eta
      has-lan .σ {M = M} α .η c' =
        ↓colim.universal c'
          (λ j → M .F₁ (j .map) D.∘ α .η (j .x))
          (λ f →
            D.pullr (α .is-natural _ _ _)
            ∙ pulll M ((f .sq) ∙ C'.idl _))
      has-lan .σ {M = M} α .is-natural x y f =
        ↓colim.unique₂ _ _
          (λ f →
            D.pullr (α .is-natural _ _ _)
            ∙ pulll M (C'.pullr (f .sq) ∙ C'.elim-inner refl))
          (λ j →
            D.pullr (↓colim.factors _ _ _)
            ∙ ↓colim.factors _ _ _)
          (λ j →
            D.pullr (↓colim.factors _ _ _)
            ∙ D.pulll (sym (M .F-∘ _ _)))

```


Finally, commutativity and uniqueness follow from the corresponding
properties of colimits.

```agda
      has-lan .σ-comm {M = M} = Nat-path λ c →
        ↓colim.factors _ _ _
        ∙ D.eliml (M .F-id)
      has-lan .σ-uniq {M = M} {α = α} {σ′ = σ′} p = Nat-path λ c' →
        sym $ ↓colim.unique _ _ _ _ λ j →
          σ′ .η c' D.∘ ↓colim.ψ c' j                                ≡⟨ ap (λ ϕ → σ′ .η c' D.∘ ↓colim.ψ c' ϕ) (↓Obj-path _ _ refl refl (sym (C'.idr _))) ⟩
          (σ′ .η c' D.∘ ↓colim.ψ c' (↓obj (j .map C'.∘ C'.id)))     ≡⟨ D.pushr (sym $ ↓colim.factors _ _ _) ⟩
          (σ′ .η c' D.∘ ↓colim.universal _ _ _) D.∘ ↓colim.ψ _ _    ≡⟨ D.pushl (σ′ .is-natural _ _ _) ⟩
          M .F₁ (j .map) D.∘ (σ′ .η _ D.∘ ↓colim.ψ _ (↓obj C'.id))  ≡˘⟨ (D.refl⟩∘⟨ (p ηₚ j .x)) ⟩
          M .F₁ (j .map) D.∘ α .η (j .x)                            ∎
```

All that remains is to bundle up the data!

```agda
      lan : Lan F G
      lan .Lan.Ext = F′
      lan .Lan.eta = eta
      lan .Lan.has-lan = has-lan
```

Obviously if $\cD$ is $\kappa$-cocomplete, then it has the required
colimits.

```agda
  cocomplete→lan
    : is-cocomplete ℓ ℓ D
    → Lan F G
  cocomplete→lan colimits =
    comma-colimits→lan (λ c' → colimits (↓Dia c'))
```


Next, we shall show that the left extension we just constructed is
pointwise. To do this, we shall show a more general fact: if
$H : D \to E$ preserves all $\kappa$-small colimits, then $H$ preserves
left kan extensions constructed from colimits.

<!--
```agda
module _
  {o o′ ℓ ℓ′}
  {C : Precategory ℓ ℓ} {C' : Precategory o ℓ} {D : Precategory o′ ℓ′}
  (F : Functor C C') (G : Functor C D)
  where

  private
    module C = Cat.Reasoning C
    module C' = Cat.Reasoning C'
    module D = Cat.Reasoning D
    open Func
    open ↓Obj
    open ↓Hom
    open _=>_
    open is-lan
```
-->

The mathematical content of the proof is quite straightforward:
$H$ preserves the colimits used to construct the extension, so we
can perform the exact same process in $\cE$ to obtain a left extension.
However, the mechanical content of this proof is less pleasant: we
end up being off by a bunch of natural isomorphisms.

```agda
  preserves-colimits→preserves-pointwise-lan
    : ∀ {o″ ℓ″} {E : Precategory o″ ℓ″}
    → (colimits : is-cocomplete ℓ ℓ D)
    → (H : Functor D E)
    → is-cocontinuous ℓ ℓ H
    → preserves-lan H (Lan.has-lan (cocomplete→lan F G colimits))
  preserves-colimits→preserves-pointwise-lan {E = E} colimits H cocont =
    natural-isos→is-lan idni idni HF′-cohere fixup $
    comma-colimits→lan.has-lan F (H F∘ G) H-↓colim

    where
      module E = Cat.Reasoning E
      open make-natural-iso
      open Func

      ↓colim : (c' : C'.Ob) → Colimit (G F∘ Dom F (Const c'))
      ↓colim c' = colimits (G F∘ Dom F (Const c'))

      module ↓colim c' = Colimit (↓colim c')

      H-↓colim : (c' : C'.Ob) → Colimit ((H F∘ G) F∘ Dom F (Const c'))
      H-↓colim c' =
        natural-iso→colimit ni-assoc $
        preserves-colimit.colimit cocont (↓colim c')

      module H-↓colim c' = Colimit (H-↓colim c')
```

<details>
<summary>Whe shall omit the tedious coherence details.
</summary>

```agda
      F′ : Functor C' D
      F′ = comma-colimits→lan.F′ F G λ c' → colimits (G F∘ Dom F (Const c'))

      HF′ : Functor C' E
      HF′ = comma-colimits→lan.F′ F (H F∘ G) H-↓colim

      HF′-cohere : natural-iso HF′ (H F∘ F′)
      HF′-cohere = to-natural-iso mi where
        mi : make-natural-iso HF′ (H F∘ F′)
        mi .eta c' = E.id
        mi .inv c' = E.id
        mi .eta∘inv _ = E.idl _
        mi .inv∘eta _ = E.idl _
        mi .natural _ _ _ =
          E.idr _
          ∙ H-↓colim.unique _ _ _ _ (λ j → pulll H (↓colim.factors _ _ _))
          ∙ sym (E.idl _)

      module HF′-cohere = natural-iso HF′-cohere

      abstract
        fixup : (HF′-cohere.to ◆ idnt) ∘nt comma-colimits→lan.eta F (H F∘ G) _ ∘nt idnt ≡ nat-assoc-to (H ▸ comma-colimits→lan.eta F G _)
        fixup = Nat-path λ j →
          (H .F₁ (↓colim.universal _ _ _)  E.∘ E.id) E.∘ (H-↓colim.ψ _ _ E.∘ E.id) ≡⟨ ap₂ E._∘_ (E.idr _) (E.idr _) ⟩
          H .F₁ (↓colim.universal _ _ _) E.∘ H-↓colim.ψ _ _                        ≡⟨ pulll H (↓colim.factors _ _ _) ⟩
          H .F₁ (↓colim.ψ _ _) E.∘ E.id                                            ≡⟨ E.idr _ ⟩
          H .F₁ (↓colim.ψ _ (↓obj ⌜ C'.id C'.∘ C'.id ⌝))                           ≡⟨ ap! (C'.idl _) ⟩
          H .F₁ (↓colim.ψ _ (↓obj (C'.id)))                                        ∎
```
</details>

Hom functors take colimits in $\dD$ to colimits in $\set^op$, so by
the previous lemma, they must preserve the left extension. In other
words, the extension we constructed is pointwise.

```agda
  cocomplete→pointwise-lan
    : (colim : is-cocomplete ℓ ℓ D)
    → is-pointwise-lan (Lan.has-lan (cocomplete→lan F G colim))
  cocomplete→pointwise-lan colim d =
    preserves-colimits→preserves-pointwise-lan
      colim (Functor.op (Hom-into D d))
      (よ-reverses-colimits d)
```
