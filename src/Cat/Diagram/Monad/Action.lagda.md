<!--
```agda
open import Cat.Instances.Shape.Terminal
open import Cat.Functor.Coherence
open import Cat.Displayed.Total
open import Cat.Diagram.Monad
open import Cat.Functor.Base
open import Cat.Prelude

open Algebra-on
open Total-hom
open Functor
open _=>_
```
-->

```agda
module Cat.Diagram.Monad.Action where
```

# Monad actions {defines="monad-action module-over-a-monad"}

<!--
```agda
module _
    {o ℓ}
    {C : Precategory o ℓ} {M : Functor C C} (Mᵐ : Monad-on M)
    where

  private
    module M = Monad-on Mᵐ
```
-->

Let $M$ be a [[monad]] on a category $\cC$, and $A : \cB \to \cC$ a
[[functor]]. A **left $M$-action** on $A$, also called a **left
$M$-module** or an $M$-algebra (although that term conflicts with [[algebras
over a monad]]), is a natural transformation $\alpha : M \circ A \To A$
obeying laws similar to the ones for [[monad algebras]].

```agda
  record Action-on {o' ℓ'} {B : Precategory o' ℓ'} (A : Functor B C)
    : Type (ℓ ⊔ o' ⊔ ℓ') where
    no-eta-equality
    field
      α : M F∘ A => A
      α-unit : α ∘nt nat-idl-from (M.unit ◂ A) ≡ idnt
      α-mult : α ∘nt nat-unassoc-from (M.mult ◂ A) ≡ α ∘nt (M ▸ α)
```

To tie things together, we observe that $M$-actions on functors out of
the [[terminal category]] are equivalent to $M$-algebras
[[over|equivalence over]] the equivalence between functors $\top \to \cC$
and objects of $\cC$.

<!--
```agda
module _
    {o ℓ}
    {C : Precategory o ℓ} {M : Functor C C} {Mᵐ : Monad-on M}
    where

  open Action-on

  private
    unquoteDecl eqv = declare-record-iso eqv (quote Action-on)

  Action-on-pathp
    : ∀ {o' ℓ'} {B : Precategory o' ℓ'} {X Y : Functor B C} (p : X ≡ Y) {A : Action-on Mᵐ X} {B : Action-on Mᵐ Y}
    → PathP (λ i → M F∘ p i => p i) (A .α) (B .α)
    → PathP (λ i → Action-on Mᵐ (p i)) A B
  Action-on-pathp over mults = injectiveP (λ _ → eqv) (mults ,ₚ prop!)

  instance
    Extensional-Action-on
      : ∀ {o' ℓ' ℓr} {B : Precategory o' ℓ'}
      → (let open Precategory C)
      → ∀ {A : Functor B C}
      → ⦃ sa : Extensional (M F∘ A => A) ℓr ⦄
      → Extensional (Action-on Mᵐ A) ℓr
    Extensional-Action-on ⦃ sa ⦄ =
      injection→extensional! (Action-on-pathp refl) sa
```
-->

```agda
  Algebra≃⊤Action : Algebra-on Mᵐ ≃[ !Const , !Const-is-equiv ] Action-on Mᵐ
  Algebra≃⊤Action = over-left→over (_ , !Const-is-equiv) λ where
    c .fst alg → λ where
      .α → !constⁿ (alg .ν)
      .α-unit → ext λ _ → alg .ν-unit
      .α-mult → ext λ _ → alg .ν-mult
    c .snd → is-iso→is-equiv λ where
      .is-iso.from act → λ where
        .ν → act .α .η tt
        .ν-unit → act .α-unit ηₚ tt
        .ν-mult → act .α-mult ηₚ tt
      .is-iso.rinv act → ext λ _ → refl
      .is-iso.linv alg → ext refl
```

## The universal left monad action {defines="universal-left-monad-action universal-left-module"}

Monad actions give us a new perspective on [[Eilenberg-Moore categories]]:
given a [[monad $M$ in|monad in]] an arbitrary [[bicategory]], the
**Eilenberg-Moore object** of $M$ is the *universal* left $M$-action,
in a sense to be explained. Then, Eilenberg-Moore categories are nothing
more than the instantiation of this concept to the [[bicategory of
categories]].

What this means is that, first, there is a left $M$-action on the forgetful
functor $U : \cC^M \to \cC$, which is simply given componentwise by
the algebra maps.

<!--
```agda
module _ {o ℓ} {C : Precategory o ℓ} {M : Functor C C} (Mᵐ : Monad-on M) where
  open Action-on
```
-->

```agda
  Forget-EM-action : Action-on Mᵐ (Forget-EM {M = Mᵐ})
  Forget-EM-action .α .η (_ , alg) = alg .ν
  Forget-EM-action .α .is-natural _ _ f = sym (f .preserves)
  Forget-EM-action .α-unit = ext λ (_ , alg) → alg .ν-unit
  Forget-EM-action .α-mult = ext λ (_ , alg) → alg .ν-mult
```

And, second, that this left $M$-action is universal in the sense that
functors $\cB \to \cC^M$ correspond precisely to left $M$-actions on
functors $\cB \to \cC$.

<!--
```agda
  module _ {o' ℓ'} {B : Precategory o' ℓ'} where
```
-->

```agda
    EM-universal
      : {A : Functor B C} (act : Action-on Mᵐ A)
      → Functor B (Eilenberg-Moore Mᵐ)
    EM-universal {A = A} act .F₀ b .fst = A .F₀ b
    EM-universal {A = A} act .F₀ b .snd .ν = act .α .η b
    EM-universal {A = A} act .F₀ b .snd .ν-unit = act .α-unit ηₚ b
    EM-universal {A = A} act .F₀ b .snd .ν-mult = act .α-mult ηₚ b
    EM-universal {A = A} act .F₁ f .hom = A .F₁ f
    EM-universal {A = A} act .F₁ f .preserves = sym (act .α .is-natural _ _ f)
    EM-universal {A = A} act .F-id = ext (A .F-id)
    EM-universal {A = A} act .F-∘ f g = ext (A .F-∘ f g)

    EM→Action
      : (A^M : Functor B (Eilenberg-Moore Mᵐ))
      → Action-on Mᵐ (Forget-EM F∘ A^M)
    EM→Action A^M .α .η b = A^M .F₀ b .snd .ν
    EM→Action A^M .α .is-natural _ _ f = sym (A^M .F₁ f .preserves)
    EM→Action A^M .α-unit = ext λ b → A^M .F₀ b .snd .ν-unit
    EM→Action A^M .α-mult = ext λ b → A^M .F₀ b .snd .ν-mult
```

Note that the universal action itself is induced by the identity
functor on $\cC^M$.

The above correspondence is really an isomorphism of *categories*, so
we also have a further characterisation of *2-cells* (in our case,
natural transformations) between functors $X, Y : \cB \to \cC^M$;
namely, these are in bijection with *morphisms of actions* between the
induced actions on $U \circ X$ and $U \circ Y$: natural transformations
$\beta : U \circ X \To U \circ Y$ that make the following diagram
commute, where $\nu$ is the universal $M$-action.

~~~{.quiver}
\[\begin{tikzcd}
  MUX & MUY \\
  UX & UY
  \arrow["{M\beta}", Rightarrow, from=1-1, to=1-2]
  \arrow["{\nu X}"', Rightarrow, from=1-1, to=2-1]
  \arrow["{\nu Y}", Rightarrow, from=1-2, to=2-2]
  \arrow["\beta"', Rightarrow, from=2-1, to=2-2]
\end{tikzcd}\]
~~~

```agda
    EM-2-cell
      : {X Y : Functor B (Eilenberg-Moore Mᵐ)}
      → (β : Forget-EM F∘ X => Forget-EM F∘ Y)
      → β ∘nt EM→Action X .α ≡ EM→Action Y .α ∘nt (M ▸ β)
      → X => Y
    EM-2-cell β comm .η b .hom = β .η b
    EM-2-cell β comm .η b .preserves = comm ηₚ b
    EM-2-cell β comm .is-natural _ _ f = ext (β .is-natural _ _ f)
```

We also provide a useful variant for the heterogeneous case with a
functor into $\cC^M$ on the left and an $M$-action on the right.

```agda
    EM-2-cell'
      : {X : Functor B (Eilenberg-Moore Mᵐ)}
      → {A : Functor B C} {act : Action-on Mᵐ A}
      → (β : Forget-EM F∘ X => A)
      → β ∘nt EM→Action X .α ≡ act .α ∘nt (M ▸ β)
      → X => EM-universal act
    EM-2-cell' β comm = EM-2-cell (cohere! β) (reext! comm)
```
