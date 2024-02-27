<!--
```agda
open import 1Lab.Reflection.Record

open import Cat.Monoidal.Instances.Cartesian
open import Cat.Functor.Naturality
open import Cat.Instances.Product
open import Cat.Monoidal.Braided
open import Cat.Monoidal.Reverse
open import Cat.Functor.Compose
open import Cat.Monoidal.Base
open import Cat.Functor.Base
open import Cat.Prelude

import Cat.Functor.Reasoning
import Cat.Reasoning

open _=>_
```
-->

```agda
module Cat.Monoidal.Strength where
```

# Strong functors {defines="strong-functor strength left-strength right-strength"}

<!--
```agda
module _
  {o ℓ} {C : Precategory o ℓ}
  (Cᵐ : Monoidal-category C)
  (F : Functor C C)
  where
  open Cat.Reasoning C
  open Monoidal-category Cᵐ
  open Functor F
  private module F = Cat.Functor.Reasoning F
```
-->

A **left strength** for a [[functor]] $F : \cC \to \cC$ on a [[monoidal
category]] $\cC$ is a [[natural transformation]]

$$
\sigma : A \otimes FB \to F (A \otimes B)
$$

interacting nicely with the left unitor and associator.

```agda
  record Left-strength : Type (o ⊔ ℓ) where
    field
      left-strength : -⊗- F∘ (Id F× F) => F F∘ -⊗-

    module σ = _=>_ left-strength

    σ : ∀ {A B} → Hom (A ⊗ F₀ B) (F₀ (A ⊗ B))
    σ = σ.η _

    field
      left-strength-λ← : ∀ {A} → F₁ (λ← {A}) ∘ σ ≡ λ←
      left-strength-α→ : ∀ {A B C}
        → F₁ (α→ A B C) ∘ σ ≡ σ ∘ (id ⊗₁ σ) ∘ α→ A B (F₀ C)
```

Reversely^[That is, on the other side of the [[reverse monoidal
category]] duality.], a **right strength** is a natural transformation

$$
\tau : FA \otimes B \to F (A \otimes B)
$$

interacting nicely with the *right* unitor and associator.

```agda
  record Right-strength : Type (o ⊔ ℓ) where
    field
      right-strength : -⊗- F∘ (F F× Id) => F F∘ -⊗-

    module τ = _=>_ right-strength

    τ : ∀ {A B} → Hom (F₀ A ⊗ B) (F₀ (A ⊗ B))
    τ = τ.η _

    field
      right-strength-ρ← : ∀ {A} → F₁ (ρ← {A}) ∘ τ ≡ ρ←
      right-strength-α← : ∀ {A B C}
        → F₁ (α← A B C) ∘ τ ≡ τ ∘ (τ ⊗₁ id) ∘ α← (F₀ A) B C
```

<!--
```agda
    right-strength-α→ : ∀ {A B C} → τ ∘ α→ (F₀ A) B C ≡ F₁ (α→ A B C) ∘ τ ∘ (τ ⊗₁ id)
    right-strength-α→ = sym $ swizzle
      (sym (right-strength-α← ∙ assoc _ _ _))
      (α≅ .invr)
      (F.F-map-iso α≅ .invl)
```
-->

A **strength** for $F$ is a pair of a left strength and a right strength
inducing a single operation $A \otimes FB \otimes C \to F (A \otimes
B \otimes C)$, i.e. making the following diagram commute:

~~~{.quiver}
\[\begin{tikzcd}
  {(A \otimes FB) \otimes C} & {A \otimes (FB \otimes C)} \\
  {F(A \otimes B) \otimes C} & {A \otimes F(B \otimes C)} \\
  {F((A \otimes B) \otimes C)} & {F(A \otimes (B \otimes C))}
  \arrow["\alpha", from=1-1, to=1-2]
  \arrow["{\sigma \otimes C}"', from=1-1, to=2-1]
  \arrow["\tau"', from=2-1, to=3-1]
  \arrow["F\alpha"', from=3-1, to=3-2]
  \arrow["{A \otimes \tau}", from=1-2, to=2-2]
  \arrow["\sigma", from=2-2, to=3-2]
\end{tikzcd}\]
~~~

```agda
  record Strength : Type (o ⊔ ℓ) where
    field
      strength-left : Left-strength
      strength-right : Right-strength

    open Left-strength strength-left public
    open Right-strength strength-right public

    field
      strength-α→ : ∀ {A B C}
        → F₁ (α→ A B C) ∘ τ ∘ (σ ⊗₁ id) ≡ σ ∘ (id ⊗₁ τ) ∘ α→ A (F₀ B) C
```

A functor equipped with a strength is called a **strong functor**.

<!--
```agda
  private unquoteDecl left-eqv = declare-record-iso left-eqv (quote Left-strength)
  Left-strength-path
    : ∀ {a b} → a .Left-strength.left-strength ≡ b .Left-strength.left-strength
    → a ≡ b
  Left-strength-path p = Iso.injective left-eqv (Σ-prop-path (λ _ → hlevel 1) p)

  private unquoteDecl right-eqv = declare-record-iso right-eqv (quote Right-strength)
  Right-strength-path
    : ∀ {a b} → a .Right-strength.right-strength ≡ b .Right-strength.right-strength
    → a ≡ b
  Right-strength-path p = Iso.injective right-eqv (Σ-prop-path (λ _ → hlevel 1) p)
```
-->

## Symmetry

<!--
```agda
  module _ (Cᵇ : Braided-monoidal Cᵐ) where
    open Braided Cᵐ Cᵇ
    open is-iso
```
-->

In a [[symmetric monoidal category]] (or even just a [[braided monoidal
category]], if one is careful about directions), there is an equivalence
between the notions of left and right strength: we can obtain one from
the other by "conjugating" with the braiding, as illustrated by this
diagram.

~~~{.quiver}
\[\begin{tikzcd}
  {A \otimes FB} & {FB \otimes A} \\
  {F (A \otimes B)} & {F (B \otimes A)}
  \arrow["\sigma"', from=1-1, to=2-1]
  \arrow["\tau", from=1-2, to=2-2]
  \arrow["\beta", "\sim"', from=1-1, to=1-2]
  \arrow["F\beta"', "\sim", from=2-1, to=2-2]
\end{tikzcd}\]
~~~

Therefore, the literature usually speaks of "strength" in a symmetric
monoidal category to mean either a left or a right strength, but note
that this is not quite the same as a `Strength`{.Agda} as defined above,
which has left and right strengths *not necessarily related* by the
braiding. If they are, we will say that the strength is *symmetric*;
such a strength contains exactly the information of a left (or right)
strength.

```agda
    is-symmetric-strength : Strength → Type (o ⊔ ℓ)
    is-symmetric-strength s = ∀ {A B} → τ {A} {B} ∘ β→ ≡ F₁ β→ ∘ σ
      where open Strength s
```

<details>
<summary>
The construction of the equivalence between left and right strengths
is extremely tedious, so we leave the details to the curious reader.

```agda
    left≃right : Iso Left-strength Right-strength
```

</summary>

```agda
    left≃right .fst l = r where
      open Left-strength l
      open Right-strength
      r : Right-strength
      r .right-strength .η _ = F₁ β→ ∘ σ ∘ β←
      r .right-strength .is-natural _ _ (f , g) =
        (F₁ β→ ∘ σ ∘ β←) ∘ (F₁ f ⊗₁ g) ≡⟨ pullr (pullr (β←.is-natural _ _ _)) ⟩
        F₁ β→ ∘ σ ∘ (g ⊗₁ F₁ f) ∘ β←   ≡⟨ refl⟩∘⟨ extendl (σ.is-natural _ _ _) ⟩
        F₁ β→ ∘ F₁ (g ⊗₁ f) ∘ σ ∘ β←   ≡⟨ F.extendl (β→.is-natural _ _ _) ⟩
        F₁ (f ⊗₁ g) ∘ F₁ β→ ∘ σ ∘ β←   ∎
      r .right-strength-ρ← =
        F₁ ρ← ∘ F₁ β→ ∘ σ ∘ β← ≡⟨ F.pulll ρ←-β→ ⟩
        F₁ λ← ∘ σ ∘ β←         ≡⟨ pulll left-strength-λ← ⟩
        λ← ∘ β←                ≡⟨ λ←-β← ⟩
        ρ←                     ∎
      r .right-strength-α← =
        F₁ (α← _ _ _) ∘ F₁ β→ ∘ σ ∘ β←                                       ≡⟨ refl⟩∘⟨ refl⟩∘⟨ pushl3 (sym (lswizzle (σ.is-natural _ _ _) (F.annihilate (◀.annihilate (β≅ .invl))))) ⟩
        F₁ (α← _ _ _) ∘ F₁ β→ ∘ F₁ (β→ ⊗₁ id) ∘ σ ∘ (β← ⊗₁ ⌜ F₁ id ⌝) ∘ β←   ≡⟨ ap! F-id ⟩
        F₁ (α← _ _ _) ∘ F₁ β→ ∘ F₁ (β→ ⊗₁ id) ∘ σ ∘ (β← ⊗₁ id) ∘ β←          ≡⟨ F.extendl3 (sym β→-id⊗β→-α→) ⟩
        F₁ β→ ∘ F₁ (id ⊗₁ β→) ∘ F₁ (α→ _ _ _) ∘ σ ∘ (β← ⊗₁ id) ∘ β←          ≡⟨ refl⟩∘⟨ refl⟩∘⟨ pulll left-strength-α→ ⟩
        F₁ β→ ∘ F₁ (id ⊗₁ β→) ∘ (σ ∘ (id ⊗₁ σ) ∘ α→ _ _ _) ∘ (β← ⊗₁ id) ∘ β← ≡⟨ refl⟩∘⟨ refl⟩∘⟨ pullr (pullr refl) ⟩
        F₁ β→ ∘ F₁ (id ⊗₁ β→) ∘ σ ∘ (id ⊗₁ σ) ∘ α→ _ _ _ ∘ (β← ⊗₁ id) ∘ β←   ≡⟨ refl⟩∘⟨ pushr (pushr (refl⟩∘⟨ sym β←-β←⊗id-α←)) ⟩
        F₁ β→ ∘ (F₁ (id ⊗₁ β→) ∘ σ ∘ (id ⊗₁ σ)) ∘ β← ∘ (β← ⊗₁ id) ∘ α← _ _ _ ≡˘⟨ refl⟩∘⟨ pulll (▶.shufflel (σ.is-natural _ _ _)) ⟩
        F₁ β→ ∘ σ ∘ (id ⊗₁ (F₁ β→ ∘ σ)) ∘ β← ∘ (β← ⊗₁ id) ∘ α← _ _ _         ≡⟨ pushr (pushr (extendl (sym (β←.is-natural _ _ _)))) ⟩
        (F₁ β→ ∘ σ ∘ β←) ∘ ((F₁ β→ ∘ σ) ⊗₁ id) ∘ (β← ⊗₁ id) ∘ α← _ _ _       ≡⟨ refl⟩∘⟨ ◀.pulll (sym (assoc _ _ _)) ⟩
        (F₁ β→ ∘ σ ∘ β←) ∘ ((F₁ β→ ∘ σ ∘ β←) ⊗₁ id) ∘ α← _ _ _               ∎
    left≃right .snd .inv r = l where
      open Right-strength r
      open Left-strength
      l : Left-strength
      l .left-strength .η _ = F₁ β← ∘ τ ∘ β→
      l .left-strength .is-natural _ _ (f , g) =
        (F₁ β← ∘ τ ∘ β→) ∘ (f ⊗₁ F₁ g) ≡⟨ pullr (pullr (β→.is-natural _ _ _)) ⟩
        F₁ β← ∘ τ ∘ (F₁ g ⊗₁ f) ∘ β→   ≡⟨ refl⟩∘⟨ extendl (τ.is-natural _ _ _) ⟩
        F₁ β← ∘ F₁ (g ⊗₁ f) ∘ τ ∘ β→   ≡⟨ F.extendl (β←.is-natural _ _ _) ⟩
        F₁ (f ⊗₁ g) ∘ F₁ β← ∘ τ ∘ β→   ∎
      l .left-strength-λ← =
        F₁ λ← ∘ F₁ β← ∘ τ ∘ β→ ≡⟨ F.pulll λ←-β← ⟩
        F₁ ρ← ∘ τ ∘ β→         ≡⟨ pulll right-strength-ρ← ⟩
        ρ← ∘ β→                ≡⟨ ρ←-β→ ⟩
        λ←                     ∎
      l .left-strength-α→ =
        F₁ (α→ _ _ _) ∘ F₁ β← ∘ τ ∘ β→                                       ≡⟨ refl⟩∘⟨ refl⟩∘⟨ pushl3 (sym (lswizzle (τ.is-natural _ _ _) (F.annihilate (▶.annihilate (β≅ .invr))))) ⟩
        F₁ (α→ _ _ _) ∘ F₁ β← ∘ F₁ (id ⊗₁ β←) ∘ τ ∘ (⌜ F₁ id ⌝ ⊗₁ β→) ∘ β→   ≡⟨ ap! F-id ⟩
        F₁ (α→ _ _ _) ∘ F₁ β← ∘ F₁ (id ⊗₁ β←) ∘ τ ∘ (id ⊗₁ β→) ∘ β→          ≡⟨ F.extendl3 ((refl⟩∘⟨ β←.is-natural _ _ _) ∙ sym β←-β←⊗id-α←) ⟩
        F₁ β← ∘ F₁ (β← ⊗₁ id) ∘ F₁ (α← _ _ _) ∘ τ ∘ (id ⊗₁ β→) ∘ β→          ≡⟨ refl⟩∘⟨ refl⟩∘⟨ pulll right-strength-α← ⟩
        F₁ β← ∘ F₁ (β← ⊗₁ id) ∘ (τ ∘ (τ ⊗₁ id) ∘ α← _ _ _) ∘ (id ⊗₁ β→) ∘ β→ ≡⟨ refl⟩∘⟨ refl⟩∘⟨ pullr (pullr refl) ⟩
        F₁ β← ∘ F₁ (β← ⊗₁ id) ∘ τ ∘ (τ ⊗₁ id) ∘ α← _ _ _ ∘ (id ⊗₁ β→) ∘ β→   ≡⟨ refl⟩∘⟨ pushr (pushr (refl⟩∘⟨ ((refl⟩∘⟨ sym (β→.is-natural _ _ _)) ∙ sym β→-id⊗β→-α→))) ⟩
        F₁ β← ∘ (F₁ (β← ⊗₁ id) ∘ τ ∘ (τ ⊗₁ id)) ∘ β→ ∘ (id ⊗₁ β→) ∘ α→ _ _ _ ≡˘⟨ refl⟩∘⟨ pulll (◀.shufflel (τ.is-natural _ _ _)) ⟩
        F₁ β← ∘ τ ∘ ((F₁ β← ∘ τ) ⊗₁ id) ∘ β→ ∘ (id ⊗₁ β→) ∘ α→ _ _ _         ≡⟨ pushr (pushr (extendl (sym (β→.is-natural _ _ _)))) ⟩
        (F₁ β← ∘ τ ∘ β→) ∘ (id ⊗₁ (F₁ β← ∘ τ)) ∘ (id ⊗₁ β→) ∘ α→ _ _ _       ≡⟨ refl⟩∘⟨ ▶.pulll (sym (assoc _ _ _)) ⟩
        (F₁ β← ∘ τ ∘ β→) ∘ (id ⊗₁ (F₁ β← ∘ τ ∘ β→)) ∘ α→ _ _ _               ∎
    left≃right .snd .rinv r = Right-strength-path $ ext λ (A , B) →
      F₁ β→ ∘ (F₁ β← ∘ τ ∘ β→) ∘ β← ≡⟨ extendl (F.cancell (β≅ .invl)) ⟩
      τ ∘ β→ ∘ β←                   ≡⟨ elimr (β≅ .invl) ⟩
      τ                             ∎
      where open Right-strength r
    left≃right .snd .linv l = Left-strength-path $ ext λ (A , B) →
      F₁ β← ∘ (F₁ β→ ∘ σ ∘ β←) ∘ β→ ≡⟨ extendl (F.cancell (β≅ .invr)) ⟩
      σ ∘ β← ∘ β→                   ≡⟨ elimr (β≅ .invr) ⟩
      σ                             ∎
      where open Left-strength l
```
</details>

## Duality

As hinted to above, a right strength for $F$ on $\cC$ can equivalently
be defined as a left strength on the [[reverse monoidal category]]
$\cC^\rm{rev}$. It is entirely trivial to show that the two definitions
are equivalent:

<!--
```agda
module _ {o ℓ} {C : Precategory o ℓ}
  (M : Monoidal-category C) (F : Functor C C)
  where
  open is-iso
```
-->

```agda
  strength^rev : Left-strength (M ^rev) F ≃ Right-strength M F
  strength^rev = Iso→Equiv is where
    is : Iso _ _
    is .fst l = record
      { right-strength = NT (λ _ → σ) λ _ _ _ → σ.is-natural _ _ _
      ; right-strength-ρ← = left-strength-λ←
      ; right-strength-α← = left-strength-α→
      } where open Left-strength l
    is .snd .inv r = record
      { left-strength = NT (λ _ → τ) λ _ _ _ → τ.is-natural _ _ _
      ; left-strength-λ← = right-strength-ρ←
      ; left-strength-α→ = right-strength-α←
      } where open Right-strength r
    is .snd .rinv _ = Right-strength-path _ _ trivial!
    is .snd .linv _ = Left-strength-path _ _ trivial!
```

## Sets-endofunctors are strong {defines="sets-endofunctors-are-strong"}

<!--
```agda
module _ {ℓ} (F : Functor (Sets ℓ) (Sets ℓ)) where
  open Functor F
  open Left-strength
```
-->

Every endofunctor on $\Sets$, seen as a [[cartesian monoidal category]],
can be equipped with a canonical symmetric strength: the tensor product
$A \otimes FB$ is the actual product of sets, so, given $a : A$, we can
simply apply the functorial action of $F$ on the function $\lambda b.
(a, b)$, yielding a function $FB \to F(A \times B)$.

```agda
  Sets-strength : Left-strength Setsₓ F
  Sets-strength .left-strength .η (A , B) (a , Fb) = F₁ (a ,_) Fb
  Sets-strength .left-strength .is-natural (A , B) (C , D) (ac , bd) =
    ext λ a Fb → (sym (F-∘ _ _) ∙ F-∘ _ _) $ₚ Fb
  Sets-strength .left-strength-λ← =
    ext λ _ Fa → (sym (F-∘ _ _) ∙ F-id) $ₚ Fa
  Sets-strength .left-strength-α→ =
    ext λ a b Fc → (sym (F-∘ _ _) ∙ F-∘ _ _) $ₚ Fc
```

This is an instance of a more general fact: in a *closed*
monoidal category $\cC$ (that is, one with an [[adjunction]] $- \otimes
X \dashv [X, -]$, for example coming from a [[cartesian closed]] category),
left strengths for endofunctors $F : \cC \to \cC$ are equivalent to
$\cC$-*enrichments* of F: that is, natural transformations

$$
\hom_\cC([A, B], [FA, FB])
$$

internalising the functorial action $F_1 : \hom(A, B) \to \hom(FA, FB)$.
Then, what we have shown boils down to the fact that every endofunctor
on $\Sets$ is trivially $\Sets$-enriched!
