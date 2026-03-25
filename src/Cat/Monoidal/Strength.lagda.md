<!--
```agda
open import 1Lab.Reflection.Record

open import Cat.Monoidal.Instances.Cartesian
open import Cat.Functor.Naturality
open import Cat.Functor.Bifunctor
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
      left-strength : precompose₂ -⊗- Id F => postcompose₂ F -⊗-

    module σ = Binatural left-strength

    σ : ∀ {A B} → Hom (A ⊗ F₀ B) (F₀ (A ⊗ B))
    σ = σ.η _ _

    field
      left-strength-λ← : ∀ {A} → F₁ (λ← A) ∘ σ ≡ λ← _
      left-strength-α→ : ∀ {A B C}
        → F₁ (α→ (A , B , C)) ∘ σ ≡ σ ∘ (_ ▶ σ) ∘ α→ (A , B , F₀ C)
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
      right-strength : precompose₂ -⊗- F Id => postcompose₂ F -⊗-

    module τ = Binatural right-strength

    τ : ∀ {A B} → Hom (F₀ A ⊗ B) (F₀ (A ⊗ B))
    τ = τ.η _ _

    field
      right-strength-ρ← : ∀ {A} → F₁ (ρ← A) ∘ τ ≡ ρ← _
      right-strength-α← : ∀ {A B C}
        → F₁ (α← (A , B , C)) ∘ τ ≡ τ ∘ (τ ◀ C) ∘ α← (F₀ A , B , C)
```

<!--
```agda
    right-strength-α→ : ∀ {A B C} → τ ∘ α→ (F₀ A , B , C) ≡ F₁ (α→ _) ∘ τ ∘ (τ ◀ C)
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
        → F₁ (α→ (A , B , C)) ∘ τ ∘ (σ ◀ _) ≡ σ ∘ (_ ▶ τ) ∘ α→ (A , F₀ B , C)
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
      open Make-binatural
      r : Right-strength
      r .right-strength = make-binatural λ where
        .η _ _ → F₁ β→ ∘ σ ∘ β←
        .is-natural-◀ f _ →
          (F₁ β→ ∘ σ ∘ β←) ∘ (F₁ f ◀ _) ≡⟨ pullr (pullr β←◀) ⟩
          F₁ β→ ∘ σ ∘ (_ ▶ F₁ f) ∘ β←   ≡⟨ extend-inner σ.natural-▶ ⟩
          F₁ β→ ∘ F₁ (_ ▶ f) ∘ σ ∘ β←   ≡⟨ F.extendl β→▶ ⟩
          F₁ (f ◀ _) ∘ F₁ β→ ∘ σ ∘ β←   ∎
        .is-natural-▶ _ f →
          (F₁ β→ ∘ σ ∘ β←) ∘ (_ ▶ f)    ≡⟨ pullr (pullr β←▶) ⟩
          F₁ β→ ∘ σ ∘ (f ◀ _) ∘ β←      ≡⟨ cdr (extendl σ.natural-◀) ⟩
          F₁ β→ ∘ (F₁ (f ◀ _) ∘ σ ∘ β←) ≡⟨ F.extendl β→◀ ⟩
          F₁ (_ ▶ f) ∘ F.₁ β→ ∘ σ ∘ β←  ∎
      r .right-strength-ρ← =
        F₁ (ρ← _) ∘ F₁ β→ ∘ σ ∘ β← ≡⟨ F.pulll ρ←-β→ ⟩
        F₁ (λ← _) ∘ σ ∘ β←         ≡⟨ pulll left-strength-λ← ⟩
        λ← _ ∘ β←                  ≡⟨ λ←-β← ⟩
        ρ← _                       ∎
      r .right-strength-α← =
        F₁ (α← _) ∘ F₁ β→ ∘ σ ∘ β←                                 ≡⟨ cddr (pushl3 (sym (lswizzle σ.natural-◀ (F.annihilate (◀.annihilate (β≅ .invl)))))) ⟩
        F₁ (α← _) ∘ F₁ β→ ∘ F₁ (β→ ◀ _) ∘ σ ∘ (β← ◀ _) ∘ β←        ≡⟨ F.extendl3 (sym β→-id⊗β→-α→) ⟩
        F₁ β→ ∘ F₁ (_ ▶ β→) ∘ F₁ (α→ _) ∘ σ ∘ (β← ◀ _) ∘ β←        ≡⟨ cddr (extendl left-strength-α→ ∙ cdr (pullr refl)) ⟩
        F₁ β→ ∘ F₁ (_ ▶ β→) ∘ σ ∘ (_ ▶ σ) ∘ α→ _ ∘ (β← ◀ _) ∘ β←   ≡⟨ cddr (cddr (sym β←-β←⊗id-α←)) ⟩
        F₁ β→ ∘ F₁ (_ ▶ β→) ∘ σ ∘ (_ ▶ σ) ∘ β← ∘ (β← ◀ _) ∘ α← _   ≡⟨ cdr (extendl (sym σ.natural-▶) ∙ cdr (▶.pulll refl)) ⟩
        F₁ β→ ∘ σ ∘ (_ ▶ F.₁ β→ ∘ σ) ∘ β← ∘ (β← ◀ _) ∘ α← _        ≡⟨ pushr (pushr (extendl (sym β←◀) ∙ cdr (◀.pulll (pullr refl)))) ⟩
        (F₁ β→ ∘ σ ∘ β←) ∘ (F₁ β→ ∘ σ ∘ β← ◀ _) ∘ α← _             ∎
    left≃right .snd .from r = l where
      open Right-strength r
      open Left-strength
      open Make-binatural
      l : Left-strength
      l .left-strength = make-binatural λ where
         .η _ _ → F₁ β← ∘ τ ∘ β→
         .is-natural-◀ f _ →
           (F₁ β← ∘ τ ∘ β→) ∘ (f ◀ _)  ≡⟨ pullr (pullr β→◀) ⟩
           F₁ β← ∘ τ ∘ (_ ▶ f) ∘ β→    ≡⟨ cdr (extendl τ.natural-▶) ⟩
           F₁ β← ∘ F₁ (_ ▶ f) ∘ τ ∘ β→ ≡⟨ F.extendl β←▶ ⟩
           F₁ (f ◀ _) ∘ F₁ β← ∘ τ ∘ β→ ∎
         .is-natural-▶ _ f →
           (F₁ β← ∘ τ ∘ β→) ∘ (_ ▶ F₁ f) ≡⟨ pullr (pullr β→▶) ⟩
           F₁ β← ∘ τ ∘ (F₁ f ◀ _) ∘ β→   ≡⟨ cdr (extendl τ.natural-◀) ⟩
           F₁ β← ∘ F₁ (f ◀ _) ∘ τ ∘ β→   ≡⟨ F.extendl β←◀ ⟩
           F₁ (_ ▶ f) ∘ F₁ β← ∘ τ ∘ β→   ∎
      l .left-strength-λ← =
        F₁ (λ← _) ∘ F₁ β← ∘ τ ∘ β→ ≡⟨ F.pulll λ←-β← ⟩
        F₁ (ρ← _) ∘ τ ∘ β→         ≡⟨ pulll right-strength-ρ← ⟩
        ρ← _ ∘ β→                  ≡⟨ ρ←-β→ ⟩
        λ← _                       ∎
      l .left-strength-α→ =
        F₁ (α→ _) ∘ F₁ β← ∘ τ ∘ β→                               ≡⟨ cddr (pushl3 (sym (lswizzle τ.natural-▶ (F.annihilate (▶.annihilate (β≅ .invr)))))) ⟩
        F₁ (α→ _) ∘ F₁ β← ∘ F₁ (_ ▶ β←) ∘ τ ∘ (_ ▶ β→) ∘ β→      ≡⟨ F.extendl3 (cdr β←▶ ∙ sym β←-β←⊗id-α←) ⟩
        F₁ β← ∘ F₁ (β← ◀ _) ∘ F₁ (α← _) ∘ τ ∘ (_ ▶ β→) ∘ β→      ≡⟨ cddr (extendl right-strength-α← ∙ cdr (pullr refl)) ⟩
        F₁ β← ∘ F₁ (β← ◀ _) ∘ τ ∘ (τ ◀ _) ∘ α← _ ∘ (_ ▶ β→) ∘ β→ ≡⟨ cddr (cddr (cdr (sym β→◀) ∙ sym β→-id⊗β→-α→)) ⟩
        F₁ β← ∘ F₁ (β← ◀ _) ∘ τ ∘ (τ ◀ _) ∘ β→ ∘ (_ ▶ β→) ∘ α→ _ ≡⟨ cdr (extendl (sym τ.natural-◀) ∙ cdr (◀.pulll refl)) ⟩
        F₁ β← ∘ τ ∘ ((F₁ β← ∘ τ) ◀ _) ∘ β→ ∘ (_ ▶ β→) ∘ α→ _     ≡⟨ pushr (pushr (extendl (sym β→▶) ∙ cdr (▶.pulll (pullr refl)))) ⟩
        ((F₁ β← ∘ τ ∘ β→) ∘ (_ ▶ (F₁ β← ∘ τ ∘ β→)) ∘ α→ _)       ∎
    left≃right .snd .rinv r = Right-strength-path $ ext λ A B →
      F₁ β→ ∘ (F₁ β← ∘ τ ∘ β→) ∘ β← ≡⟨ extendl (F.cancell (β≅ .invl)) ⟩
      τ ∘ β→ ∘ β←                   ≡⟨ elimr (β≅ .invl) ⟩
      τ                             ∎
      where open Right-strength r
    left≃right .snd .linv l = Left-strength-path $ ext λ A B →
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
  open Cat.Reasoning C
  private module M = Monoidal-category M using (module ▶)
  open is-iso
```
-->

```agda
  strength^rev : Left-strength (M ^rev) F ≃ Right-strength M F
  strength^rev = Iso→Equiv is where
    is : Iso (Left-strength (M ^rev) F) (Right-strength M F)
    is .fst l = record
      { right-strength    = NT (λ _ → NT (λ _ → σ) (λ _ _ _ → σ.natural-◀)) λ _ _ _ → ext λ _ → σ.natural-▶
      ; right-strength-ρ← = left-strength-λ←
      ; right-strength-α← = left-strength-α→
      }
      where open Left-strength l
    is .snd .from r = record
      { left-strength    = NT (λ _ → NT (λ _ → τ) λ _ _ _ → τ.natural-◀) λ _ _ _ → ext λ _ → τ.natural-▶
      ; left-strength-λ← = right-strength-ρ←
      ; left-strength-α→ = right-strength-α←
      }
      where open Right-strength r
    is .snd .rinv _ = Right-strength-path _ _ $ ext λ _ _ → refl
    is .snd .linv _ = Left-strength-path  _ _ $ ext λ _ _ → refl
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
  Sets-strength .left-strength .η A .η B (a , Fb) = F₁ (a ,_) Fb
  Sets-strength .left-strength .η A .is-natural _ _ _ = ext λ a Fb →
    (sym (F-∘ _ _) ∙ F-∘ _ _) $ₚ Fb
  Sets-strength .left-strength .is-natural x y f = ext λ _ a Fb → F-∘ _ _ $ₚ Fb
  Sets-strength .left-strength-λ← = ext λ _ Fa → (sym (F-∘ _ _) ∙ F-id) $ₚ Fa
  Sets-strength .left-strength-α→ = ext λ a b Fc → (sym (F-∘ _ _) ∙ F-∘ _ _) $ₚ Fc
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
