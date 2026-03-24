<!--
```agda
{-# OPTIONS --allow-unsolved-metas #-}
open import Cat.Monoidal.Instances.Cartesian
open import Cat.Functor.Bifunctor
open import Cat.Functor.Coherence
open import Cat.Instances.Product
open import Cat.Monoidal.Strength
open import Cat.Monoidal.Braided
open import Cat.Monoidal.Functor
open import Cat.Monoidal.Reverse
open import Cat.Diagram.Monad
open import Cat.Monoidal.Base
open import Cat.Functor.Base
open import Cat.Prelude

import Cat.Functor.Reasoning
import Cat.Reasoning
```
-->

```agda
module Cat.Monoidal.Strength.Monad where
```

# Strong monads {defines="strong-monad monad-strength left-monad-strength right-monad-strength"}

Recall that a (left) [[strength]] for an endofunctor $M : \cC \to
\cC$ on a [[monoidal category]] consists of a natural transformation
$A \otimes MB \to M (A \otimes B)$ allowing us to "slide" things from
the ambient context into the functor. If $M$ is equipped with the
structure of a [[monad]], then it is natural to refine this notion to be
compatible with the monad, yielding the notion of a (left/right-)
**strong monad**.

<!--
```agda
module _ {o ℓ} {C : Precategory o ℓ} (Cᵐ : Monoidal-category C) {M : Functor C C} (monad : Monad-on M) where
  open Cat.Reasoning C
  open Monoidal-category Cᵐ
  open Monad-on monad
```
-->

```agda
  record Left-monad-strength : Type (o ⊔ ℓ) where
    field
      functor-strength : Left-strength Cᵐ M

    open Left-strength functor-strength public

    field
      left-strength-η : ∀ {A B} → σ ∘ (A ▶ η B) ≡ η (A ⊗ B)
      left-strength-μ : ∀ {A B} → σ ∘ (A ▶ μ B) ≡ μ (A ⊗ B) ∘ M₁ σ ∘ σ

  record Right-monad-strength : Type (o ⊔ ℓ) where
    field
      functor-strength : Right-strength Cᵐ M

    open Right-strength functor-strength public

    field
      right-strength-η : ∀ {A B} → τ ∘ (η A ◀ B) ≡ η (A ⊗ B)
      right-strength-μ : ∀ {A B} → τ ∘ (μ A ◀ B) ≡ μ (A ⊗ B) ∘ M₁ τ ∘ τ

  record Monad-strength : Type (o ⊔ ℓ) where
    field
      strength-left : Left-monad-strength
      strength-right : Right-monad-strength

    open Left-monad-strength strength-left hiding (functor-strength) public
    open Right-monad-strength strength-right hiding (functor-strength) public

    field
      strength-α→ : ∀ {A B C}
        → M₁ (α→ (A , B , C)) ∘ τ ∘ (σ ◀ _) ≡ σ ∘ (_ ▶ τ) ∘ α→ (A , M₀ B , C)
```

Strong monads are of particular importance in the semantics of effectful
programming languages: while monads are used to model effects, they do
not capture the fact that monadic computations can make use of
information from the *context*; for example, consider the following
pseudo-Haskell program (in `do` notation, then in two possible
desugared forms):

<div class="mathpar">
```haskell
do
  a ← ma ∷ M A
  b ← mb ∷ M B
  pure (a , b)
```

$=$

```haskell
ma >>= λ a →
  mb >>= λ b →
    pure (a , b)
```

$=$

```haskell
join (fmap (λ a →
  fmap (λ b →
    (a , b)) mb) ma)
```
</div>

Notice that `mb`, and then `a`, are available *under*
$\lambda$-*abstractions*: this is no problem in a functional programming
language like Haskell, because monads are automatically *enriched* in
the sense that the functorial action `fmap` is an *internal* morphism;
in other words, [[$\Sets$-monads are strong]]. But the
mathematical denotation of the above program in a general monoidal
category makes crucial use of the strengths, as we will see below.

With this perspective in mind, the additional coherences imposed on a
*monad* strength are quite natural: using the strength to slide into a
"pure" computation (that is, one in the image of the unit) should yield
a pure computation, and using the strength twice before multiplying
should be the same as using it once after multiplying: they express a
sort of "internal naturality" condition for the unit and multiplication
with respect to the enrichment induced by the strength.

<!--
```agda
    functor-strength : Strength Cᵐ M
    functor-strength .Strength.strength-left  = strength-left .Left-monad-strength.functor-strength
    functor-strength .Strength.strength-right = strength-right .Right-monad-strength.functor-strength
    functor-strength .Strength.strength-α→    = strength-α→

  private unquoteDecl left-eqv = declare-record-iso left-eqv (quote Left-monad-strength)
  Left-monad-strength-path
    : ∀ {a b}
    → a .Left-monad-strength.functor-strength ≡ b .Left-monad-strength.functor-strength
    → a ≡ b
  Left-monad-strength-path p = Iso.injective left-eqv (Σ-prop-path (λ _ → hlevel 1) p)

  private unquoteDecl right-eqv = declare-record-iso right-eqv (quote Right-monad-strength)
  Right-monad-strength-path
    : ∀ {a b}
    → a .Right-monad-strength.functor-strength ≡ b .Right-monad-strength.functor-strength
    → a ≡ b
  Right-monad-strength-path p = Iso.injective right-eqv (Σ-prop-path (λ _ → hlevel 1) p)

  private unquoteDecl strength-eqv = declare-record-iso strength-eqv (quote Monad-strength)
  Monad-strength-path
    : ∀ {a b}
    → a .Monad-strength.strength-left ≡ b .Monad-strength.strength-left
    → a .Monad-strength.strength-right ≡ b .Monad-strength.strength-right
    → a ≡ b
  Monad-strength-path p q = Iso.injective strength-eqv (Σ-pathp p (Σ-prop-pathp (λ _ _ → hlevel 1) q))
```
-->

## Monoidal functors from strong monads {defines="monoidal-functors-from-strong-monads"}

<!--
```agda
module _ {o ℓ}
  {C : Precategory o ℓ} {Cᵐ : Monoidal-category C}
  {M : Functor C C} {monad : Monad-on M}
  where
  open Cat.Reasoning C
  open Monoidal-category Cᵐ
  open Monad-on monad
  private
    module M = Cat.Functor.Reasoning M
  open is-iso

  module _ (s : Monad-strength Cᵐ monad) where
    open Monad-strength s
    open Lax-monoidal-functor-on
```
-->

The above program wasn't picked at random -- it witnesses the common
functional programming wisdom that "every monad is an applicative
functor[^applicative]", whose theoretical underpinning is that, given a
*strong* monad $M$, we can equip $M$ with the structure of a [[lax monoidal
functor]].

[^applicative]: Applicative functors, or *idioms*, are usually defined
as [[lax monoidal functors]] equipped with a compatible strength (not to
be confused with [[strong monoidal functors]]).

In fact, we can do so in *two* different ways, corresponding to
sequencing the effects from left to right or from right to left:

~~~{.quiver}
\[\begin{tikzcd}
  & {M (A \otimes MB)} & {M^2 (A \otimes B)} \\
  {MA \otimes MB} &&& {M (A \otimes B)} \\
  & {M (MA \otimes B)} & {M^2 (A \otimes B)}
  \arrow["\tau", from=2-1, to=1-2]
  \arrow["M\sigma", from=1-2, to=1-3]
  \arrow["\mu", from=1-3, to=2-4]
  \arrow["\sigma"', from=2-1, to=3-2]
  \arrow["M\tau"', from=3-2, to=3-3]
  \arrow["\mu"', from=3-3, to=2-4]
\end{tikzcd}\]
~~~

```agda
    left-φ right-φ : precompose₂ -⊗- M M => postcompose₂ M -⊗-

    left-φ = make-binatural λ where
        .η x y → μ (x ⊗ y) ∘ M.₁ σ ∘ τ
        .is-natural-◀ f x →
          extendr (pullr τ.natural-◀)
          ∙ extendr (M.extendl σ.natural-◀)
          ∙ pushl (mult.is-natural _ _ _)
        .is-natural-▶ x f →
          extendr (pullr τ.natural-▶)
          ∙ extendr (extendl (M.weave σ.natural-▶))
          ∙ pushl (mult.is-natural _ _ _)
       where open Make-binatural

    right-φ = make-binatural λ where
        .η x y → μ (x ⊗ y) ∘ M.₁ τ ∘ σ
        .is-natural-◀ f x →
          extendr (pullr σ.natural-◀)
          ∙ extendr (M.extendl τ.natural-◀)
          ∙ pushl (mult.is-natural _ _ _)
        .is-natural-▶ x f →
          extendr (pullr σ.natural-▶)
          ∙ extendr (M.extendl τ.natural-▶)
          ∙ pushl (mult.is-natural _ _ _)
      where open Make-binatural
```

::: {.definition #commutative-monad alias="commutative-strength"}
If the two ways are the same (thus if the above diagram commutes), we say
that the monad (or the strength) is **commutative**.
:::

```agda
    is-commutative-strength : Type (o ⊔ ℓ)
    is-commutative-strength = right-φ ≡ left-φ
```

<details>
<summary>
We now complete the definition of the *left-to-right* monoidal structure,
which requires a bit of work. For the unit, we pick $\eta_1$, the unit
of the monad.

```agda
    strength→monoidal : Lax-monoidal-functor-on Cᵐ Cᵐ M
    strength→monoidal .ε = η Unit
    strength→monoidal .F-mult = left-φ
```
</summary>

The associator coherence is witnessed by the following ~~monstrosity~~
commutative diagram.

~~~{.quiver}
\[\begin{tikzcd}[column sep=0.4em]
  {(MA\otimes MB)\otimes MC} &&&& {MA\otimes(MB\otimes MC)} \\
  {M(A\otimes MB)\otimes MC} & {M((A\otimes MB)\otimes MC)} & {M(A\otimes (MB\otimes MC))} && {MA\otimes M(B\otimes MC)} \\
  {M^2(A\otimes B)\otimes MC} & {M(M(A\otimes B)\otimes MC)} & {M(A\otimes M(B\otimes MC))} & {M(A\otimes M^2(B\otimes C))} & {MA\otimes M^2(B\otimes C)} \\
  {M(A\otimes B)\otimes MC} & {M^2((A\otimes B)\otimes MC)} & {M^2(A\otimes(B\otimes MC))} & {M^2(A\otimes M(B\otimes C))} & {MA\otimes M(B\otimes C)} \\
  {M((A\otimes B)\otimes MC)} && {M(A\otimes (B\otimes MC))} & {M^3(A\otimes (B\otimes C))} & {M(A\otimes M(B\otimes C))} \\
  && {M(A\otimes M(B\otimes C))} \\
  {M^2((A\otimes B)\otimes C)} &&&& {M^2(A\otimes (B\otimes C))} \\
  {M((A\otimes B)\otimes C)} &&&& {M(A\otimes (B\otimes C))}
  \arrow[from=1-1, to=1-5]
  \arrow[from=1-1, to=2-1]
  \arrow[from=2-1, to=3-1]
  \arrow[from=3-1, to=4-1]
  \arrow[from=4-1, to=5-1]
  \arrow[from=5-1, to=7-1]
  \arrow[from=7-1, to=8-1]
  \arrow[from=8-1, to=8-5]
  \arrow[from=1-5, to=2-5]
  \arrow[from=2-5, to=3-5]
  \arrow[from=3-5, to=4-5]
  \arrow[from=4-5, to=5-5]
  \arrow[from=5-5, to=7-5]
  \arrow[from=7-5, to=8-5]
  \arrow[from=2-1, to=2-2]
  \arrow[from=1-5, to=2-3]
  \arrow[from=2-2, to=2-3]
  \arrow[from=2-5, to=3-3]
  \arrow[from=2-3, to=3-3]
  \arrow[from=3-5, to=3-4]
  \arrow[from=3-3, to=3-4]
  \arrow[from=3-4, to=5-5]
  \arrow[from=2-2, to=3-2]
  \arrow[from=3-1, to=3-2]
  \arrow[from=3-3, to=4-3]
  \arrow[from=3-2, to=4-2]
  \arrow[from=4-2, to=4-3]
  \arrow[from=4-2, to=5-1]
  \arrow[from=5-1, to=5-3]
  \arrow[from=4-3, to=5-3]
  \arrow[from=7-1, to=7-5]
  \arrow[from=4-3, to=4-4]
  \arrow[from=3-4, to=4-4]
  \arrow[from=5-3, to=6-3]
  \arrow[from=6-3, to=7-5]
  \arrow[from=4-4, to=5-4]
  \arrow["\mu"', curve={height=6pt}, from=5-4, to=7-5]
  \arrow[from=4-4, to=6-3]
  \arrow["M\mu", curve={height=-6pt}, from=5-4, to=7-5]
\end{tikzcd}\]
~~~

```agda
    strength→monoidal .F-α→ =
      M.₁ (α→ _) ∘ (μ _ ∘ M.₁ σ  ∘ τ) ∘ (μ _ ∘ M.₁ σ ∘ τ ◀ _)                                ≡⟨ cdr (pullr (pullr refl)) ⟩
      M.₁ (α→ _) ∘ μ _ ∘ M.₁ σ ∘ τ ∘ (μ _ ∘ M.₁ σ ∘ τ ◀ _)                                   ≡⟨ extendl (sym $ mult.is-natural _ _ _) ⟩
      μ _ ∘ M.₁ (M.₁ (α→ _)) ∘ M.₁ σ ∘ τ ∘ (μ _ ∘ M.₁ σ ∘ τ ◀ _)                             ≡⟨ cdr (M.pulll left-strength-α→) ⟩
      μ _ ∘ M.₁ (σ ∘ (_ ▶ σ) ∘ α→ _) ∘ τ ∘ (μ _ ∘ M.₁ σ ∘ τ ◀ _)                             ≡⟨ cddr (◀.popl right-strength-μ ∙ pullr (pullr refl)) ⟩
      μ _ ∘ M.₁ (σ ∘ (_ ▶ σ) ∘ α→ _) ∘ μ _ ∘ M.₁ τ ∘ τ ∘ (M.₁ σ ∘ τ ◀ _)                     ≡⟨ cddddr (◀.popl τ.natural-◀ ∙ pullr refl) ⟩
      μ _ ∘ M.₁ (σ ∘ (_ ▶ σ) ∘ α→ _) ∘ μ _ ∘ M.₁ τ ∘ M.₁ (σ ◀ _) ∘ τ ∘ (τ ◀ _)               ≡⟨ cdr (M.popr (M.popr (extendl (sym (mult.is-natural _ _ _))))) ⟩
      μ _ ∘ M.₁ σ ∘ M.₁ (_ ▶ σ) ∘ μ _ ∘ M.₁ (M.₁ (α→ _)) ∘ M.₁ τ ∘ M.₁ (σ ◀ _) ∘ τ ∘ (τ ◀ _) ≡⟨ cddddr (M.pulll3 strength-α→) ⟩
      μ _ ∘ M.₁ σ ∘ M.₁ (_ ▶ σ) ∘ μ _ ∘ M.₁ (σ ∘ (_ ▶ τ) ∘ α→ _) ∘ τ ∘ (τ ◀ _)               ≡⟨ cddddr (M.popr (M.popr (sym right-strength-α→))) ⟩
      μ _ ∘ M₁ σ ∘ M₁ (_ ▶ σ) ∘ μ _ ∘ M₁ σ ∘ M₁ (_ ▶ τ) ∘ τ ∘ α→ _                           ≡⟨ cddddr (cdr (extendl (sym τ.natural-▶))) ⟩
      μ _ ∘ M₁ σ ∘ M₁ (_ ▶ σ) ∘ μ _ ∘ M₁ σ ∘ τ ∘ (_ ▶ τ) ∘ α→ _                              ≡⟨ cddr (extendl (sym (mult.is-natural _ _ _))) ⟩
      μ _ ∘ M₁ σ ∘ μ _ ∘ M₁ (M₁ (_ ▶ σ)) ∘ M₁ σ ∘ τ ∘ (_ ▶ τ) ∘ α→ _                         ≡⟨ cdr (extendl (sym (mult.is-natural _ _ _))) ⟩
      μ _ ∘ μ _ ∘ M₁ (M₁ σ) ∘ M₁ (M₁ (_ ▶ σ)) ∘ M₁ σ ∘ τ ∘ (_ ▶ τ) ∘ α→ _                    ≡⟨ extendl (sym μ-assoc) ⟩
      μ _ ∘ M₁ (μ _) ∘ M₁ (M₁ σ) ∘ M₁ (M₁ (_ ▶ σ)) ∘ M₁ σ ∘ τ ∘ (_ ▶ τ) ∘ α→ _               ≡⟨ cdddr (M.extendl (sym (σ.natural-▶))) ⟩
      μ _ ∘ M₁ (μ _) ∘ M₁ (M₁ σ) ∘ M₁ σ ∘ M₁ (_ ▶ M₁ σ) ∘ τ ∘ (_ ▶ τ) ∘ α→ _                 ≡⟨ cdr (M.pulll3 (sym left-strength-μ)) ⟩
      μ _ ∘ M₁ (σ ∘ (_ ▶ μ _)) ∘ M₁ (_ ▶ M₁ σ) ∘ τ ∘ (_ ▶ τ) ∘ α→ _                          ≡⟨ cddr (extendl (sym τ.natural-▶)) ⟩
      μ _ ∘ M₁ (σ ∘ (_ ▶ μ _)) ∘ τ ∘ (_ ▶ M₁ σ) ∘ (_ ▶ τ) ∘ α→ _                             ≡⟨ cdr (M.popr (extendl (sym τ.natural-▶))) ⟩
      μ _ ∘ M₁ σ ∘ τ ∘ (_ ▶ μ _) ∘ (_ ▶ M₁ σ) ∘ (_ ▶ τ) ∘ α→ _                               ≡⟨ pushr (pushr (cdr (▶.pulll3 refl))) ⟩
      (μ _ ∘ M₁ σ ∘ τ) ∘ (_ ▶ (μ _ ∘ M₁ σ ∘ τ)) ∘ α→ _                                       ∎
```

The unitor coherences are relatively easy to prove.

```agda
    strength→monoidal .F-λ← =
      M₁ (λ← _) ∘ (μ _ ∘ M₁ σ ∘ τ) ∘ (η _ ◀ _) ≡⟨ cdr (pullr (pullr right-strength-η)) ⟩
      M₁ (λ← _) ∘ μ _ ∘ M₁ σ ∘ η _             ≡˘⟨ cddr (unit.is-natural _ _ _) ⟩
      M₁ (λ← _) ∘ μ _ ∘ η _ ∘ σ                ≡⟨ cdr (cancell μ-unitl) ⟩
      M₁ (λ← _) ∘ σ                            ≡⟨ left-strength-λ← ⟩
      λ← _                                     ∎
    strength→monoidal .F-ρ← =
      M₁ (ρ← _) ∘ (μ _ ∘ M₁ σ ∘ τ) ∘ (_ ▶ η _)  ≡⟨ cdr (pullr (pullr τ.natural-▶)) ⟩
      M₁ (ρ← _) ∘ μ _ ∘ M₁ σ ∘ M₁ (_ ▶ η _) ∘ τ ≡⟨ cddr (M.pulll left-strength-η) ⟩
      M₁ (ρ← _) ∘ μ _ ∘ M₁ (η _) ∘ τ            ≡⟨ cdr (cancell μ-unitr) ⟩
      M₁ (ρ← _) ∘ τ                             ≡⟨ right-strength-ρ← ⟩
      ρ← _                                      ∎
```
</details>

## Symmetry

In a [[braided monoidal category]], we unsurprisingly say that a monad
strength is *symmetric* if the underlying functor [[strength]] is: a
strength with this property is equivalent to the data of a left (or
right) strength, with the other one obtained by the braiding.

```agda
  module _ (Cᵇ : Braided-monoidal Cᵐ) where
    is-symmetric-monad-strength : Monad-strength Cᵐ monad → Type (o ⊔ ℓ)
    is-symmetric-monad-strength s =
      is-symmetric-strength Cᵐ M Cᵇ functor-strength
      where open Monad-strength s
```

## Duality

Just as with functor strengths, the definitions of left and right monad
strengths are completely dual up to [[reversing|reverse monoidal
category]] the tensor product.

```agda
  monad-strength^rev
    : Left-monad-strength (Cᵐ ^rev) monad ≃ Right-monad-strength Cᵐ monad
  monad-strength^rev = Iso→Equiv is where
    is : Iso _ _
    is .fst l = record
      { functor-strength = strength^rev Cᵐ M .fst functor-strength
      ; right-strength-η = left-strength-η
      ; right-strength-μ = left-strength-μ
      } where open Left-monad-strength l
    is .snd .from r = record
      { functor-strength = Equiv.from (strength^rev Cᵐ M) functor-strength
      ; left-strength-η = right-strength-η
      ; left-strength-μ = right-strength-μ
      } where open Right-monad-strength r
    is .snd .rinv _ = Right-monad-strength-path Cᵐ monad
      (Equiv.ε (strength^rev Cᵐ M) _)
    is .snd .linv _ = Left-monad-strength-path (Cᵐ ^rev) monad
      (Equiv.η (strength^rev Cᵐ M) _)
```

## Sets-monads are strong {defines="sets-monads-are-strong"}

<!--
```agda
module _ {ℓ} ((F , monad) : Monad (Sets ℓ)) where
  open Monad-on monad
  open Left-monad-strength
```
-->

The fact that [[$\Sets$-endofunctors are strong]] straightforwardly
extends to the fact that $\Sets$-*monads* are strong, by naturality of
the unit and multiplication.

```agda
  Sets-monad-strength : Left-monad-strength Setsₓ monad
  Sets-monad-strength .functor-strength = Sets-strength F
  Sets-monad-strength .left-strength-η = ext λ a b →
    sym (unit.is-natural _ _ (a ,_) $ₚ _)
  Sets-monad-strength .left-strength-μ = ext λ a mmb →
    sym (mult.is-natural _ _ (a ,_) $ₚ _) ∙ ap (μ _) (M-∘ _ _ $ₚ _)
```
