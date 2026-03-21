<!--
```agda
{-# OPTIONS --allow-unsolved-metas #-}
open import Cat.Functor.Adjoint.Reflective
open import Cat.Monoidal.Strength.Monad
open import Cat.Functor.Naturality
open import Cat.Functor.Properties
open import Cat.Monoidal.Diagonals
open import Cat.Monoidal.Functor
open import Cat.Displayed.Total
open import Cat.Diagram.Monad
open import Cat.Monoidal.Base
open import Cat.Functor.Base
open import Cat.Prelude

import Cat.Functor.Reasoning
import Cat.Reasoning

open Algebra-on
open Functor
```
-->

```agda
module Cat.Diagram.Monad.Idempotent {o ℓ}
  {C : Precategory o ℓ} {M : Functor C C} (monad : Monad-on M)
  where
```

# Idempotent monads {defines="idempotent-monad"}

<!--
```agda
open Cat.Reasoning C
open Monad-on monad
private
  module M = Cat.Functor.Reasoning M
```
-->

A [[monad]] $M$ is said to be **idempotent** if it "squares to itself"
in the sense that its multiplication is a [[natural isomorphism]] $\mu :
M^2 \cong M$.

```agda
is-idempotent-monad : Type (o ⊔ ℓ)
is-idempotent-monad = is-invertibleⁿ mult
```

The intuition is that an idempotent monad on $\cC$ equips its algebras
with *property*, rather than structure: in that sense, it contains
exactly as much information as a [[reflective subcategory]] of $\cC$.
More precisely, the forgetful functor from the [[Eilenberg-Moore category]]
of an idempotent monad is a reflective subcategory inclusion, and
conversely any reflective [[adjunction]] $F \dashv U$ yields an
idempotent monad $UF$.

This means that idempotent monads may be used to interpret *modalities*
in type theory. As a motivating, if informal, example, think of the
($\infty$-)category of types and functions: the property of being an
[[$n$-type]] defines a reflective subuniverse whose corresponding
idempotent monad is the $n$-[[truncation]] operator.

We start by showing the following elementary characterisation: a monad
is idempotent if and only if $\eta M, M \eta : M \To M^2$ are equal.
In the forwards direction, the monad laws tell us that $\mu \circ \eta M
\equiv \mu \circ M \eta$, and we've assumed that $\mu$ is invertible,
hence in particular [[monic]].

```agda
opaque
  idempotent→η≡Mη : is-idempotent-monad → ∀ A → η (M₀ A) ≡ M₁ (η A)
  idempotent→η≡Mη idem A = invertible→monic
    (is-invertibleⁿ→is-invertible idem A) _ _
    (μ-unitl ∙ sym μ-unitr)
```

For the other direction, we can prove a slightly more general result:
assuming $\eta M \equiv M \eta$, *any* $M$-[[algebra|monad algebra]] $\nu : MA \to A$
is invertible. Indeed, algebra laws guarantee that $\eta M$ is a right
inverse of $\nu$; we check that it is also a left inverse by a short
computation involving the naturality of $\eta$.

```agda
η≡Mη→algebra-invertible
  : (∀ A → η (M₀ A) ≡ M₁ (η A))
  → ∀ (A : Algebra monad)
  → is-invertible (A .snd .ν)
η≡Mη→algebra-invertible h (A , alg) = make-invertible (η _) (alg .ν-unit) $
  η A ∘ alg .ν           ≡⟨ unit.is-natural _ _ _ ⟩
  M₁ (alg .ν) ∘ η (M₀ A) ≡⟨ refl⟩∘⟨ h A ⟩
  M₁ (alg .ν) ∘ M₁ (η A) ≡⟨ M.annihilate (alg .ν-unit) ⟩
  id                     ∎
```

In particular, by applying this to the [[*free* algebras]] we get that
$\mu$ is componentwise invertible.

```agda
η≡Mη→idempotent : (∀ A → η (M₀ A) ≡ M₁ (η A)) → is-idempotent-monad
η≡Mη→idempotent h = invertible→invertibleⁿ _ λ A →
  η≡Mη→algebra-invertible h (Free-EM .F₀ A)

idempotent≃η≡Mη : is-idempotent-monad ≃ (∀ A → η (M₀ A) ≡ M₁ (η A))
idempotent≃η≡Mη = prop-ext! idempotent→η≡Mη η≡Mη→idempotent
```

As a consequence, if $\mu$ is only componentwise *[[monic]]*, then
we can still conclude that $\eta M \equiv M \eta$ and hence that $M$
is idempotent.

```agda
μ-monic→idempotent : (∀ A → is-monic (μ A)) → is-idempotent-monad
μ-monic→idempotent monic = η≡Mη→idempotent λ A →
  monic _ _ _ (μ-unitl ∙ sym μ-unitr)
```

Finally, we turn to showing the equivalence with reflective subcategories.

The forgetful functor out of the Eilenberg-Moore category is always
[[faithful|faithful functor]], so we need to show that it is [[full|full functor]]; that
is, that any map $f : A \to B$ between $M$-algebras is an algebra
morphism, in that it makes the outer square commute:

~~~{.quiver}
\[\begin{tikzcd}
  MA & MB \\
  A & B
  \arrow["a"', from=1-1, to=2-1]
  \arrow["b", from=1-2, to=2-2]
  \arrow["Mf", from=1-1, to=1-2]
  \arrow["f"', from=2-1, to=2-2]
  \arrow["{\eta_A}"', curve={height=6pt}, from=2-1, to=1-1]
  \arrow["{\eta_B}", curve={height=-6pt}, from=2-2, to=1-2]
\end{tikzcd}\]
~~~

As we showed earlier, the algebras $a$ and $b$ are both inverses of
$\eta$, so this reduces to showing that the *inner* square commutes,
which is just the naturality of $\eta$.

```agda
idempotent→reflective : is-idempotent-monad → is-reflective Free-EM⊣Forget-EM
idempotent→reflective idem = full+faithful→ff Forget-EM
  (λ {(A , a)} {(B , b)} f → inc (∫hom f
    (sym (swizzle (sym (unit.is-natural _ _ _))
      (η≡Mη→algebra-invertible (idempotent→η≡Mη idem) (A , a) .is-invertible.invr)
      (b .ν-unit)))
    , refl))
  Forget-EM-is-faithful
```

<!--
```agda
_ = is-reflective→is-monadic
```
-->

In the other direction, we will show that, if the free-forgetful
adjunction is reflective, then $M$ is an idempotent monad. Note that
this doesn't lose any generality over our initial claim, since any
reflective adjunction $F \dashv U$ `is monadic`{.Agda
ident=is-reflective→is-monadic}!

Since the adjunction is reflective, we know the counit of the adjunction
$\epsilon : F \circ U \To \Id$ is an isomorphism; hence the whiskering
$U \epsilon F$ must be as well, but this is exactly the multiplication
of our monad.

```agda
reflective→idempotent : is-reflective (Free-EM⊣Forget-EM {M = monad}) → is-idempotent-monad
reflective→idempotent ref = invertible→invertibleⁿ _ λ A →
  iso→invertible (F-map-iso Forget-EM
    (is-reflective→counit-is-iso Free-EM⊣Forget-EM ref
      {Free-EM .F₀ A}))

idempotent≃reflective : is-idempotent-monad ≃ is-reflective Free-EM⊣Forget-EM
idempotent≃reflective = prop-ext! idempotent→reflective reflective→idempotent
```

## Strong idempotent monads

Being an idempotent monad is quite a strong property. Indeed, if the monad
is also [[strong|strong monad]], then it has to be [[commutative|commutative monad]].

<!--
```agda
module _ (idem : is-idempotent-monad) (Cᵐ : Monoidal-category C) (s : Monad-strength Cᵐ monad) where
  open Monoidal-category Cᵐ
  open Monad-strength s
```
-->

::: source
The following proof comes from the nLab page on [idempotent monads];
see there for a diagram.
:::

[idempotent monads]: https://ncatlab.org/nlab/show/idempotent+monad#idempotent_strong_monads_are_commutative

```agda
  opaque
    idempotent→commutative : is-commutative-strength s
    idempotent→commutative = ext λ A B → {!   !}
      -- μ _ ∘ M₁ τ ∘ σ                                              ≡⟨ insertl μ-unitl ⟩
      -- μ _ ∘ η _ ∘ μ _ ∘ M₁ τ ∘ σ                                  ≡⟨ refl⟩∘⟨ unit.is-natural _ _ _ ⟩
      -- μ _ ∘ M₁ (μ _ ∘ M₁ τ ∘ σ) ∘ η _                             ≡˘⟨ refl⟩∘⟨ refl⟩∘⟨ right-strength-η ⟩
      -- μ _ ∘ M₁ (μ _ ∘ M₁ τ ∘ σ) ∘ τ ∘ (⌜ η _ ⌝ ⊗₁ id)             ≡⟨ ap! (idempotent→η≡Mη idem _) ⟩
      -- μ _ ∘ M₁ (μ _ ∘ M₁ τ ∘ σ) ∘ τ ∘ (M₁ (η _) ⊗₁ id)            ≡⟨ refl⟩∘⟨ refl⟩∘⟨ {! τ.is-natural _ _ _ !} ⟩
      -- μ _ ∘ M₁ (μ _ ∘ M₁ τ ∘ σ) ∘ M₁ (η _ ⊗₁ ⌜ id ⌝) ∘ τ          ≡˘⟨ ap¡ M-id ⟩
      -- μ _ ∘ M₁ (μ _ ∘ M₁ τ ∘ σ) ∘ M₁ (η _ ⊗₁ M₁ id) ∘ τ           ≡⟨ refl⟩∘⟨ M.popr (M.popr (extendl (M.weave {! (σ.is-natural _ _ _ ηₚ _) !}))) ⟩
      -- μ _ ∘ M₁ (μ _) ∘ M₁ (M₁ τ) ∘ M₁ (M₁ (η _ ⊗₁ id)) ∘ M₁ σ ∘ τ ≡⟨ refl⟩∘⟨ refl⟩∘⟨ M.pulll (M.collapse right-strength-η) ⟩
      -- μ _ ∘ M₁ (μ _) ∘ M₁ (M₁ (η _)) ∘ M₁ σ ∘ τ                   ≡⟨ refl⟩∘⟨ M.cancell μ-unitr ⟩
      -- μ _ ∘ M₁ σ ∘ τ                                              ∎
```

If furthermore we are in a [[monoidal category with diagonals]],
then the [[monoidal functor]] induced by the strength is automatically
an [[idempotent monoidal functor]].

The proof is by chasing the following slightly wonky diagram.

~~~{.quiver}
\[\begin{tikzcd}
  MA &&& {MA \times MA} & {M(A \times MA)} \\
  & MMA \\
  && {M(MA \times MA)} & {M^2(A \times MA)} \\
  \\
  {M(A \times A)} && {M(A \times MA)} && {M(A \times MA)} \\
  & {M^2(A \times A)}
  \arrow["\mu", curve={height=-6pt}, from=6-2, to=5-1]
  \arrow["M\delta"', from=1-1, to=5-1]
  \arrow["M\eta"', curve={height=6pt}, from=1-1, to=2-2]
  \arrow["M\delta", from=2-2, to=3-3]
  \arrow["M\tau", from=3-3, to=3-4]
  \arrow["\eta", from=1-4, to=3-3]
  \arrow["M\eta"{pos=0.8}, curve={height=-6pt}, from=5-1, to=6-2]
  \arrow["{M(\eta\times\eta)}", from=5-1, to=3-3]
  \arrow["{M(A \times \eta)}", from=5-1, to=5-3]
  \arrow["{M(\eta\times MA)}", from=5-3, to=3-3]
  \arrow["\eta"', from=5-3, to=3-4]
  \arrow["\tau", from=1-4, to=1-5]
  \arrow["\delta", from=1-1, to=1-4]
  \arrow["\eta", curve={height=-6pt}, from=1-1, to=2-2]
  \arrow["M\sigma", from=5-3, to=6-2]
  \arrow["\eta", from=1-5, to=3-4]
  \arrow["\mu", from=3-4, to=5-5]
  \arrow[Rightarrow, no head, from=1-5, to=5-5]
  \arrow[Rightarrow, no head, from=5-5, to=5-3]
\end{tikzcd}\]
~~~

```agda
  module _ (Cᵈ : Diagonals Cᵐ) where
    open Diagonals Cᵈ

    opaque
      idempotent-monad→diagonal
        : is-diagonal-functor _ _ Cᵈ Cᵈ (M , strength→monoidal s)
      idempotent-monad→diagonal = {!   !}
        -- (μ _ ∘ M₁ σ ∘ τ) ∘ δ                                             ≡⟨ pullr (pullr (insertl μ-unitl)) ⟩
        -- μ _ ∘ M₁ σ ∘ μ _ ∘ η _ ∘ τ ∘ δ                                   ≡⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ unit.is-natural _ _ _ ⟩
        -- μ _ ∘ M₁ σ ∘ μ _ ∘ M₁ (τ ∘ δ) ∘ η _                              ≡⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ idempotent→η≡Mη idem _ ⟩
        -- μ _ ∘ M₁ σ ∘ μ _ ∘ M₁ (τ ∘ δ) ∘ M₁ (η _)                         ≡⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ M.pushl refl ⟩
        -- μ _ ∘ M₁ σ ∘ μ _ ∘ M₁ τ ∘ M₁ δ ∘ M₁ (η _)                        ≡⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ M.weave (δ.is-natural _ _ _) ⟩
        -- μ _ ∘ M₁ σ ∘ μ _ ∘ M₁ τ ∘ M₁ (η _ ⊗₁ η _) ∘ M₁ δ                 ≡⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ M.pushl (⊗.expand (sym (idr _) ,ₚ sym (idl _))) ⟩
        -- μ _ ∘ M₁ σ ∘ μ _ ∘ M₁ τ ∘ M₁ (η _ ⊗₁ id) ∘ M₁ (id ⊗₁ η _) ∘ M₁ δ ≡⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ M.pulll right-strength-η ⟩
        -- μ _ ∘ M₁ σ ∘ μ _ ∘ M₁ (η _) ∘ M₁ (id ⊗₁ η _) ∘ M₁ δ              ≡⟨ refl⟩∘⟨ refl⟩∘⟨ cancell μ-unitr ⟩
        -- μ _ ∘ M₁ σ ∘ M₁ (id ⊗₁ η _) ∘ M₁ δ                               ≡⟨ refl⟩∘⟨ M.pulll left-strength-η ⟩
        -- μ _ ∘ M₁ (η _) ∘ M₁ δ                                            ≡⟨ cancell μ-unitr ⟩
        -- M₁ δ                                                             ∎
```
