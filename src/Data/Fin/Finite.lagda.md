```agda
open import 1Lab.Prim.Monad
open import 1Lab.Prelude

open import Algebra.Group.Homotopy.BAut

open import Data.Fin.Properties
open import Data.Fin.Closure
open import Data.Fin.Base
open import Data.Nat
open import Data.Sum

module Data.Fin.Finite where
```

# Finite types

This module pieces together a couple of pre-existing constructions: In
terms of the \r{standard finite sets} (which are defined for natural
numbers $n$) and [deloopings of automorphism groups], we construct the
type of finite types. [By univalence], the space of finite types
classifies maps with finite fibres.

[deloopings of automorphism groups]: Algebra.Group.Homotopy.BAut.html
[By univalence]: 1Lab.Univalence.html#object-classifiers

But what does it mean for a type to be finite? A naïve first approach is
to define "$X$ is finite" to mean "$X$ is equipped with $n : \NN$ and $f
: [n] \simeq X$" but this turns out to be _too strong_: This doesn't
just equip the type $X$ with a cardinality, but also with a choice of
total order. Additionally, defined like this, the type of finite types
_is a set_!

```agda
naïve-fin-is-set : is-set (Σ[ X ∈ Type ] Σ[ n ∈ Nat ] Fin n ≃ X)
naïve-fin-is-set = is-hlevel≃ 2 Σ-swap₂ $
  Σ-is-hlevel 2 (hlevel 2) λ x → is-prop→is-hlevel-suc {n = 1} $
    is-contr→is-prop $ Equiv-is-contr (Fin x)
```

That's because, as the proof above shows, it's equivalent to the type of
natural numbers: The type
$$
\sum_{X : \ty} \sum_{n : \NN}\ [n] \simeq X
$$
is equivalent to the type
$$
\sum_{n : \NN} \sum_{X : \ty} [n] \simeq X\text{,}
$$
and univalence says (rather directly) that the sum of $[n] \simeq X$ as
$X$ ranges over a universe is contractible, so we're left with the type
of natural numbers.

This simply won't do: we want the type of finite sets to be equivalent
to the (core of the) _category_ of finite sets, where the automorphism
group of $n$ has $n!$ elements, not exactly one element. What we do is
appeal to a basic intuition: A groupoid is the sum over its connected
components, and we have representatives for every connected component
(given by the standard finite sets):

```agda
Fin-type : Type (lsuc lzero)
Fin-type = Σ[ n ∈ Nat ] BAut (Fin n)

Fin-type-is-groupoid : is-hlevel Fin-type 3
Fin-type-is-groupoid = Σ-is-hlevel 3 (hlevel 3) λ _ →
  BAut-is-hlevel (Fin _) 2 (hlevel 2)
```

Informed by this, we now express the correct definition of "being
finite", namely, being _merely_ equivalent to some standard finite set.
Rather than using Σ types for this, we can set up typeclass machinery
for automatically deriving boring instances of finiteness, i.e. those
that follow directly from the closure properties.

```agda
record Finite {ℓ} (T : Type ℓ) : Type ℓ where
  constructor fin
  field
    {cardinality} : Nat
    enumeration   : ∥ T ≃ Fin cardinality ∥

open Finite ⦃ ... ⦄ public
```

<!--
```agda
instance
  H-Level-Finite : ∀ {ℓ} {A : Type ℓ} {n : Nat} → H-Level (Finite A) (suc n)
  H-Level-Finite = prop-instance {T = Finite _} λ where
    x y i .Finite.cardinality → ∥-∥-proj
      ⦇ Fin-injective (⦇ ⦇ x .enumeration e⁻¹ ⦈ ∙e y .enumeration ⦈) ⦈
      i
    x y i .Finite.enumeration → is-prop→pathp
      {B = λ i → ∥ _ ≃ Fin (∥-∥-proj ⦇ Fin-injective (⦇ ⦇ x .enumeration e⁻¹ ⦈ ∙e y .enumeration ⦈) ⦈ i) ∥}
      (λ _ → squash)
      (x .enumeration) (y .enumeration) i

Finite-choice
  : ∀ {ℓ ℓ′} {A : Type ℓ} {B : A → Type ℓ′}
  → ⦃ Finite A ⦄
  → (∀ x → ∥ B x ∥) → ∥ (∀ x → B x) ∥
Finite-choice {B = B} ⦃ fin {sz} e ⦄ k = do
  e ← e
  choose ← finite-choice sz λ x → k (equiv→inverse (e .snd) x)
  pure $ λ x → subst B (equiv→unit (e .snd) x) (choose (e .fst x))

private variable
  ℓ : Level
  A B : Type ℓ
  P Q : A → Type ℓ
```
-->

```agda
instance
  Finite-Fin : ∀ {n} → Finite (Fin n)
  Finite-× : ⦃ Finite A ⦄ → ⦃ Finite B ⦄ → Finite (A × B)
  Finite-⊎ : ⦃ Finite A ⦄ → ⦃ Finite B ⦄ → Finite (A ⊎ B)

  Finite-Σ
    : {P : A → Type ℓ} → ⦃ Finite A ⦄ → ⦃ ∀ x → Finite (P x) ⦄ → Finite (Σ A P)
  Finite-Π
    : {P : A → Type ℓ} → ⦃ Finite A ⦄ → ⦃ ∀ x → Finite (P x) ⦄ → Finite (∀ x → P x)
```

<!--
```agda
private
  finite-pi-fin
    : ∀ {ℓ′} n {B : Fin n → Type ℓ′}
    → (∀ x → Finite (B x))
    → Finite ((x : Fin n) → B x)
  finite-pi-fin zero fam = fin {cardinality = 1} $ pure $ Iso→Equiv λ where
    .fst x → fzero
    .snd .is-iso.inv x ()
    .snd .is-iso.rinv fzero → refl
    .snd .is-iso.linv x → funext λ { () }

  finite-pi-fin (suc sz) {B} fam = ∥-∥-proj $ do
    e ← finite-choice (suc sz) λ x → fam x .enumeration
    let rest = finite-pi-fin sz (λ x → fam (fsuc x))
    cont ← rest .Finite.enumeration
    let
      work = Fin-suc-universal {n = sz} {A = B}
        ∙e Σ-ap (e fzero) (λ x → cont)
        ∙e Finite-sum λ _ → rest .Finite.cardinality
    pure $ fin $ pure work

Finite-Fin = fin (inc (_ , id-equiv))
Finite-× {A = A} {B = B} = fin $ do
  aeq ← enumeration {T = A}
  beq ← enumeration {T = B}
  pure ((Σ-ap aeq λ _ → beq) ∙e Finite-product)

Finite-⊎ {A = A} {B = B} = fin $ do
  aeq ← enumeration {T = A}
  beq ← enumeration {T = B}
  pure (⊎-ap aeq beq ∙e Finite-coproduct)

Finite-Π {A = A} {P = P} ⦃ fin {sz} en ⦄ ⦃ fam ⦄ = ∥-∥-proj $ do
  eqv ← en
  let count = finite-pi-fin sz λ x → fam $ equiv→inverse (eqv .snd) x
  eqv′ ← count .Finite.enumeration
  pure $ fin $ pure $ Π-dom≃ (eqv e⁻¹) ∙e eqv′

Finite-Σ {A = A} {P = P} ⦃ afin ⦄ ⦃ fam ⦄ = ∥-∥-proj $ do
  aeq ← afin .Finite.enumeration
  let
    module aeq = Equiv aeq
    bc : (x : Fin (afin .Finite.cardinality)) → Nat
    bc x = fam (aeq.from x) .Finite.cardinality

    fs : (Σ _ λ x → Fin (bc x)) ≃ Fin (sum (afin .Finite.cardinality) bc)
    fs = Finite-sum bc
    work = do
      t ← Finite-choice λ x → fam x .Finite.enumeration
      pure $ Σ-ap aeq λ x → t x
          ∙e (_ , cast-is-equiv (ap (λ e → fam e .cardinality)
                    (sym (aeq.η x))))
  pure $ fin ⦇ work ∙e pure fs ⦈
```
-->
