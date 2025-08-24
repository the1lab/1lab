<!--
```agda
open import 1Lab.HLevel.Closure
open import 1Lab.Prelude

open import Data.Maybe
open import Data.Bool
open import Data.Dec
open import Data.Fin
open import Data.Nat
open import Data.Sum
```
-->

```agda
module Lang.STLC.DebruIntrinsic where
```

# The simply typed lambda calculus, fancier-er

You may have noticed that last time, the typing
derivations looks suspiciously similar to the terms themselves.
What if we could just make the terms the typing derivations at the
same time?

```agda
infixr 30 _`⇒_
infix 30 _`×_

data Ty : Type where
  `⊤ : Ty
  _`×_ : Ty → Ty → Ty
  _`⇒_ : Ty → Ty → Ty
```

We need slightly fancier contexts this time. We could import and use
lists, but this definition is more beneficial to understanding.

```agda
infixl 20 _,,_
data Con : Type where
  ∅ : Con
  _,,_ : Con → Ty → Con
```

We need a slightly more high tech membership. This time, having a type
in a context is a proof instead of just a lookup.

We could call these constructors `here` and `there`, but we'll call them
`Z` and `S` because they correspond to de Bruijn indexes.

```agda
infix 10 _∋_
data _∋_ : Con → Ty → Type where
  Z : ∀ {Γ A} →
         Γ ,, A ∋ A
  S_ : ∀ {Γ A B} →
         Γ ∋ A →
         Γ ,, B ∋ A
```

Now we write only one judgement, instead of both terms and typing
judgements seperately. We will call it `_⊢_`{.Agda}.

```agda
infix 10 _⊢_
data _⊢_ : Con → Ty → Type where
```

If a context contains a type, it can bind it to a variable.

```agda
  ` : ∀ {Γ A} →
        Γ ∋ A →
        Γ ⊢ A
```

The others follow roughly as they did in the extrinsic de bruijn presentation.

```agda
  `λ : ∀ {Γ A B} →
       Γ ,, A ⊢ B →
       Γ ⊢ A `⇒ B
  _`$_ : ∀ {Γ A B} →
       Γ ⊢ A `⇒ B →
       Γ ⊢ A →
       Γ ⊢ B
  `⟨_,_⟩ : ∀ {Γ A B} →
       Γ ⊢ A →
       Γ ⊢ B →
       Γ ⊢ A `× B
  `π₁ : ∀ {Γ A B} →
       Γ ⊢ A `× B →
       Γ ⊢ A
  `π₂ : ∀ {Γ A B} →
       Γ ⊢ A `× B →
       Γ ⊢ B
  `tt : ∀ {Γ} → Γ ⊢ `⊤
```

Let's try some terms:


<!--
```agda
module Example-1 where
```
-->

```agda
  id' : ∅ ⊢ `⊤ `⇒ `⊤
  id' = `λ (` Z)

  proj' : ∅ ⊢ `⊤
  proj' = `π₁ `⟨ `tt , `tt ⟩
```


Substitution time! Using very similar ideas to the
simultaneous substitution in the previous.

```agda
exts : ∀ {Γ Δ} → (∀ {A}   → Γ ∋ A      → Δ ∋ A)
                → ∀ {A B} → Γ ,, B ∋ A → Δ ,, B ∋ A
exts f Z = Z
exts f (S x) = S f x

rename : ∀ {Γ Δ} → (∀ {A} → Γ ∋ A → Δ ∋ A) →
                    ∀ {A} → Γ ⊢ A → Δ ⊢ A
rename f (` x) = ` (f x)
rename f (`λ x) = `λ (rename (exts f) x)
rename f (g `$ y) = rename f g `$ rename f y
rename f `⟨ a , b ⟩ = `⟨ (rename f a) , (rename f b) ⟩
rename f (`π₁ x) = `π₁ (rename f x)
rename f (`π₂ x) = `π₂ (rename f x)
rename f `tt = `tt

extnd : ∀ {Γ Δ} → (∀ {A}   → Γ ∋ A      → Δ ⊢ A) →
                   ∀ {A B} → Γ ,, B ∋ A → Δ ,, B ⊢ A
extnd f Z = ` Z
extnd f (S x) = rename S_ (f x)

simsub : ∀ {Γ Δ} → (∀ {A} → Γ ∋ A → Δ ⊢ A) →
         ∀ {A} → Γ ⊢ A → Δ ⊢ A
simsub f (` x) = f x
simsub f (`λ x) = `λ (simsub (extnd f) x)
simsub f (a `$ b) = (simsub f a) `$ (simsub f b)
simsub f `⟨ a , b ⟩ = `⟨ (simsub f a) , (simsub f b) ⟩
simsub f (`π₁ x) = `π₁ (simsub f x)
simsub f (`π₂ x) = `π₂ (simsub f x)
simsub f `tt = `tt
```

Single substitution is handy.

```agda
_[_] : ∀ {Γ A B} →
       Γ ,, B ⊢ A →
       Γ ⊢ B →
       Γ ⊢ A
_[_] {Γ} {A} {B} x y = simsub {Γ ,, B} {Γ} f x
  where
    f : ∀ {A} → Γ ,, B ∋ A → Γ ⊢ A
    f Z = y
    f (S x) = ` x
```

That was pretty easy, aye? And we don't need to prove any additional
theorems, because they're built into the definition of substitution!

```agda
data is-value : ∀ {Γ A} → Γ ⊢ A → Type where
  v-λ : ∀ {Γ A B} {body : Γ ,, B ⊢ A} → is-value (`λ body)
  v-⟨,⟩ : ∀ {Γ A B} {a : Γ ⊢ A} {b : Γ ⊢ B} → is-value (`⟨ a , b ⟩)
  v-⊤ : ∀ {Γ} → is-value {Γ} `tt

infix 10 _↦_
data _↦_ : ∀ {Γ A} → Γ ⊢ A → Γ ⊢ A → Type where
     β-λ : ∀ {Γ A B} {f : Γ ,, A ⊢ B} {x : Γ ⊢ A} →
           is-value x →
           (`λ f) `$ x ↦ f [ x ]
     β-π₁ : ∀ {Γ A B} {a : Γ ⊢ A} {b : Γ ⊢ B} →
          `π₁ `⟨ a , b ⟩ ↦ a
     β-π₂ : ∀ {Γ A B} {a : Γ ⊢ A} {b : Γ ⊢ B} →
          `π₂ `⟨ a , b ⟩ ↦ b
     ξ-π₁ : ∀ {Γ A B} {a b : Γ ⊢ A `× B} →
           a ↦ b →
           `π₁ a ↦ `π₁ b
     ξ-π₂ : ∀ {Γ A B} {a b : Γ ⊢ A `× B} →
           a ↦ b →
           `π₂ a ↦ `π₂ b
     ξ-$ₗ : ∀ {Γ A B} {f g : Γ ⊢ A `⇒ B} {x : Γ ⊢ A} →
           f ↦ g →
           f `$ x ↦ g `$ x
     ξ-$ᵣ : ∀ {Γ A B} {f : Γ ⊢ A `⇒ B} {x y : Γ ⊢ A} →
           is-value f →
           x ↦ y →
           f `$ x ↦ f `$ y
```

Preservation is free! We can only construct well-typed terms,
so our reduction rules must inherently preserve types.

Values don't reduce.

```agda
value-¬reduce : ∀ {Γ A} {x y : Γ ⊢ A} → is-value x → ¬ (x ↦ y)
value-¬reduce v-λ ()
value-¬reduce v-⟨,⟩ ()
value-¬reduce v-⊤ ()
```

Progress.

```agda
data Progress {Γ A} (x : Γ ⊢ A) : Type where
     going : ∀ {y} → x ↦ y → Progress x
     done : is-value x → Progress x

progress : ∀ {A} (x : ∅ ⊢ A) → Progress x
progress {A} (`λ x) = done v-λ
progress {A} (f `$ x) with progress f
... | going f₁ = going (ξ-$ₗ f₁)
... | done f₁ with progress x
... | going x₁ = going (ξ-$ᵣ f₁ x₁)
... | done x₁ with f₁
... | v-λ = going (β-λ x₁)
progress {A} `⟨ x , x₁ ⟩ = done v-⟨,⟩
progress {A} (`π₁ x) with progress x
... | going x₁ = going (ξ-π₁ x₁)
... | done v-⟨,⟩ = going β-π₁
progress {A} (`π₂ x) with progress x
... | going x₁ = going (ξ-π₂ x₁)
... | done v-⟨,⟩ = going β-π₂
progress {A} `tt = done v-⊤
```

Reduction in any context is deterministic.

```agda
det : ∀ {Γ A} {x y z : Γ ⊢ A} →
        x ↦ y →
        x ↦ z →
        y ≡ z
det (β-λ x) (β-λ x₁) = refl
det (β-λ x) (ξ-$ᵣ x₁ ~z) = absurd (value-¬reduce x ~z)
det β-π₁ β-π₁ = refl
det β-π₂ β-π₂ = refl
det (ξ-π₁ ~y) (ξ-π₁ ~z) = ap `π₁ (det ~y ~z)
det (ξ-π₂ ~y) (ξ-π₂ ~z) = ap `π₂ (det ~y ~z)
det (ξ-$ₗ ~y) (ξ-$ₗ ~z) = ap₂ _`$_ (det ~y ~z) refl
det (ξ-$ₗ ~y) (ξ-$ᵣ x ~z) = absurd (value-¬reduce x ~y)
det (ξ-$ᵣ x ~y) (β-λ x₁) = absurd (value-¬reduce x₁ ~y)
det (ξ-$ᵣ x ~y) (ξ-$ₗ ~z) = absurd (value-¬reduce x ~z)
det (ξ-$ᵣ x ~y) (ξ-$ᵣ x₁ ~z) = ap₂ _`$_ refl (det ~y ~z)
```
