<!--
```agda
open import 1Lab.Prelude

open import Data.Partial.Total
open import Data.Partial.Base
open import Data.Fin.Base hiding (_<_ ; _≤_)
open import Data.Nat.Base
open import Data.Vec.Base
open import Data.Irr

open import Realisability.PCA
```
-->

```agda
module Realisability.PCA.Sugar
```

<!--
```agda
  {ℓ} {A : Type ℓ} {_%_ : ↯ A → ↯ A → ↯ A} (p : is-pca _%_)
  where

private variable
  ℓ' ℓ'' : Level
```
-->

# Sugar for programming in PCAs

```agda
_⋆_ : ∀ {X : Type ℓ'} {Y : Type ℓ''} ⦃ _ : To-part X A ⦄ ⦃ _ : To-part Y A ⦄ → X → Y → ↯ A
f ⋆ x = to-part f % to-part x where open To-part ⦃ ... ⦄
```

```agda
open is-pca p public

data Termʰ (V : Type) : Type ℓ where
  var   : V → Termʰ V
  const : ↯⁺ A → Termʰ V
  app   : Termʰ V → Termʰ V → Termʰ V
  lam   : (V → Termʰ V) → Termʰ V

private
  wf : Nat → Termʰ Nat → Type
  wf Γ (var k)   = Γ - suc k < Γ
  wf Γ (const a) = ⊤
  wf Γ (app f x) = wf Γ f × wf Γ x
  wf Γ (lam b)   = wf (suc Γ) (b Γ)

  from-wf : ∀ {n} (t : Termʰ Nat) → wf n t → Term A n
  from-wf {n} (var x) w       = var (fin (n - suc x) ⦃ forget w ⦄)
  from-wf (const x)   w       = const x
  from-wf (app f x) (wf , wx) = app (from-wf f wf) (from-wf x wx)
  from-wf {n = n} (lam f) w   = abs (from-wf (f n) w)

  always-denotes : ∀ {V} → Termʰ V → Type
  always-denotes (var x)   = ⊥
  always-denotes (const x) = ⊤
  always-denotes (app f x) = ⊥
  always-denotes (lam x)   = ⊤

expr_ : (t : ∀ {V} → Termʰ V) ⦃ _ : wf 0 t ⦄ → ↯ A
expr_ t ⦃ i ⦄ = eval {n = 0} (from-wf t i) []

val_ : (t : ∀ {V} → Termʰ V) ⦃ _ : wf 0 t ⦄ ⦃ _ : always-denotes {Nat} t ⦄ → ↯⁺ A
val_ t ⦃ i ⦄ = eval {n = 0} (from-wf t i) [] , d t where abstract
  d : (t : Termʰ Nat) ⦃ i : wf 0 t ⦄ ⦃ _ : always-denotes t ⦄ → ⌞ eval {n = 0} (from-wf t i) [] ⌟
  d (const x) = x .snd
  d (lam x) = abs↓ (from-wf (x 0) _) []
```

```agda
record To-term {ℓ'} (V : Type) (X : Type ℓ') : Type (ℓ ⊔ ℓ') where
  field to : X → Termʰ V

instance
  var-to-term : ∀ {V} → To-term V V
  var-to-term = record { to = var }

  const-to-term' : ∀ {V} → To-term V A
  const-to-term' = record { to = λ x → const (pure x , tt) }

  const-to-term : ∀ {V} → To-term V (↯⁺ A)
  const-to-term = record { to = const }

  term-to-term : ∀ {V} → To-term V (Termʰ V)
  term-to-term = record { to = λ x → x }

_`·_
  : ∀ {ℓ' ℓ''} {V : Type} {A : Type ℓ'} {B : Type ℓ''} ⦃ _ : To-term V A ⦄ ⦃ _ : To-term V B ⦄
  → A → B → Termʰ V
f `· x = app (to f) (to x) where open To-term ⦃ ... ⦄

lam-syntax : ∀ {ℓ} {V : Type} {A : Type ℓ} ⦃ _ : To-term V A ⦄ → (V → A) → Termʰ V
lam-syntax f = lam λ x → to (f x) where open To-term ⦃ ... ⦄

syntax lam-syntax (λ x → e) = ⟨ x ⟩ e

infixl 25 _`·_
infixl 35 _⋆_
```
