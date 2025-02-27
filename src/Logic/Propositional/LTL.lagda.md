---
description: |
  Propositional linear temporal logic.
---
<!--
```agda
{-# OPTIONS --show-implicit -vtc.instance.overlap:60 -vtc.instance.sort:40 #-}
open import 1Lab.Prelude hiding (⟦_⟧)

open import Data.Bool
open import Data.Fin using (Fin; zero; suc; fzero; fsuc; weaken; inject; _[_≔_] ; fin-view)
open import Data.Nat
open import Data.Nat.Properties
open import Data.Sum

open import Order.Instances.Pointwise
open import Order.Base
```
-->
```agda
module Logic.Propositional.LTL where
```

# Propositional linear temporal logic

```agda
data LTL (Γ : Nat) : Type where
  atom        : Fin Γ → LTL Γ
  “⊤” “⊥”     : LTL Γ
  _“∧”_ _“∨”_ : LTL Γ → LTL Γ → LTL Γ
  _“⇒”_       : LTL Γ → LTL Γ → LTL Γ
  “○”_        : LTL Γ → LTL Γ
  _“U”_       : LTL Γ → LTL Γ → LTL Γ
  _“R”_       : LTL Γ → LTL Γ → LTL Γ
```

<!--
```agda
private variable
  Γ Δ : Nat
  φ ψ : LTL Γ
```
-->

```agda
“⋄”_ : ∀ {Γ} → LTL Γ → LTL Γ
“⋄” P = “⊤” “U” P

“□”_ : ∀ {Γ} → LTL Γ → LTL Γ
“□” P = “⊥” “R” P
```

## Semantics

```agda
module Semantics {o ℓ} (World : Poset o ℓ) (step : ⌞ World ⌟ → ⌞ World ⌟) where

  private
    stepⁿ : Nat → ⌞ World ⌟ → ⌞ World ⌟
    stepⁿ n w = iter n step w

  opaque
    _⊨_ : ∀ {Γ} → Monotone World (Subsets (Fin Γ)) × ⌞ World ⌟ → LTL Γ → Ω
    (ρ , w) ⊨ atom x = ρ .hom w x
    (ρ , w) ⊨ “⊤” = ⊤Ω
    (ρ , w) ⊨ “⊥” = ⊥Ω
    (ρ , w) ⊨ (φ “∧” ψ) = (ρ , w) ⊨ φ ∧Ω (ρ , w) ⊨ ψ
    (ρ , w) ⊨ (φ “∨” ψ) = (ρ , w) ⊨ φ ∨Ω (ρ , w) ⊨ ψ
    (ρ , w) ⊨ (φ “⇒” ψ) = (ρ , w) ⊨ φ →Ω (ρ , w) ⊨ ψ
    (ρ , w) ⊨ (“○” φ) =
      (ρ , step w) ⊨ φ
    ((ρ , w) ⊨ (φ “U” ψ)) .∣_∣ =
      ∃[ k ∈ Nat ] ∣ (ρ , stepⁿ k w) ⊨ ψ ∣ × (∀ (i : Nat) → i < k → ∣ (ρ , stepⁿ i w) ⊨ φ ∣)
    ((ρ , w) ⊨ (φ “U” ψ)) .is-tr = hlevel 1
    ((ρ , w) ⊨ (φ “R” ψ)) .∣_∣ =
      ∀ (k : Nat) → ∥ ∣ (ρ , stepⁿ k w) ⊨ ψ ∣ ⊎ (∃[ i ∈ Nat ] i < k × ∣ (ρ , stepⁿ i w) ⊨ φ ∣) ∥
    ((ρ , w) ⊨ (φ “R” ψ)) .is-tr = hlevel 1
```

<!--
```agda
  private variable
    ρ : Monotone World (Subsets (Fin Γ))
    w : ⌞ World ⌟

  opaque
    unfolding _⊨_
    atom-sem : ∀ {x} → ∣ (ρ , w) ⊨ atom x ∣ ↔ ∣ ρ .hom w x ∣
    atom-sem = id↔

    ⊤-sem : ∣ (ρ , w) ⊨ “⊤” ∣ ↔ ⊤
    ⊤-sem = id↔

    ⊥-sem : ∣ (ρ , w) ⊨ “⊥” ∣ ↔ ⊥
    ⊥-sem = id↔

    ∧-sem : ∣ (ρ , w) ⊨ (φ “∧” ψ) ∣ ↔ (∣ (ρ , w) ⊨ φ ∣ × ∣ (ρ , w) ⊨ ψ ∣)
    ∧-sem = id↔

    ∨-sem : ∣ (ρ , w) ⊨ (φ “∨” ψ) ∣ ↔ ∥ ∣ (ρ , w) ⊨ φ ∣ ⊎ ∣ (ρ , w) ⊨ ψ ∣ ∥
    ∨-sem = id↔

    ⇒-sem : ∣ (ρ , w) ⊨ (φ “⇒” ψ) ∣ ↔ (∣ (ρ , w) ⊨ φ ∣ → ∣ (ρ , w) ⊨ ψ ∣)
    ⇒-sem = id↔

    ○-sem : ∣ (ρ , w) ⊨ (“○” φ) ∣ ↔ ∣ (ρ , step w) ⊨ φ ∣
    ○-sem = id↔

    U-sem : ∣ (ρ , w) ⊨ (φ “U” ψ) ∣ ↔ (∃[ k ∈ Nat ] ∣ (ρ , stepⁿ k w) ⊨ ψ ∣ × (∀ (i : Nat) → i < k → ∣ (ρ , stepⁿ i w) ⊨ φ ∣))
    U-sem = id↔

    R-sem : ∣ (ρ , w) ⊨ (φ “R” ψ) ∣ ↔ (∀ (k : Nat) → ∥ ∣ (ρ , stepⁿ k w) ⊨ ψ ∣ ⊎ (∃[ i ∈ Nat ] i < k × ∣ (ρ , stepⁿ i w) ⊨ φ ∣) ∥)
    R-sem = id↔
```
-->

```agda
  record Semantics (φ : LTL Γ) : Typeω where
    constructor semantics
    no-eta-equality
    field
      {lvl} : Level
      Sem : Monotone World (Subsets (Fin Γ)) → ⌞ World ⌟ → Type lvl
      Sem-is-prop : ∀ {ρ w} → is-prop (Sem ρ w)
      sem : ∀ {ρ w} → ∣ (ρ , w) ⊨ φ ∣ ↔ Sem ρ w


  Sem
    : (φ : LTL Γ)
    → ⦃ _ : Semantics φ ⦄
    → Monotone World (Subsets (Fin Γ)) → ⌞ World ⌟ → Type _
  Sem φ ⦃ e ⦄ = Semantics.Sem e


  sem
    : (φ : LTL Γ)
    → ⦃ _ : Semantics φ ⦄
    → ∀ {ρ w} → ∣ (ρ , w) ⊨ φ ∣ ↔ Sem φ ρ w
  sem φ ⦃ s ⦄ = Semantics.sem s

  intro
    : (φ : LTL Γ)
    → ⦃ _ : Semantics φ ⦄
    → ∀ {ρ w} → Sem φ ρ w → ∣ (ρ , w) ⊨ φ ∣
  intro φ ⦃ s ⦄ = _↔_.from (Semantics.sem s)

  elim
    : (φ : LTL Γ)
    → ⦃ _ : Semantics φ ⦄
    → ∀ {ρ w} → ∣ (ρ , w) ⊨ φ ∣ → Sem φ ρ w
  elim φ ⦃ s ⦄ = _↔_.to (Semantics.sem s)
```


<!--
```agda
  instance
    Semantics-Default : Semantics φ
    Semantics-Default {φ = φ} =
      semantics (λ ρ w → ∣ (ρ , w) ⊨ φ ∣) (hlevel 1) id↔
    {-# INCOHERENT Semantics-Default #-}
--       -- Semantics-atom
--       --   : ∀ {x : Fin Γ}
--       --   → Semantics (λ ρ w → apply ρ w x) (atom x)
--       -- Semantics-atom {x = x} = entails (λ pf → pf) (λ pf → pf)

--       -- Semantics-⊤
--       --   : Semantics {Γ = Γ} (λ _ _ → ⊤Ω) “⊤”
--       -- Semantics-⊤ = entails (λ pf → pf) (λ pf → pf)

    Semantics-⊥ : Semantics {Γ = Γ} “⊥”
    Semantics-⊥ = semantics (λ _ _ → ⊥) (hlevel 1) ⊥-sem
--       -- (λ pf → pf) (λ pf → pf)

--       -- Semantics-∧
--       --   : ⦃ _ : Semantics ⟦φ⟧ φ ⦄ ⦃ _ : Semantics ⟦ψ⟧ ψ ⦄
--       --   → Semantics (λ ρ w → ⟦φ⟧ ρ w ∧Ω ⟦ψ⟧ ρ w) (φ “∧” ψ)
--       -- Semantics-∧ {φ = φ} {ψ = ψ} =
--       --   entails
--       --     (×-map (intro {φ = φ}) (intro {φ = ψ}))
--       --     (×-map (elim {φ = φ}) (elim {φ = ψ}))

--   --     Semantics-∨
--   --       : ⦃ _ : Semantics φ ⦄ ⦃ _ : Semantics ψ ⦄
--   --       → Semantics (φ “∨” ψ)
--   --     Semantics-∨ {φ = φ} {ψ = ψ} =
--   --       entails (λ ρ w → ∥ Sem φ ρ w ⊎ Sem ψ ρ w ∥)
--   --         (∥-∥-map (⊎-map (intro {φ = φ}) (intro {φ = ψ})))
--   --         (∥-∥-map (⊎-map (elim {φ = φ}) (elim {φ = ψ})))

--   --     Semantics-⇒
--   --       : ⦃ _ : Semantics φ ⦄ ⦃ _ : Semantics ψ ⦄
--   --       → Semantics (φ “⇒” ψ)
--   --     Semantics-⇒ {φ = φ} {ψ = ψ} =
--   --       entails (λ ρ w → Sem φ ρ w → Sem ψ ρ w)
--   --         (λ k p → intro {φ = ψ} (k (elim {φ = φ} p)))
--   --         (λ k p → elim {φ = ψ} (k (intro {φ = φ} p)))

--   --     Semantics-U
--   --       : ⦃ _ : Semantics φ ⦄ ⦃ _ : Semantics ψ ⦄
--   --       → Semantics (φ “U” ψ)
--   --     Semantics-U {φ = φ} {ψ = ψ} =
--   --       entails (λ ρ w → ∃[ k ∈ Nat ] Sem ψ ρ (stepⁿ k w) × (∀ (i : Nat) → i < k → Sem φ ρ (stepⁿ i w)))
--   --         (rec! (λ k psi phi → inc (k , intro {φ = ψ} psi , λ i i<k → intro {φ = φ} (phi i i<k))))
--   --         (rec! (λ k psi phi → inc (k , elim {φ = ψ} psi , λ i i<k → elim {φ = φ} (phi i i<k))))

    Semantics-R : ∀ {Γ} {φ ψ : LTL Γ} ⦃ _ : Semantics φ ⦄ ⦃ _ : Semantics ψ ⦄ → Semantics (φ “R” ψ)
    Semantics-R {φ = φ} {ψ = ψ} .Semantics.lvl = _
    Semantics-R {φ = φ} {ψ = ψ} .Semantics.Sem ρ w =
      ∀ (k : Nat) → ∥ Sem ψ ρ (stepⁿ k w) ⊎ (∃[ i ∈ Nat ] i < k × Sem φ ρ (stepⁿ i w)) ∥
    Semantics-R {φ = φ} {ψ = ψ} .Semantics.Sem-is-prop = hlevel 1
    Semantics-R {φ = φ} {ψ = ψ} .Semantics.sem = R-sem ∙↔ Π-cod↔ (λ k → ∥-∥-↔ (⊎-↔ (sem ψ) (∥-∥-↔ (Σ-↔₂ λ _ → Σ-↔₂ λ _ → sem φ))))
      -- semantics (λ ρ w → (∀ (k : Nat) → ∥ Sem ψ ρ (stepⁿ k w) ⊎ (∃[ i ∈ Nat ] i < k × Sem φ ρ (stepⁿ i w)) ∥))
      --   (hlevel 1)
      --   (R-sem ∙↔ Π-cod↔ (λ k → ∥-∥-↔ (⊎-↔ (sem ψ) (∥-∥-↔ (Σ-↔₂ λ _ → Σ-↔₂ λ _ → sem φ)))))
```
-->

```agda
  □-sem : ∣ (ρ , w) ⊨ (“□” φ) ∣ ↔ (∀ k → ∣ (ρ , stepⁿ k w) ⊨ φ ∣)
  □-sem {φ = φ} =
    sem (“⊥” “R” φ)
    ∙↔ Π-cod↔ (λ k → biimp (rec! (id , λ i i<k → tt)) (λ phi → inc (inl phi)))

  instance
    Semantics-□ : ∀ {Γ} {φ : LTL Γ} ⦃ _ : Semantics φ ⦄ → Semantics (“⊥” “R” φ)
    Semantics-□ {φ = φ} .Semantics.lvl = _
    Semantics-□ {φ = φ} .Semantics.Sem ρ w = (k : Nat) → Sem φ ρ (stepⁿ k w)
    Semantics-□ {φ = φ} .Semantics.Sem-is-prop = {!!}
    Semantics-□ {φ = φ} .Semantics.sem = □-sem ∙↔ Π-cod↔ (λ k → sem φ)
      -- semantics (λ ρ w → (k : Nat) → Sem φ ρ (stepⁿ k w))
      --   (Π-is-hlevel 1 λ _ → {!!})
      --   (□-sem ∙↔ Π-cod↔ (λ k → sem φ))
    {-# OVERLAPPING Semantics-□ #-}
    {-# OVERLAPPABLE Semantics-R #-}
-- --       entails (λ ρ w → (k : Nat) → Sem φ ρ (stepⁿ k w))
-- --         {!!}
-- --         {!!}
-- --         {!!}
-- --     --  entails (Π-is-hlevel 1 λ _ → Sem-is-prop)
-- --     --    (λ pf → intro ⦃ Semantics-R ⦄ λ k → inc (inl (pf k)))
-- --     --    (λ pf k → ∥-∥-rec Sem-is-prop [ id , (λ (i , i<k , ff) → absurd ff) ] (elim ⦃ Semantics-R ⦄ pf k))
```

```agda
  □-counit : ∣ (ρ , w) ⊨ (“□” φ) ∣ → ∣ (ρ , w) ⊨ φ ∣
  □-counit {ρ = ρ} {w = w} {φ = φ} □phi = _↔_.to (sem (“□” φ)) □phi 0

--   -- □-comult : ∣ (ρ , w) ⊨ (“□” φ) ∣ → ∣ (ρ , w) ⊨ (“□” “□” φ) ∣
--   -- □-comult {ρ = ρ} {w = w} {φ = φ} □phi =
--   --   intro λ k k' →
--   --     subst (λ w → ∣ (ρ , w) ⊨ φ ∣)
--   --       (ap (λ k → iter k step w) (+-commutative k k') ∙ iter-+ k' k step w)
--   --       (elim □phi (k + k'))
-- ```
