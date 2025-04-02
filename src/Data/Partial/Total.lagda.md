<!--
```agda
open import 1Lab.Prelude

open import Data.Partial.Base
open import Data.Nat.Base
open import Data.Power using (ℙ)
```
-->

```agda
module Data.Partial.Total where
```

```agda
private variable
  ℓ ℓ' ℓ'' : Level
  A B C X Y : Type ℓ
```

# Total partial elements

```agda
↯⁺ : Type ℓ → Type ℓ
↯⁺ A = Σ[ a ∈ ↯ A ] ⌞ a ⌟
```

<!--
```agda
instance
  fat-to-part : To-part (↯⁺ A) A
  fat-to-part = record { to-part = fst }

  ↯⁺-Map : Map (eff ↯⁺)
  ↯⁺-Map .Map.map f (x , hx) = part-map f x , hx

  ↯⁺-Idiom : Idiom (eff ↯⁺)
  ↯⁺-Idiom .Idiom.Map-idiom = ↯⁺-Map
  ↯⁺-Idiom .Idiom.pure x    = always x , tt
  ↯⁺-Idiom .Idiom._<*>_ (f , hf) (x , hx) = part-ap f x , hf , hx

  Extensional-↯⁺ : ⦃ _ : Extensional (↯ A) ℓ ⦄ → Extensional (↯⁺ A) ℓ
  Extensional-↯⁺ ⦃ e ⦄ = embedding→extensional (fst , Subset-proj-embedding (λ _ → hlevel 1)) e

  abstract
    H-Level-↯⁺ : ∀ {A : Type ℓ} {n} ⦃ _ : 2 ≤ n ⦄ ⦃ _ : H-Level A n ⦄ → H-Level (↯⁺ A) n
    H-Level-↯⁺ {n = suc (suc n)} ⦃ s≤s (s≤s p) ⦄ = hlevel-instance $
      embedding→is-hlevel (1 + n) (Subset-proj-embedding λ _ → hlevel 1) (hlevel (2 + n))

    {-# OVERLAPPING H-Level-↯⁺ #-}
```
-->

```agda
from-total : ↯⁺ A → A
from-total (a , ha) = a .elt ha

from-total-is-equiv : is-equiv (from-total {A = A})
from-total-is-equiv = is-iso→is-equiv (iso pure (λ _ → refl) λ (x , a) → Σ-prop-path! (sym (is-always x a)))
```

```agda
record ℙ⁺ (A : Type ℓ) : Type ℓ where
  field
    mem     : ↯ A → Ω
    defined : ∀ {a} → ⌞ mem a ⌟ → ⌞ a ⌟
```

<!--
```agda
private unquoteDecl eqv = declare-record-iso eqv (quote ℙ⁺)
open ℙ⁺ public
open is-iso

instance
  Membership-ℙ⁺ : ⦃ _ : To-part X A ⦄ → Membership X (ℙ⁺ A) _
  Membership-ℙ⁺ = record { _∈_ = λ a p → ⌞ p .mem (to-part a) ⌟ } where open To-part ⦃ ... ⦄

  Extensional-ℙ⁺ : ∀ {ℓr} ⦃ _ : Extensional (↯ A → Ω) ℓr ⦄ → Extensional (ℙ⁺ A) ℓr
  Extensional-ℙ⁺ ⦃ e ⦄ = injection→extensional! (λ p → Iso.injective eqv (Σ-prop-path! p)) e

  H-Level-ℙ⁺ : ∀ {n} → H-Level (ℙ⁺ A) (2 + n)
  H-Level-ℙ⁺ = basic-instance 2 (Iso→is-hlevel 2 eqv (hlevel 2))
```
-->

```agda
from-total-predicate : ℙ A → ℙ⁺ A
from-total-predicate P .mem x = el (Σ[ hx ∈ x ] x .elt hx ∈ P) (hlevel 1)
from-total-predicate P .defined (hx , _) = hx

from-total-predicate-is-equiv : is-equiv (from-total-predicate {A = A})
from-total-predicate-is-equiv = is-iso→is-equiv λ where
  .inv P a → P .mem (always a)
  .rinv P → ext λ a → Ω-ua (rec! (λ ha → subst (_∈ P) (sym (is-always a ha)))) λ pa → P .defined pa , subst (_∈ P) (is-always a _) pa
  .linv P → ext λ a → Ω-ua snd (tt ,_)
```
