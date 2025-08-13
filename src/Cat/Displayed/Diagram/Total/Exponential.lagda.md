<!--
```agda
open import Cat.Displayed.Diagram.Total.Terminal
open import Cat.Displayed.Diagram.Total.Product
open import Cat.Diagram.Exponential
open import Cat.Displayed.Base
open import Cat.Cartesian
open import Cat.Prelude

import Cat.Displayed.Reasoning
```
-->

```agda
module Cat.Displayed.Diagram.Total.Exponential
  {o ℓ o' ℓ'} {B : Precategory o ℓ} (E : Displayed B o' ℓ')
  {bcart : Cartesian-category B} (ecart : Cartesian-over E bcart)
  where
```

<!--
```agda
open Cat.Displayed.Reasoning E
open Cartesian-category bcart
open Cartesian-over ecart
```
-->

# Total exponential objects {defines="total-exponential-object"}

```agda
module
  _ {A B B^A : Ob} {ev : Hom (B^A ⊗₀ A) B}
    (exp : is-exponential _ bcart B^A ev)
    {A' : E ʻ A} {B' : E ʻ B} (B^A' : E ʻ B^A)
  where

  record is-exponential-over (ev' : Hom[ ev ] (B^A' ⊗₀' A') B') : Type (o ⊔ ℓ ⊔ o' ⊔ ℓ') where
    open is-exponential exp

    field
      ƛ'
        : ∀ {Γ Γ'} {m : Hom (Γ ⊗₀ A) B} (m' : Hom[ m ] (Γ' ⊗₀' A') B')
        → Hom[ ƛ m ] Γ' B^A'

      commutes'
        : ∀ {Γ Γ'} {m : Hom (Γ ⊗₀ A) B} (m' : Hom[ m ] (Γ' ⊗₀' A') B')
        → ev' ∘' ⟨ ƛ' m' ∘' π₁' , id' ∘' π₂' ⟩' ≡[ commutes m ] m'

      unique'
        : ∀ {Γ Γ'} {m : Hom (Γ ⊗₀ _) _} {n}
        → {p : ev ∘ (n ⊗₁ id) ≡ m}
        → {m' : Hom[ m ] (Γ' ⊗₀' _) _} (n' : Hom[ n ] Γ' _)
        → ev' ∘' ⟨ n' ∘' π₁' , id' ∘' π₂' ⟩' ≡[ p ] m'
        → n' ≡[ unique n p ] ƛ' m'

module _ {A B : Ob} (exp : Exponential _ bcart A B) where
  open Exponential exp

  record ExponentialP (A' : E ʻ A) (B' : E ʻ B) : Type (o ⊔ ℓ ⊔ o' ⊔ ℓ') where
    no-eta-equality
    field
      B^A'                : E ʻ B^A
      ev'                 : Hom[ ev ] (B^A' ⊗₀' A') B'
      has-is-exponential' : is-exponential-over has-is-exp B^A' ev'

    open is-exponential-over has-is-exponential' public

Cartesian-closed-over : Cartesian-closed B bcart → Type _
Cartesian-closed-over cc =
  let open Cartesian-closed cc
   in ∀ {A B} (A' : E ʻ A) (B' : E ʻ B) → ExponentialP (has-exp A B) A' B'

module Cartesian-closed-over {cc : Cartesian-closed B bcart} (cco : Cartesian-closed-over cc) where
  module _ {a b : Ob} (a' : E ʻ a) (b' : E ʻ b) where open ExponentialP (cco a' b') renaming (B^A' to [_,_]') using () public
  module _ {a b : Ob} {a' : E ʻ a} {b' : E ʻ b} where open ExponentialP (cco a' b') renaming (unique' to ƛ'-unique) hiding (B^A') public
```
