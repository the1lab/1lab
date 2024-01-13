<!--
```agda
open import Cat.Bi.Base

open import Cat.Functor.Bifunctor
open import Cat.Instances.Functor
open import Cat.Instances.EnrichedFunctor
open import Cat.Instances.EnrichedFunctor.Compose
open import Cat.Instances.Product
open import Cat.Prelude

open import Cat.Monoidal.Base
open import Cat.Enriched.Base

import Cat.Reasoning
import Cat.Enriched.Reasoning
```
-->

```agda
module Cat.Bi.Instances.EnrichedCats
  {ov ℓv} {V : Precategory ov ℓv}
  (V-monoidal : Monoidal-category V)
  where
```

<!--
```agda
open Prebicategory
private
  module V = Cat.Reasoning V

open Monoidal-category V-monoidal
open Enriched-functor
```
-->

# The bicategory of V-enriched categories

Let $\cV$ be a [[monoidal category]]. $\cV$-[[enriched categories]],
$\cV$-[[enriched functors]] and $\cV$-[[enriched natural transformations]]
assemble into a [[bicategory]].

```agda
Enriched-cats : ∀ o → Prebicategory (ov ⊔ ℓv ⊔ lsuc o) (ov ⊔ ℓv ⊔ o) (ov ⊔ ℓv ⊔ o ⊔ o)
Enriched-cats o = vcats where
  open make-natural-iso
```

Unfortunately, the unitors and associators are not quite in the form
we require, so some repackaging is required.

```agda
  ƛ : ∀ {A B : Enriched-precategory V-monoidal o}
    → Id ≅ⁿ (Right (Fv∘-functor A B B) Idv)

  ρ : ∀ {A B : Enriched-precategory V-monoidal o}
    → Id ≅ⁿ (Left (Fv∘-functor A A B) Idv)

  α : ∀ {A B C D : Enriched-precategory V-monoidal o}
    → _≅ⁿ_ {C = VCat[ C , D ] ×ᶜ VCat[ B , C ] ×ᶜ VCat[ A , B ]}
        (compose-assocˡ (λ {A} {B} {C} → Fv∘-functor A B C))
        (compose-assocʳ (λ {A} {B} {C} → Fv∘-functor A B C))
```

<details>
<summary>However, we omit the (tedious) details of the repackaging.
</summary>

```agda
  ƛ {B = B} = to-natural-iso ni where
    open Cat.Enriched.Reasoning B
    ni : make-natural-iso _ _
    ni .eta F = record
      { ηv = λ Γ x → idv
      ; is-naturalv = λ f → id-comm-symv
      ; ηv-natural = λ σ → idv-natural σ
      }
    ni .inv F = record
      { ηv = λ Γ x → idv
      ; is-naturalv = λ f → id-comm-symv
      ; ηv-natural = λ σ → idv-natural σ
      }
    ni .eta∘inv F = Enriched-nat-path λ Γ x → idlv _
    ni .inv∘eta F = Enriched-nat-path λ Γ x → idlv _
    ni .natural F G α = Enriched-nat-path λ Γ x →
      idrv _ ∙ id-commv

  ρ {B = B} = to-natural-iso ni where
    open Cat.Enriched.Reasoning B
    ni : make-natural-iso _ _
    ni .eta F = record
      { ηv = λ Γ x → idv
      ; is-naturalv = λ f → id-comm-symv
      ; ηv-natural = λ σ → idv-natural σ
      }
    ni .inv F = record
      { ηv = λ Γ x → idv
      ; is-naturalv = λ f → id-comm-symv
      ; ηv-natural = λ σ → idv-natural σ
      }
    ni .eta∘inv F = Enriched-nat-path λ Γ x → idlv _
    ni .inv∘eta F = Enriched-nat-path λ Γ x → idlv _
    ni .natural F G α = Enriched-nat-path λ Γ x →
      idrv _ ∙ ap (_∘v _) (G .Fv-id)

  α {D = D} = to-natural-iso ni where
    open Cat.Enriched.Reasoning D
    ni : make-natural-iso _ _
    ni .eta F = record
      { ηv = λ Γ x → idv
      ; is-naturalv = λ f → id-comm-symv
      ; ηv-natural = λ σ → idv-natural σ
      }
    ni .inv F = record
      { ηv = λ Γ x → idv
      ; is-naturalv = λ f → id-comm-symv
      ; ηv-natural = λ σ → idv-natural σ
      }
    ni .eta∘inv F = Enriched-nat-path λ Γ x → idlv _
    ni .inv∘eta F = Enriched-nat-path λ Γ x → idlv _
    ni .natural (F , G , H) (J , K , L) α = Enriched-nat-path λ Γ x →
      idrv _ ·· pushlv (J .Fv-∘ _ _) ·· sym (idlv _)
```
</details>

Luckily, the rest of the construction is straightforward.

```agda
  vcats : Prebicategory _ _ _
  vcats .Ob = Enriched-precategory V-monoidal o
  vcats .Hom C D = VCat[ C , D ]
  vcats .id = Idv
  vcats .compose = Fv∘-functor _ _ _
  vcats .unitor-l = ƛ
  vcats .unitor-r = ρ
  vcats .associator = α
  vcats .triangle {C = C} F G = Enriched-nat-path λ Γ x → idrv _
    where open Cat.Enriched.Reasoning C
  vcats .pentagon {E = E} F G H J = Enriched-nat-path λ Γ x →
    ap₂ _∘v_
      (elimlv (ap (F .Fv₁ ⊙ G .Fv₁) (H .Fv-id) ·· ap (F .Fv₁) (G .Fv-id) ·· F .Fv-id))
      (elimrv (elimlv (F .Fv-id)))
    where open Cat.Enriched.Reasoning E
```
