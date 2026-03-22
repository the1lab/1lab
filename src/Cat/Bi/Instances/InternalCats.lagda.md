<!--
```agda
open import Cat.Instances.InternalFunctor.Compose
open import Cat.Instances.InternalFunctor
open import Cat.Functor.Bifunctor
open import Cat.Instances.Functor
open import Cat.Instances.Product
open import Cat.Functor.Closed
open import Cat.Bi.Base
open import Cat.Prelude

import Cat.Internal.Reasoning
import Cat.Internal.Base
import Cat.Reasoning
```
-->

```agda
module Cat.Bi.Instances.InternalCats
  {o ℓ} (C : Precategory o ℓ)
  where
```

<!--
```agda
open Cat.Reasoning C
open Cat.Internal.Base C
open Prebicategory
open Internal-functor
open _=>i_
```
-->

# The bicategory of internal categories

Let $\cC$ be some category. The collection of [internal categories] in
$\cC$ forms a [[bicategory]], with internal functors as 1-cells, and
internal natural transformations as 2-cells.

[internal categories]: Cat.Internal.Base.html

```agda
Internal-cats : Prebicategory (o ⊔ ℓ) (o ⊔ ℓ) (o ⊔ ℓ)
Internal-cats = icats where
  open make-natural-iso
```

We have already shown that [internal functors] form a precategory, so
all that remains is to construct the unitors and the associator. These
are *almost* identity 2-cells, as internal functor composition is
pointwise strictly unital and associative. Unfortunately, this does not
extend to internal functor composition _as a whole_, so we cannot use
the identity internal natural isomorphism as-is.

[internal functors]: Cat.Instances.InternalFunctor.html

```agda
  ƛ : ∀ {A B : Internal-cat}
    → Id ≅ⁿ Bifunctor.Right (Fi∘-functor A B B) Idi
  ƛ {B = B} = to-natural-iso ni where
    open Cat.Internal.Reasoning B
    ni : make-natural-iso _ _
    ni .make-natural-iso.eta F = record
      { ηi          = λ x     → idi _
      ; is-naturali = λ x y f → id-comm-symi
      ; ηi-nat      = λ x σ   → casti $ idi-nat σ ∙i ap idi (F .Fi₀-nat x σ)
      }
    ni .make-natural-iso.inv F = record
      { ηi          = λ x     → idi _
      ; is-naturali = λ x y f → id-comm-symi
      ; ηi-nat      = λ x σ   → casti $ idi-nat σ ∙i ap idi (F .Fi₀-nat x σ)
      }
    ni .make-natural-iso.eta∘inv F = Internal-nat-path λ x → idli _
    ni .make-natural-iso.inv∘eta F = Internal-nat-path λ x → idli _
    ni .make-natural-iso.natural F G α = Internal-nat-path λ x → id-commi

  ρ : ∀ {A B : Internal-cat}
    → Id ≅ⁿ Bifunctor.Left (Fi∘-functor A A B) Idi
  ρ {B = B} = to-natural-iso ni where
    open Cat.Internal.Reasoning B
    ni : make-natural-iso _ _
    ni .make-natural-iso.eta F = record
      { ηi          = λ x     → idi _
      ; is-naturali = λ x y f → id-comm-symi
      ; ηi-nat      = λ x σ   → casti $ idi-nat σ ∙i ap idi (F .Fi₀-nat x σ)
      }
    ni .make-natural-iso.inv F = record
      { ηi          = λ x     → idi _
      ; is-naturali = λ x y f → id-comm-symi
      ; ηi-nat      = λ x σ   → casti $ idi-nat σ ∙i ap idi (F .Fi₀-nat x σ)
      }
    ni .make-natural-iso.eta∘inv F = Internal-nat-path λ x → idli _
    ni .make-natural-iso.inv∘eta F = Internal-nat-path λ x → idli _
    ni .make-natural-iso.natural F G α = Internal-nat-path λ x → id-commi

  α : {A B C D : Internal-cat}
    → _≅ⁿ_
       {C = Internal-functors _ C D ×ᶜ Internal-functors _ B C ×ᶜ Internal-functors _ A B}
       (compose-assocˡ (Internal-functors _) λ {A} {B} {C} → Fi∘-functor A B C)
       (compose-assocʳ (Internal-functors _) λ {A} {B} {C} → Fi∘-functor A B C)
  α {C = C} {D = D} = to-natural-iso ni where
    open Cat.Internal.Reasoning D
    module C = Cat.Internal.Reasoning C
    ni : make-natural-iso _ _
    ni .eta (F , G , H) .ηi x = idi _
    ni .eta (F , G , H) .is-naturali _ _ _ = id-comm-symi
    ni .eta (F , G , H) .ηi-nat x σ = casti $
      idi-nat σ
      ∙i ap idi
        (F .Fi₀-nat _ σ
         ∙ ap (F .Fi₀) (G .Fi₀-nat _ σ ∙ ap (G .Fi₀) (H .Fi₀-nat _ σ)))
    ni .inv (F , G , H) .ηi x = idi _
    ni .inv (F , G , H) .is-naturali _ _ _ = id-comm-symi
    ni .inv (F , G , H) .ηi-nat x σ = casti $
      idi-nat σ
      ∙i ap idi
        (F .Fi₀-nat _ σ
         ∙ ap (F .Fi₀) (G .Fi₀-nat _ σ ∙ ap (G .Fi₀) (H .Fi₀-nat _ σ)))
    ni .eta∘inv _ = Internal-nat-path λ x → idli _
    ni .inv∘eta _ = Internal-nat-path λ x → idli _
    ni .natural (F , G , H) (J , K , L) α = Internal-nat-path λ x → idri _ ∙ pushri (F .Fi-∘ _ _) ∙ introli refl
```

Once we've got that tedium out of the way, the rest of the construction
is a breeze.

```agda
  icats : Prebicategory _ _ _
  icats .Ob = Internal-cat
  icats .Hom 𝔸 𝔹 = Internal-functors C 𝔸 𝔹
  icats .id = Idi
  icats .compose = Fi∘-functor _ _ _
  icats .unitor-l = ƛ
  icats .unitor-r = ρ
  icats .associator = α
  icats .triangle {C = C} F G = Internal-nat-path λ x → idri _ ∙ sym (F .Fi-id)
    where open Cat.Internal.Reasoning C
  icats .pentagon {E = E} F G H J = Internal-nat-path λ x → ap₂ _∘i_ refl (elimri (F .Fi-id))
    where open Cat.Internal.Reasoning E
```
