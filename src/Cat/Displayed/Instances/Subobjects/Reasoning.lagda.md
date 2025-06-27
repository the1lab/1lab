<!--
```agda
open import Cat.Diagram.Pullback.Properties
open import Cat.Diagram.Pullback.Along
open import Cat.Displayed.Cartesian
open import Cat.Diagram.Pullback
open import Cat.Diagram.Product
open import Cat.Prelude

import Cat.Displayed.Instances.Subobjects as Subobj
import Cat.Displayed.Cartesian.Indexing
import Cat.Reasoning as Cat
```
-->

```agda
module Cat.Displayed.Instances.Subobjects.Reasoning
  {o ℓ} {C : Precategory o ℓ} (pb : has-pullbacks C) where
```

<!--
```agda
open is-pullback-along
open Subobj C public
open Pullback
open Cat C

private
  module Ix = Cat.Displayed.Cartesian.Indexing Subobjects (with-pullbacks.Subobject-fibration pb)
  variable
    X Y Z : Ob
    f g h : Hom X Y
    l m n : Subobject X

open Sub
  renaming (_≅_ to _≅ₘ_)
  using ()
  public

≅ₘ→iso : m ≅ₘ n → m .domain ≅ n .domain
≅ₘ→iso p .to = p .Sub.to .map
≅ₘ→iso p .from = p .Sub.from .map
≅ₘ→iso p .inverses = record
  { invl = ap ≤-over.map (p .Sub.invl)
  ; invr = ap ≤-over.map (p .Sub.invr)
  }
```
-->

# Subobjects in a cartesian category

```agda
open with-pullbacks pb renaming (pullback-subobject to infixr 35 _^*_) public
```

```agda
^*-univ : ≤-over f m n → m ≤ₘ f ^* n
^*-univ = Cartesian-lift.universalv (Subobject-fibration _ _)

^*-id : id ^* m ≅ₘ m
^*-id .to       = Ix.^*-id-to
^*-id .from     = Ix.^*-id-from
^*-id .inverses = record { invl = prop! ; invr = prop! }

^*-assoc : f ^* (g ^* m) ≅ₘ (g ∘ f) ^* m
^*-assoc .to       = Ix.^*-comp-from
^*-assoc .from     = Ix.^*-comp-to
^*-assoc .inverses = record { invl = prop! ; invr = prop! }

⊤ₘ : Subobject X
⊤ₘ .domain = _
⊤ₘ .map    = id
⊤ₘ .monic  = id-monic

opaque
  !ₘ : m ≤ₘ ⊤ₘ
  !ₘ {m = m} = record { map = m .map ; sq = refl }

module _ {X} where
  open Binary-products (Sub X) (Sub-products pb) public renaming
    ( _⊗₀_  to infixr 30 _∩ₘ_
    ; π₁    to ∩ₘ≤l
    ; π₂    to ∩ₘ≤r
    ; ⟨_,_⟩ to ∩ₘ-univ
    )

opaque
  ∩ₘ-idl : ⊤ₘ ∩ₘ m ≅ₘ m
  ∩ₘ-idl = Sub-antisym ∩ₘ≤r (∩ₘ-univ !ₘ Sub.id)

  ∩ₘ-idr : m ∩ₘ ⊤ₘ ≅ₘ m
  ∩ₘ-idr = Sub-antisym ∩ₘ≤l (∩ₘ-univ Sub.id !ₘ)

  ∩ₘ-assoc : l ∩ₘ m ∩ₘ n ≅ₘ (l ∩ₘ m) ∩ₘ n
  ∩ₘ-assoc = Sub-antisym
    (∩ₘ-univ (∩ₘ-univ ∩ₘ≤l (∩ₘ≤l Sub.∘ ∩ₘ≤r)) (∩ₘ≤r Sub.∘ ∩ₘ≤r))
    (∩ₘ-univ (∩ₘ≤l Sub.∘ ∩ₘ≤l) (∩ₘ-univ (∩ₘ≤r Sub.∘ ∩ₘ≤l) ∩ₘ≤r))

opaque
  ^*-∩ₘ : f ^* (m ∩ₘ n) ≅ₘ f ^* m ∩ₘ f ^* n
  ^*-∩ₘ {f = f} {m = m} {n = n} = Sub-antisym
    (∩ₘ-univ
      (^*-univ record { sq = pb _ _ .square ∙ pullr refl })
      (^*-univ record { sq = pb _ _ .square ∙ pullr refl ∙ extendl (pb _ _ .square) }))
    record
      { map = pb _ _ .universal
        {p₁' = pb _ _ .p₁ ∘ pb _ _ .p₁}
        {p₂' = pb _ _ .universal {p₁' = pb _ _ .p₂ ∘ pb _ _ .p₁} {p₂' = pb _ _ .p₂ ∘ pb _ _ .p₂}
          (pulll (sym (pb _ _ .square)) ∙ pullr (pb _ _ .square) ∙ extendl (pb _ _ .square))}
        (sym (pullr (pb _ _ .p₁∘universal) ∙ extendl (sym (pb _ _ .square))))
      ; sq  = sym (pb _ _ .p₁∘universal ∙ introl refl)
      }

  ^*-⊤ₘ : f ^* ⊤ₘ ≅ₘ ⊤ₘ
  ^*-⊤ₘ {f = f} = Sub-antisym !ₘ record
    { map = pb _ _ .universal {p₁' = id} {p₂' = f} id-comm
    ; sq  = sym (pb _ _ .p₁∘universal ∙ introl refl)
    }

opaque
  is-pullback-along→iso : is-pullback-along C (m .map) h (n .map) → m ≅ₘ h ^* n
  is-pullback-along→iso pba = Sub-antisym
    record { map = pb _ _ .universal (pba .square) ; sq = sym (pb _ _ .p₁∘universal ∙ introl refl) }
    record { map = pba .universal (pb _ _ .square) ; sq = sym (pba .p₁∘universal ∙ introl refl) }

  iso→is-pullback-along : m ≅ₘ h ^* n → is-pullback-along C (m .map) h (n .map)
  iso→is-pullback-along _ .top = _
  iso→is-pullback-along {h = h} {n = n} m .has-is-pb = subst-is-pullback
    (sym (m .Sub.to .sq) ∙ idl _) refl refl refl
    (is-pullback-iso
      record
        { to       = m .Sub.from .map
        ; from     = m .Sub.to .map
        ; inverses = record
          { invl = ap ≤-over.map (m .Sub.invr)
          ; invr = ap ≤-over.map (m .Sub.invl)
          }
        }
      (pb h (n .map) .has-is-pb))
```
