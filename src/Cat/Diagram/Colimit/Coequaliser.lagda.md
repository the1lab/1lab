```agda
open import Cat.Instances.Shape.Parallel

open import Cat.Diagram.Colimit.Base
open import Cat.Diagram.Coequaliser
open import Cat.Instances.Functor
open import Cat.Diagram.Initial
open import Cat.Prelude

open import Data.Bool

module Cat.Diagram.Colimit.Coequaliser
  {o ℓ} (Cat : Precategory o ℓ) where
```

<!--
```agda
open import Cat.Reasoning Cat
open import Cat.Univalent Cat

open is-coequaliser
open Coequaliser
open Initial
open Cocone-hom
open Functor
open Cocone
```
-->

We establish the correspondence between `Coequaliser`{.Agda} and the
`Colimit`{.Agda} of a [parallel arrows] diagram.

[parallel arrows]: Cat.Instances.Shape.Parallel.html

```agda
Fork→Cocone
  : ∀ {E} (F : Functor ·⇉· Cat)
  → (eq : Hom (F .F₀ true) E)
  → eq ∘ F .F₁ {false} {true} false ≡ eq ∘ F .F₁ {false} {true} true
  → Cocone F
Fork→Cocone F eq p .coapex = _
Fork→Cocone F eq p .ψ false = eq ∘ F .F₁ false
Fork→Cocone F eq p .ψ true = eq
Fork→Cocone F eq p .commutes {false} {false} tt = elimr (F .F-id)
Fork→Cocone F eq p .commutes {false} {true} false = refl
Fork→Cocone F eq p .commutes {false} {true} true = sym p
Fork→Cocone F eq p .commutes {true} {true} tt = elimr (F .F-id)

Coequaliser→Colimit
  : ∀ {F : Functor ·⇉· Cat}
  → Coequaliser Cat (F .F₁ false) (F .F₁ true)
  → Colimit F
Coequaliser→Colimit {F = F} coeq = colim where
  module coeq = Coequaliser coeq
  colim : Colimit _
  colim .bot = Fork→Cocone F coeq.coeq coeq.coequal
  colim .has⊥ K .centre .hom =
    coeq.coequalise $ K .commutes {false} {true} false
      ∙ sym (K .commutes true)
  colim .has⊥ K .centre .commutes false =
    pulll coeq.universal ∙ K .commutes {false} {true} false
  colim .has⊥ K .centre .commutes true = coeq.universal
  colim .has⊥ K .paths other = Cocone-hom-path _ (sym (coeq.unique p)) where
    p : K .ψ true ≡ other .hom ∘ coeq.coeq
    p = sym (other .commutes _)
  
Colimit→Coequaliser
  : ∀ {F : Functor ·⇉· Cat}
  → Colimit F
  → Coequaliser Cat (F .F₁ false) (F .F₁ true)
Colimit→Coequaliser {F = F} colim = coequ where
  module colim = Initial colim

  coequ : Coequaliser Cat _ _
  coequ .coapex = _
  coequ .coeq = colim.bot .ψ true
  coequ .has-is-coeq .coequal =
    colim.bot .commutes {false} {true} false
    ∙ sym (colim.bot .commutes true)
  coequ .has-is-coeq .coequalise p =
    colim.has⊥ (Fork→Cocone _ _ p) .centre .hom
  coequ .has-is-coeq .universal {p = p} =
    colim.has⊥ (Fork→Cocone _ _ p) .centre .commutes true
  coequ .has-is-coeq .unique {e′ = e′} {p = p} {colim = colim'} x =
    sym (ap hom (colim.has⊥ (Fork→Cocone _ _ p) .paths other))
    where
      other : Cocone-hom _ _ _
      other .hom = colim'
      other .commutes false =
        colim' ∘ colim .bot .ψ false               ≡⟨ pushr (sym $ colim.bot .commutes false) ⟩
        (colim' ∘ colim.bot .ψ true) ∘ F .F₁ false ≡˘⟨ ap (_∘ F .F₁ false) x ⟩
        e′ ∘ F .F₁ false ∎
      other .commutes true = sym x
```
