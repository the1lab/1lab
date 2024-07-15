<!--
```agda
open import Cat.Functor.Hom.Representable
open import Cat.Instances.Shape.Terminal
open import Cat.Diagram.Colimit.Base
open import Cat.Instances.Functor
open import Cat.Functor.Constant
open import Cat.Functor.Kan.Base
open import Cat.Functor.Compose
open import Cat.Functor.Hom
open import Cat.Prelude

import Cat.Reasoning
```
-->

```agda
module Cat.Diagram.Colimit.Representable where
```

## Representability of colimits

Since [colimits] are defined by universal property, we can also phrase
the definition in terms of an equivalence between $\hom$-functors.

[colimits]: Cat.Diagram.Colimit.Base.html

<!--
```agda
module _
  {o ℓ}
  {J : Precategory ℓ ℓ} {C : Precategory o ℓ} {Dia : Functor J C}
  where
  private
    module C = Cat.Reasoning C
    open Functor
    open _=>_
    open Corepresentation
    open Colimit
    open is-lan
```
-->

Let $\mathrm{Dia} : \cJ \to \cC$ be some diagram in $\cC$. If
$\mathrm{Dia}$ has a colimit $c$, then that means that maps **out** of
$c$ are in bijection with a product of maps $\pi_i$, subject to some
conditions.

```agda
  Lim[C[F-,=]] : Functor C (Sets ℓ)
  Lim[C[F-,=]] .F₀ c = el (Dia => Const c) Nat-is-set
  Lim[C[F-,=]] .F₁ f α = constⁿ f ∘nt α
  Lim[C[F-,=]] .F-id = ext λ _ _ → C.idl _
  Lim[C[F-,=]] .F-∘ _ _ = ext λ _ _ → sym $ C.assoc _ _ _

  Hom-into-inj
    : ∀ {c : C.Ob} (eta : Dia => Const c)
    → Hom-from C c => Lim[C[F-,=]]
  Hom-into-inj eta .η x f = constⁿ f ∘nt eta
  Hom-into-inj eta .is-natural x y f = ext λ g _ →
    sym $ C.assoc _ _ _

  represents→is-colimit
    : ∀ {c : C.Ob} {eta : Dia => Const c}
    → is-invertibleⁿ (Hom-into-inj eta)
    → is-colimit Dia c eta
  represents→is-colimit {c} {eta} nat-inv = colim where
    module nat-inv = is-invertibleⁿ nat-inv

    colim : is-colimit Dia c eta
    colim .σ {M} α =
      !constⁿ (nat-inv.inv .η _ (to-coconeⁿ α))
    colim .σ-comm {M} {α} = ext λ j → unext nat-inv.invl _ _ j
    colim .σ-uniq {M} {α} {σ'} q = ext λ j →
      nat-inv.inv .η _ (to-coconeⁿ ⌜ α ⌝)                  ≡⟨ ap! q ⟩
      nat-inv.inv .η _ ⌜ to-coconeⁿ ((σ' ◂ !F) ∘nt eta) ⌝  ≡⟨ ap! trivial! ⟩
      nat-inv.inv .η _ ((!constⁿ (σ' .η tt) ◂ !F) ∘nt eta) ≡⟨ unext nat-inv.invr _ _ ⟩
      σ' .η tt                                             ∎
```
