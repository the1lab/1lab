```agda
open import Cat.Functor.Kan.Duality
open import Cat.Functor.Kan.Base
open import Cat.Functor.Adjoint
open import Cat.Prelude

import Cat.Functor.Reasoning as Func
import Cat.Reasoning as Cat

module Cat.Functor.Kan.Adjoint where
```

<!--
```agda
private
  variable
    o ℓ : Level
    C C′ D E : Precategory o ℓ
```
-->

# Adjoints are Kan extensions

The elevator pitch for Kan extensions is that "all concepts are Kan
extensions". The example we will give here is that, if $F \dashv G$ is
an adjunction, then $(G, \eta)$ gives $\Lan_F(\rm{Id})$. This isn't
exactly enlightening: adjunctions and Kan extensions have very different
vibes, but the latter concept _is_ a legitimate generalisation.

<!--
```agda
module _ {F : Functor C D} {G : Functor D C} (adj : F ⊣ G) where
  open Lan
  open is-lan
  open is-ran
  private
    module F = Functor F
    module G = Functor G
    module C = Cat C
    module D = Cat D

  open Functor
  open _⊣_ adj
  open _=>_
```
-->

```agda
  adjoint→is-lan : is-lan F Id G unit
```

The proof is mostly pushing symbols around, and the calculation is
available below unabridged. In components, $\sigma_x$ must give,
assuming a map $\alpha : \rm{Id} \To MFx$, a map $Gx \to Mx$. The
transformation we're looking for arises as the composite

$$
Gx \xto{\alpha} MFGx \xto{M\epsilon} Mx\text{,}
$$

where uniqueness and commutativity follows from the triangle identities
`zig`{.Agda} and `zag`{.Agda}.

```agda
  adjoint→is-lan .σ {M} α .η x = M .F₁ (counit.ε _) C.∘ α .η (G.₀ x)
  adjoint→is-lan .σ {M} nt .is-natural x y f =
    (M.₁ (counit.ε _) C.∘ nt .η _) C.∘ G.₁ f            ≡⟨ C.pullr (nt .is-natural _ _ _) ⟩
    M.₁ (counit.ε _) C.∘ M.₁ (F.₁ (G.₁ f)) C.∘ nt .η _  ≡⟨ M.extendl (counit.is-natural _ _ _) ⟩
    M.₁ f C.∘ M.₁ (counit.ε _) C.∘ nt .η _              ∎
    where module M = Func M

  adjoint→is-lan .σ-comm {M} {α} = Nat-path λ _ →
    (M.₁ (counit.ε _) C.∘ α.η _) C.∘ unit.η _              ≡⟨ C.pullr (α.is-natural _ _ _) ⟩
    M.₁ (counit.ε _) C.∘ M.₁ (F.F₁ (unit .η _)) C.∘ α.η _  ≡⟨ M.cancell zig ⟩
    α.η _                                                  ∎
    where module α = _=>_ α
          module M = Func M

  adjoint→is-lan .σ-uniq {M} {α} {σ'} p = Nat-path λ x →
    M.₁ (counit.ε _) C.∘ α.η _                ≡⟨ ap (_ C.∘_) (p ηₚ _) ⟩
    M.₁ (counit.ε _) C.∘ σ' .η _ C.∘ unit.η _ ≡⟨ C.extendl (sym (σ' .is-natural _ _ _)) ⟩
    σ' .η _ C.∘ G.₁ (counit.ε _) C.∘ unit.η _ ≡⟨ C.elimr zag ⟩
    σ' .η x                                   ∎
    where module α = _=>_ α
          module M = Func M
```

As expected, adjoints also yield right Kan extensions.

```agda
  adjoint→is-ran : is-ran G Id F counit
```

<details>
<summary>The proof is the same as left adjoints, just dualized.
</summary>

```agda
  adjoint→is-ran .σ {M} β .η x = β .η _ D.∘ M .F₁ (unit.η _)
  adjoint→is-ran .σ {M} β .is-natural _ _ _ =
    M.extendr (unit.is-natural _ _ _)
    ∙ D.pushl (β .is-natural _ _ _)
    where module M = Func M
  adjoint→is-ran .σ-comm {M} {β} = Nat-path λ _ →
    D.pulll (sym $ β .is-natural _ _ _)
    ∙ M.cancelr zag
    where module M = Func M
  adjoint→is-ran .σ-uniq {M} {β} {σ′} p = Nat-path λ _ →
    ap (D._∘ _) (p ηₚ _)
    ·· D.extendr (σ′ .is-natural _ _ _)
    ·· D.eliml zig
```
</details>
