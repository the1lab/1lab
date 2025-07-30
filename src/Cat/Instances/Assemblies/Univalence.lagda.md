<!--
```agda
open import Cat.Instances.Assemblies
open import Cat.Instances.Sets
open import Cat.Functor.Base
open import Cat.Prelude

open import Data.Partial.Total
open import Data.Partial.Base
open import Data.Bool.Base

open import Realisability.PCA.Trivial
open import Realisability.PCA

import Realisability.Data.Bool
import Realisability.PCA.Sugar
```
-->

```agda
module Cat.Instances.Assemblies.Univalence {ℓA} (𝔸 : PCA ℓA) where
```

<!--
```agda
open Realisability.Data.Bool 𝔸
open Realisability.PCA.Sugar 𝔸
```
-->

# Failure of univalence in categories of assemblies

While the category $\thecat{Asm}(\bA)$ of [[assemblies]] over a
[[partial combinatory algebra]] $\bA$ may look like an ordinary category
of structured sets, the computable maps $X \to Y$ are *not* the maps
which preserve the realisability relation. This means that the category
of assemblies fails to be [[univalent|univalent category]], unless $\bA$
is trivial (so that $\thecat{Asm}(\bA) \cong \Sets$).

We prove this by showing that there is an automorphism of the boolean
assembly `𝟚`{.Agda} that swaps the booleans, but that this automorphism
isn't witnessed by any *identity* `𝟚 ≡ 𝟚`{.Agda}, since the only such
identity is reflexivity: intuitively, the type of assemblies is too
*rigid*.

```agda
notᴬ : 𝟚 𝔸 Asm.≅ 𝟚 𝔸
notᴬ = Asm.involution→iso to (ext not-involutive) where
  to = to-assembly-hom record where
    map = not
    realiser = `not
    tracks = λ where
      {true}  p → inc (sym (ap (`not ⋆_) (sym (□-out! p)) ∙ `not-βt))
      {false} p → inc (sym (ap (`not ⋆_) (sym (□-out! p)) ∙ `not-βf))
```

We now assume that $\thecat{Asm}(\bA)$ is univalent, and thus that we
have a path `𝟚 ≡ 𝟚`{.Agda} arising from `notᴬ`{.Agda}. The underlying
action on *sets* must arise from the negation equivalence on the booleans,
so by transporting the fact that $\tt{true} \Vdash \sf{true}$ along that
path we get that $\tt{true} \Vdash \sf{false}$, which implies that $\bA$
is trivial since the only realiser for $\sf{false}$ is $\tt{false}$.

```agda
Assemblies-not-univalent
  : is-category (Assemblies 𝔸 lzero) → is-trivial-pca 𝔸
Assemblies-not-univalent cat = sym (□-out! true⊩false)
  where
    p : 𝟚 𝔸 ≡ 𝟚 𝔸
    p = cat .to-path notᴬ

    module Sets = is-identity-system Sets-is-category
    Γ = Forget 𝔸

    q : transport (ap Ob p) true ≡ false
    q =
      subst ∣_∣ ⌜ ap· Γ p ⌝ true                       ≡⟨ ap! (F-map-path Γ cat Sets-is-category notᴬ) ⟩
      subst ∣_∣ (Sets.to-path (F-map-iso Γ notᴬ)) true ≡⟨⟩
      false                                            ∎

    r : [ 𝟚 𝔸 ] `true .fst ⊩ true ≡ [ 𝟚 𝔸 ] `true .fst ⊩ false
    r =
      [ 𝟚 𝔸 ] `true .fst ⊩ true                                      ≡⟨ ap (λ r → `true .fst ∈ r true) (from-pathp⁻ (ap realisers p)) ⟩
      [ 𝟚 𝔸 ] transport refl (`true .fst) ⊩ transport (ap Ob p) true ≡⟨ ap₂ ([ 𝟚 𝔸 ]_⊩_) (transport-refl _) q ⟩
      [ 𝟚 𝔸 ] `true .fst ⊩ false                                     ∎

    true⊩false : [ 𝟚 𝔸 ] `true .fst ⊩ false
    true⊩false = transport r (inc refl)
```
