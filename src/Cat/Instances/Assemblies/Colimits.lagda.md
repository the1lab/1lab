<!--
```agda
open import Cat.Instances.Assemblies
open import Cat.Diagram.Coproduct
open import Cat.Prelude

open import Data.Partial.Total
open import Data.Partial.Base
open import Data.Vec.Base using ([] ; _∷_)
open import Data.Sum hiding ([_,_])

open import Realisability.PCA

import Realisability.PCA.Sugar
import Realisability.Data.Sum
import Realisability.Base
```
-->

```agda
module Cat.Instances.Assemblies.Colimits {ℓA} (𝔸 : PCA ℓA) where
```

<!--
```agda
open Realisability.PCA.Sugar 𝔸
open Realisability.Data.Sum 𝔸
open Realisability.Base 𝔸

open is-coproduct
open Coproduct

private variable
  ℓ ℓ' : Level
  X Y Z : Assembly 𝔸 ℓ
```
-->

# Finite colimits of assemblies

We can define the [[coproduct]] of [[assemblies]] $X, Y$ over a
[[partial combinatory algebra]] $\bA$ using our encoding of [[sums in a
PCA]]. The underlying set is simply the [[sum type]] $X \uplus Y$, and
we define the realisability relation by
$$
\begin{align*}
\tt{inl}\, \sf{x} &\Vdash \operatorname{inl} x &\textit{iff}\enspace &\sf{x} \Vdash x \\
\tt{inr}\, \sf{y} &\Vdash \operatorname{inr} y &\textit{iff}\enspace &\sf{y} \Vdash y\text{.} \\
\end{align*}
$$

```agda
_⊎Asm_ : Assembly 𝔸 ℓ → Assembly 𝔸 ℓ' → Assembly 𝔸 (ℓ ⊔ ℓ')
(X ⊎Asm Y) .Ob         = ⌞ X ⌟ ⊎ ⌞ Y ⌟
(X ⊎Asm Y) .has-is-set = hlevel 2

(X ⊎Asm Y) .realisers (inl x) = record where
  mem e = elΩ (Σ[ a ∈ ↯ ⌞ 𝔸 ⌟ ] (e ≡ `inl ⋆ a × [ X ] a ⊩ x))
  def   = rec! λ _ a p → subst ⌞_⌟ (sym a) (`inl↓₁ (X .def p))

(X ⊎Asm Y) .realisers (inr x) = record where
  mem e = elΩ (Σ[ a ∈ ↯ ⌞ 𝔸 ⌟ ] (e ≡ `inr ⋆ a × [ Y ] a ⊩ x))
  def   = rec! λ _ a p → subst ⌞_⌟ (sym a) (`inr↓₁ (Y .def p))
```

<!--
```agda
(X ⊎Asm Y) .realised (inl x) = do
  (p , rx) ← X .realised x
  inc (`inl ⋆ p , inc (p , refl , rx))

(X ⊎Asm Y) .realised (inr x) = do
  (p , rx) ← Y .realised x
  inc (`inr ⋆ p , inc (p , refl , rx))
```
-->

By construction, the constructor *functions* are realised by the
constructor *programs*, i.e. `` `inl ``{.Agda} and `` `inr ``{.Agda}.

```agda
inlᴬ : Assembly-hom X (X ⊎Asm Y)
inlᴬ = to-assembly-hom record where
  map       = inl
  realiser  = `inl
  tracks ha = inc (_ , refl , ha)

inrᴬ : Assembly-hom Y (X ⊎Asm Y)
inrᴬ = to-assembly-hom record where
  map       = inr
  realiser  = `inr
  tracks ha = inc (_ , refl , ha)
```

```agda
Assembly-coproducts : has-coproducts (Assemblies 𝔸 ℓ)
Assembly-coproducts A B .coapex = A ⊎Asm B
Assembly-coproducts A B .ι₁ = inlᴬ
Assembly-coproducts A B .ι₂ = inrᴬ
Assembly-coproducts A B .has-is-coproduct .[_,_] {Q = Q} f g = record where
  map = λ where
    (inl a) → f · a
    (inr b) → g · b
```

Similarly, a pattern-matching function is tracked by a pattern matching
program. Suppose $f : X \to Z$ and $g : Y \to Z$ are tracked by $\sf{f}$
and $\sf{g}$, respectively. We want to show that $[f, g] : X \uplus Y
\to Z$ is tracked by `` `match ``{.Agda} of $\sf{f}$ and $\sf{g}$.

```agda
  tracked = do
    ft ← f .tracked
    gt ← g .tracked
    let
      f↓ = ft .realiser .snd
      g↓ = gt .realiser .snd
    inc record where
      realiser = `match ⋆ ft ⋆ gt , `match↓₂ f↓ g↓
```

This is by cases on the datum we've applied, which lets both $[f, g]$
and the realisability relation reduce; in either case, after invoking
the reduction rule for `` `match ``{.Agda} at a constructor, we end up
with precisely with the assumptions that $f$ and $g$ are tracked.

```agda
      tracks = λ where
        {inl x} ha → □-out (Q .realisers _ .mem _ .is-tr) do
          (e , α , e⊩x) ← ha
          pure $ subst⊩ Q (ft .tracks e⊩x) $
            ap₂ _%_ refl α ∙ `match-βl (A .def e⊩x) f↓ g↓

        {inr x} ha → □-out (Q .realisers _ .mem _ .is-tr) do
          (e , α , e⊩x) ← ha
          pure $ subst⊩ Q (gt .tracks e⊩x) $
            ap₂ _%_ refl α ∙ `match-βr (B .def e⊩x) f↓ g↓

Assembly-coproducts A B .has-is-coproduct .[]∘ι₁ = ext λ _ → refl
Assembly-coproducts A B .has-is-coproduct .[]∘ι₂ = ext λ _ → refl
Assembly-coproducts A B .has-is-coproduct .unique p q = ext λ where
  (inl x) → ap map p · x
  (inr x) → ap map q · x
```
