---
description: |
  Regular separators.
---
<!--
```agda
open import Cat.Diagram.Coequaliser.RegularEpi
open import Cat.Diagram.Coproduct.Copower
open import Cat.Diagram.Coproduct.Indexed
open import Cat.Diagram.Coequaliser
open import Cat.Prelude

import Cat.Diagram.Separator.Strong
import Cat.Morphism.StrongEpi
import Cat.Diagram.Separator
import Cat.Reasoning
```
-->
```agda
module Cat.Diagram.Separator.Regular
  {o ℓ}
  (C : Precategory o ℓ)
  (coprods : (I : Set ℓ) → has-coproducts-indexed-by C ∣ I ∣)
  where
```

<!--
```agda
open Cat.Morphism.StrongEpi C
open Cat.Diagram.Separator.Strong C coprods
open Cat.Diagram.Separator C
open Cat.Reasoning C
open Copowers coprods

private variable
  s : Ob
```
-->

# Regular separators

:::{.definition #strong-separator}
Let $\cC$ be a category with [[set-indexed coproducts|indexed-coproduct]].
An object $S$ is a **regular separator** if the canonical map $\coprod_{\cC(S,X)} S \to X$
is a [[regular epi]].
:::

```agda
is-regular-separator : Ob → Type (o ⊔ ℓ)
is-regular-separator s = ∀ {x} → is-regular-epi C (⊗!.match (Hom s x) s λ e → e)
```

:::{.definition #strong-separating-family}
A family of objects $S_i$ is a **regular separating family** if the
canonical map $\coprod_{\Sigma(i : I), \cC(S_i, X)} S_i \to X$
is a [[regular epi]].
:::

```agda
is-regular-separating-family
  : ∀ (Idx : Set ℓ)
  → (sᵢ : ∣ Idx ∣ → Ob)
  → Type (o ⊔ ℓ)
is-regular-separating-family Idx sᵢ =
  ∀ {x} → is-regular-epi C (∐!.match (Σ[ i ∈ ∣ Idx ∣ ] (Hom (sᵢ i) x)) (sᵢ ⊙ fst) snd)
```

To motivate this definition, note that [[dense separators]] are extremely
rare, as it imposes a strong discreteness condition on $\cC$. Instead, it
is slightly more reasonable to assume that every object of $\cC$ arises
via some *quotient* of a bunch of points. It this intuition is what regular
separators codify.

As the name suggests, regular separators and regular separating families
are separators and separating families, resp. This follows directly
from the fact that regular epis are epis.

```agda
regular-separator→separator
  : ∀ {s}
  → is-regular-separator s
  → is-separator s
regular-separator→separator regular =
  epi→separator coprods $
  is-regular-epi→is-epic regular

regular-separating-family→separating-family
  : ∀ (Idx : Set ℓ) (sᵢ : ∣ Idx ∣ → Ob)
  → is-regular-separating-family Idx sᵢ
  → is-separating-family sᵢ
regular-separating-family→separating-family Idx sᵢ regular =
  epi→separating-family coprods Idx sᵢ $
  is-regular-epi→is-epic regular
```

## Relations to other separators

Every [[dense separator]] is regular.

```agda
dense-separator→regular-separator
  : is-dense-separator s
  → is-regular-separator s
```

The proof here mirrors the proof that [colimits yield regular epis in
the presence of enough coproducts]. More explicitly, the idea is that
$\cC(S,X) \otimes S$ is already a sufficient approximation of $X$, so
we do not need to perform any quotienting. In other words, $(\id, \id)$
ought to be a coequalising pair.

[colimits yield regular epis in the presence of enough coproducts]:
  Cat.Diagram.Coequaliser.RegularEpi.html#existence-of-regular-epis

```agda
dense-separator→regular-separator {s = s} dense {x} = regular where
  module dense = is-dense-separator dense
  open is-regular-epi
  open is-coequaliser

  regular : is-regular-epi C (⊗!.match (Hom s x) s λ e → e)
  regular .r = Hom s x ⊗! s
  regular .arr₁ = id
  regular .arr₂ = id
  regular .has-is-coeq .coequal = refl
```

This is straightforward enough to prove with sufficient elbow grease.

```agda
  regular .has-is-coeq .universal {e' = e'} _ =
    dense.universal λ e → e' ∘ ⊗!.ι (Hom s x) s e
  regular .has-is-coeq .factors {e' = e'} {p = p} =
    ⊗!.unique₂ (Hom s x) s λ e →
      (dense.universal _ ∘ ⊗!.match _ _ _) ∘ ⊗!.ι _ _ e ≡⟨ pullr (⊗!.commute _ _) ⟩
      dense.universal _ ∘ e                             ≡⟨ dense.commute ⟩
      e' ∘ ⊗!.ι _ _ e                                   ∎
  regular .has-is-coeq .unique {e' = e'} {colim = h} p =
    dense.unique _ λ e →
      h ∘ e                           ≡˘⟨ ap (h ∘_) (⊗!.commute (Hom s x) s) ⟩
      h ∘ ⊗!.match _ _ _ ∘ ⊗!.ι _ _ e ≡⟨ pulll p ⟩
      e' ∘ ⊗!.ι _ _ e                 ∎
```

Additionally, note that every regular separator is a [[strong separator]];
this follows directly from the fact that every regular epi is strong.

```agda
regular-separator→strong-separator
  : ∀ {s}
  → is-regular-separator s
  → is-strong-separator s
regular-separator→strong-separator {s} regular {x} =
  is-regular-epi→is-strong-epi _ regular
```
