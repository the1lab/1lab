<!--
```agda
open import Cat.Functor.Bifunctor.Duality
open import Cat.Functor.Naturality
open import Cat.Monoidal.Base
open import Cat.Prelude

import Cat.Reasoning

open Monoidal-category
```
-->

```agda
module Cat.Monoidal.Opposite {o ℓ}
  {C : Precategory o ℓ} (Cᵐ : Monoidal-category C)
  where
```

<!--
```agda
private module C where
  open Monoidal-category Cᵐ public
  open Cat.Reasoning C public
open _=>_
```
-->

# Opposite monoidal categories {defines="opposite-monoidal-category"}

If $\cC$ has the structure of a [[monoidal category]], then there is
a natural monoidal structure on its [[opposite category]] $\cC\op$,
with the same unit and the [[opposite bifunctor]] for the tensor 
product.

```agda
_^mop : Monoidal-category (C ^op)
_^mop .-⊗- = bop C.-⊗-
_^mop .Unit = C.Unit
```

The coherence isomorphisms are straightforward to obtain from those of
$\cC$: Since we only need morphisms in the opposite direction, we can
can take the inverses of the coherence isomorphisms for $\cC$.

```agda
_^mop .unitor-l = to-natural-iso record where
  eta x = C.λ←
  inv x = C.λ→
  eta∘inv x = C.invl C.λ≅
  inv∘eta x = C.invr C.λ≅
  natural x y f = Isoⁿ.from C.unitor-l .is-natural y x f

_^mop .unitor-r = to-natural-iso record where
  eta x = C.ρ←
  inv x = C.ρ→
  eta∘inv x = C.invl C.ρ≅
  inv∘eta x = C.invr C.ρ≅
  natural x y f = Isoⁿ.from C.unitor-r .is-natural y x f

_^mop .associator = to-natural-iso record where
  eta (x , y , z) = C.α← x y z
  inv (x , y , z) = C.α→ x y z
  eta∘inv (x , y , z) = C.invl C.α≅
  inv∘eta (x , y , z) = C.invr C.α≅
  natural (x , y , z) (x' , y' , z') f = Isoⁿ.from C.associator .is-natural _ _ f
```

The triangle and pentagon identities are acquired from those of $\cC$
by inverting both sides. In the latter case we need to take care to
reassociate composition.

```agda
_^mop .triangle = C.inverse-unique refl refl 
  (C.α≅ C.Iso⁻¹ C.∙Iso C.◀.F-map-iso C.ρ≅ C.Iso⁻¹) 
  (C.▶.F-map-iso C.λ≅ C.Iso⁻¹) 
  C.triangle
    
_^mop .pentagon = sym (C.assoc _ _ _) ∙ C.inverse-unique refl refl
  ( C.▶.F-map-iso (C.α≅ C.Iso⁻¹) 
    C.∙Iso (C.α≅ C.Iso⁻¹) 
    C.∙Iso C.◀.F-map-iso (C.α≅ C.Iso⁻¹))
  (C.α≅ C.Iso⁻¹ C.∙Iso C.α≅ C.Iso⁻¹)
  (sym (C.assoc _ _ _) ∙ C.pentagon)
```
