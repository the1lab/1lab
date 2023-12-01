<!--
```agda
open import Cat.Base

import Cat.Morphism
```
-->

```agda
module Cat.Morphism.Duality {o ℓ} (𝒞 : Precategory o ℓ) where
```

<!--
```agda
private
  module 𝒞 = Cat.Morphism 𝒞
  module 𝒞^op = Cat.Morphism (𝒞 ^op)

private variable
  a b c d : 𝒞.Ob
  f g : 𝒞.Hom a b
```
-->

# Duality of morphism classes

In this file we prove that morphisms classes in a category
correspond to their duals in the opposite category. There is very
little interesting mathematical content in this file; it is pure
boilerplate.

We start by showing that monos and epis are dual.

```agda
co-mono→epi : a 𝒞^op.↪ b → b 𝒞.↠ a
co-mono→epi f .Cat.Morphism.mor = 𝒞^op.mor f
co-mono→epi f .Cat.Morphism.epic = 𝒞^op.monic f

epi→co-mono : b 𝒞.↠ a → a 𝒞^op.↪ b
epi→co-mono f .Cat.Morphism.mor = 𝒞.mor f
epi→co-mono f .Cat.Morphism.monic = 𝒞.epic f

co-epi→mono : a 𝒞^op.↠ b → b 𝒞.↪ a
co-epi→mono f .Cat.Morphism.mor = 𝒞^op.mor f
co-epi→mono f .Cat.Morphism.monic = 𝒞^op.epic f

mono→co-epi : b 𝒞.↪ a → a 𝒞^op.↠ b
mono→co-epi f .Cat.Morphism.mor = 𝒞.mor f
mono→co-epi f .Cat.Morphism.epic = 𝒞.monic f
```

Next, sections and retractions.

```agda
co-section→retract : 𝒞^op.has-section f → 𝒞.has-retract f
co-section→retract f .Cat.Morphism.retract = 𝒞^op.section f
co-section→retract f .Cat.Morphism.is-retract = 𝒞^op.is-section f

retract→co-section : 𝒞.has-retract f → 𝒞^op.has-section f
retract→co-section f .Cat.Morphism.section = 𝒞.retract f
retract→co-section f .Cat.Morphism.is-section = 𝒞.is-retract f

co-retract→section : 𝒞^op.has-retract f → 𝒞.has-section f
co-retract→section f .Cat.Morphism.section = 𝒞^op.retract f
co-retract→section f .Cat.Morphism.is-section = 𝒞^op.is-retract f

section→co-retract : 𝒞.has-section f → 𝒞^op.has-retract f
section→co-retract f .Cat.Morphism.retract = 𝒞.section f
section→co-retract f .Cat.Morphism.is-retract = 𝒞.is-section f
```


Next, we show that invertible morphisms are self-dual.

```agda
co-inverses→inverses : 𝒞^op.Inverses f g → 𝒞.Inverses f g
co-inverses→inverses i .Cat.Morphism.Inverses.invl =
  𝒞^op.Inverses.invr i
co-inverses→inverses i .Cat.Morphism.Inverses.invr =
  𝒞^op.Inverses.invl i

inverses→co-inverses : 𝒞.Inverses f g → 𝒞^op.Inverses f g
inverses→co-inverses i .Cat.Morphism.Inverses.invl =
  𝒞.Inverses.invr i
inverses→co-inverses i .Cat.Morphism.Inverses.invr =
  𝒞.Inverses.invl i

co-invertible→invertible : 𝒞^op.is-invertible f → 𝒞.is-invertible f
co-invertible→invertible i .Cat.Morphism.is-invertible.inv =
  𝒞^op.is-invertible.inv i
co-invertible→invertible i .Cat.Morphism.is-invertible.inverses =
  co-inverses→inverses (𝒞^op.is-invertible.inverses i)

invertible→co-invertible : 𝒞.is-invertible f → 𝒞^op.is-invertible f
invertible→co-invertible i .Cat.Morphism.is-invertible.inv =
  𝒞.is-invertible.inv i
invertible→co-invertible i .Cat.Morphism.is-invertible.inverses =
  inverses→co-inverses (𝒞.is-invertible.inverses i)

co-iso→iso : a 𝒞^op.≅ b → b 𝒞.≅ a
co-iso→iso f .Cat.Morphism.to = 𝒞^op.to f
co-iso→iso f .Cat.Morphism.from = 𝒞^op.from f
co-iso→iso f .Cat.Morphism.inverses = co-inverses→inverses (𝒞^op.inverses f)

iso→co-iso : b 𝒞.≅ a → a 𝒞^op.≅ b
iso→co-iso f .Cat.Morphism.to = 𝒞.to f
iso→co-iso f .Cat.Morphism.from = 𝒞.from f
iso→co-iso f .Cat.Morphism.inverses = inverses→co-inverses (𝒞.inverses f)
```
