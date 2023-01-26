```agda
open import Cat.Base
import Cat.Morphism

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

# Duality of Morphism Classes

In this file we prove that morphisms classes in a category
correspond to their duals in the opposite category. There is very
little interesting mathematical content in this file; it is pure
boilerplate.

We start by showing that monos and epis are dual.

```agda
monic^op→epic : a 𝒞^op.↪ b → b 𝒞.↠ a
monic^op→epic f .Cat.Morphism.mor = 𝒞^op.mor f
monic^op→epic f .Cat.Morphism.epic = 𝒞^op.monic f

epic→monic^op : b 𝒞.↠ a → a 𝒞^op.↪ b
epic→monic^op f .Cat.Morphism.mor = 𝒞.mor f
epic→monic^op f .Cat.Morphism.monic = 𝒞.epic f

epic^op→monic : a 𝒞^op.↠ b → b 𝒞.↪ a
epic^op→monic f .Cat.Morphism.mor = 𝒞^op.mor f
epic^op→monic f .Cat.Morphism.monic = 𝒞^op.epic f

monic→epic^op : b 𝒞.↪ a → a 𝒞^op.↠ b
monic→epic^op f .Cat.Morphism.mor = 𝒞.mor f
monic→epic^op f .Cat.Morphism.epic = 𝒞.monic f
```

Next, sections and retractions.

```agda
section^op→retract : 𝒞^op.has-section f → 𝒞.has-retract f
section^op→retract f .Cat.Morphism.retract = 𝒞^op.section f
section^op→retract f .Cat.Morphism.is-retract = 𝒞^op.is-section f

retract→section^op : 𝒞.has-retract f → 𝒞^op.has-section f
retract→section^op f .Cat.Morphism.section = 𝒞.retract f
retract→section^op f .Cat.Morphism.is-section = 𝒞.is-retract f

retract^op→section : 𝒞^op.has-retract f → 𝒞.has-section f
retract^op→section f .Cat.Morphism.section = 𝒞^op.retract f
retract^op→section f .Cat.Morphism.is-section = 𝒞^op.is-retract f

section→retract^op : 𝒞.has-section f → 𝒞^op.has-retract f
section→retract^op f .Cat.Morphism.retract = 𝒞.section f
section→retract^op f .Cat.Morphism.is-retract = 𝒞.is-section f
```


Next, we show that invertible morphisms are self-dual.

```agda
inverses^op→inverses : 𝒞^op.Inverses f g → 𝒞.Inverses f g
inverses^op→inverses i .Cat.Morphism.Inverses.invl =
  𝒞^op.Inverses.invr i
inverses^op→inverses i .Cat.Morphism.Inverses.invr =
  𝒞^op.Inverses.invl i

inverses→inverses^op : 𝒞.Inverses f g → 𝒞^op.Inverses f g
inverses→inverses^op i .Cat.Morphism.Inverses.invl =
  𝒞.Inverses.invr i
inverses→inverses^op i .Cat.Morphism.Inverses.invr =
  𝒞.Inverses.invl i

invertible^op→invertible : 𝒞^op.is-invertible f → 𝒞.is-invertible f
invertible^op→invertible i .Cat.Morphism.is-invertible.inv =
  𝒞^op.is-invertible.inv i
invertible^op→invertible i .Cat.Morphism.is-invertible.inverses =
  inverses^op→inverses (𝒞^op.is-invertible.inverses i)

invertible→invertible^op : 𝒞.is-invertible f → 𝒞^op.is-invertible f
invertible→invertible^op i .Cat.Morphism.is-invertible.inv =
  𝒞.is-invertible.inv i
invertible→invertible^op i .Cat.Morphism.is-invertible.inverses =
  inverses→inverses^op (𝒞.is-invertible.inverses i)

iso^op→iso : a 𝒞^op.≅ b → b 𝒞.≅ a
iso^op→iso f .Cat.Morphism.to = 𝒞^op.to f
iso^op→iso f .Cat.Morphism.from = 𝒞^op.from f
iso^op→iso f .Cat.Morphism.inverses = inverses^op→inverses (𝒞^op.inverses f)

iso→iso^op : b 𝒞.≅ a → a 𝒞^op.≅ b
iso→iso^op f .Cat.Morphism.to = 𝒞.to f
iso→iso^op f .Cat.Morphism.from = 𝒞.from f
iso→iso^op f .Cat.Morphism.inverses = inverses→inverses^op (𝒞.inverses f)
```
