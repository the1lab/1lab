<!--
```agda
open import Cat.Displayed.Total.Op
open import Cat.Displayed.Base
open import Cat.Prelude

import Cat.Displayed.Reasoning
import Cat.Displayed.Morphism
import Cat.Morphism.Duality
import Cat.Morphism
```
-->

```agda
module Cat.Displayed.Morphism.Duality
  {o ℓ o′ ℓ′}
  {ℬ : Precategory o ℓ}
  (ℰ : Displayed ℬ o′ ℓ′)
  where
```

<!--
```agda
private
  module ℬ = Cat.Morphism ℬ
  module ℬ^op = Cat.Morphism (ℬ ^op)
  module ℰ = Cat.Displayed.Morphism ℰ
  module ℰ^op = Cat.Displayed.Morphism (ℰ ^total-op)

  open Cat.Morphism.Duality ℬ
  open Cat.Displayed.Reasoning ℰ

  open Cat.Displayed.Morphism

private variable
  a b c d : ℬ.Ob
  f g : ℬ.Hom a b
  a′ b′ c′ d′ : Ob[ a ]
  f′ g′ : Hom[ f ] a′ b′
```
-->


# Duality of Displayed Morphism Classes

In this file we prove that morphism classes in a displayed category
correspond to their duals in the total opposite displayed category.
There is *even less* mathematical content here than the [non-displayed
case], just mountains of boilerplate.

[non-displayed case]: Cat.Morphism.Duality.html

We start by showing that displayed monos and epis are dual.

```agda
co-mono[]→epi[]
  : ∀ {f : a ℬ^op.↪ b}
  → a′ ℰ^op.↪[ f ] b′
  → b′ ℰ.↠[ co-mono→epi f ] a′
co-mono[]→epi[] f .mor′ = ℰ^op.mor′ f
co-mono[]→epi[] f .epic′ = ℰ^op.monic′ f

epi[]→co-mono[]
  : ∀ {f : b ℬ.↠ a}
  → b′ ℰ.↠[ f ] a′
  → a′ ℰ^op.↪[ epi→co-mono f ] b′
epi[]→co-mono[] f .mor′ = ℰ.mor′ f
epi[]→co-mono[] f .monic′ = ℰ.epic′ f

co-epi[]→mono[]
  : ∀ {f : a ℬ^op.↠ b}
  → a′ ℰ^op.↠[ f ] b′
  → b′ ℰ.↪[ co-epi→mono f ] a′
co-epi[]→mono[] f .mor′ = ℰ^op.mor′ f
co-epi[]→mono[] f .monic′ = ℰ^op.epic′ f

mono[]→co-epi[]
  : ∀ {f : b ℬ.↪ a}
  → b′ ℰ.↪[ f ] a′
  → a′ ℰ^op.↠[ mono→co-epi f ] b′
mono[]→co-epi[] f .mor′ = ℰ.mor′ f
mono[]→co-epi[] f .epic′ = ℰ.monic′ f
```

Next, we show the same for weak monos and weak epis.

```agda
weak-mono→weak-co-epi
  : ∀ {f : ℬ.Hom b a}
  → ℰ.weak-mono-over f b′ a′
  → ℰ^op.weak-epi-over f a′ b′
weak-mono→weak-co-epi f .mor′ = ℰ.mor′ f
weak-mono→weak-co-epi f .weak-epic = ℰ.weak-monic f

weak-co-epi→weak-mono
  : ∀ {f : ℬ.Hom b a}
  → ℰ^op.weak-epi-over f a′ b′
  → ℰ.weak-mono-over f b′ a′
weak-co-epi→weak-mono f .mor′ = ℰ^op.mor′ f
weak-co-epi→weak-mono f .weak-monic = ℰ^op.weak-epic f

weak-epi→weak-co-mono
  : ∀ {f : ℬ.Hom b a}
  → ℰ.weak-epi-over f b′ a′
  → ℰ^op.weak-mono-over f a′ b′
weak-epi→weak-co-mono f .mor′ = ℰ.mor′ f
weak-epi→weak-co-mono f .weak-monic = ℰ.weak-epic f

weak-co-mono→weak-epi
  : ∀ {f : ℬ.Hom b a}
  → ℰ^op.weak-mono-over f a′ b′
  → ℰ.weak-epi-over f b′ a′
weak-co-mono→weak-epi f .mor′ = ℰ^op.mor′ f
weak-co-mono→weak-epi f .weak-epic = ℰ^op.weak-monic f
```

Next, sections and retractions.

```agda
co-section[]→retract[]
  : ∀ {s : ℬ^op.has-section f}
  → ℰ^op.has-section[ s ] f′
  → ℰ.has-retract[ co-section→retract s ] f′
co-section[]→retract[] f .retract′ =
  ℰ^op.section′ f
co-section[]→retract[] f .is-retract′ =
  ℰ^op.is-section′ f

retract[]→co-section[]
  : ∀ {r : ℬ.has-retract f}
  → ℰ.has-retract[ r ] f′
  → ℰ^op.has-section[ retract→co-section r ] f′
retract[]→co-section[] f .section′ =
  ℰ.retract′ f
retract[]→co-section[] f .is-section′ =
  ℰ.is-retract′ f

co-retract[]→section[]
  : ∀ {r : ℬ^op.has-retract f}
  → ℰ^op.has-retract[ r ] f′
  → ℰ.has-section[ co-retract→section r ] f′
co-retract[]→section[] f .section′ =
  ℰ^op.retract′ f
co-retract[]→section[] f .is-section′ =
  ℰ^op.is-retract′ f

section[]→co-retract[]
  : ∀ {s : ℬ.has-section f}
  → ℰ.has-section[ s ] f′
  → ℰ^op.has-retract[ section→co-retract s ] f′
section[]→co-retract[] f .retract′ =
  ℰ.section′ f
section[]→co-retract[] f .is-retract′ =
  ℰ.is-section′ f
```

We handle vertical sections and retract separately.

```agda
vertical-co-section→vertical-retract
  : ℰ^op.has-section↓ f′
  → ℰ.has-retract↓ f′
vertical-co-section→vertical-retract f .retract′ =
  ℰ^op.section′ f
vertical-co-section→vertical-retract f .is-retract′ =
  cast[] (ℰ^op.is-section′ f)

vertical-retract→vertical-co-section
  : ℰ.has-retract↓ f′
  → ℰ^op.has-section↓ f′
vertical-retract→vertical-co-section f .section′ =
  ℰ.retract′ f
vertical-retract→vertical-co-section f .is-section′ =
  cast[] (ℰ.is-retract′ f)

vertical-co-retract→vertical-section
  : ℰ^op.has-retract↓ f′
  → ℰ.has-section↓ f′
vertical-co-retract→vertical-section f .section′ =
  ℰ^op.retract′ f
vertical-co-retract→vertical-section f .is-section′ =
  cast[] (ℰ^op.is-retract′ f)

vertical-section→vertical-co-retract
  : ℰ.has-section↓ f′
  → ℰ^op.has-retract↓ f′
vertical-section→vertical-co-retract f .retract′ =
  ℰ.section′ f
vertical-section→vertical-co-retract f .is-retract′ =
  cast[] (ℰ.is-section′ f)
```

Now, on to self-duality for invertible morphisms.

```agda
co-inverses[]→inverses[]
  : {i : ℬ^op.Inverses f g}
  → ℰ^op.Inverses[ i ] f′ g′
  → ℰ.Inverses[ co-inverses→inverses i ] f′ g′
co-inverses[]→inverses[] i .Inverses[_].invl′ =
  ℰ^op.Inverses[_].invr′ i
co-inverses[]→inverses[] i .Inverses[_].invr′ =
  ℰ^op.Inverses[_].invl′ i

inverses[]→co-inverses[]
  : {i : ℬ.Inverses f g}
  → ℰ.Inverses[ i ] f′ g′
  → ℰ^op.Inverses[ inverses→co-inverses i ] f′ g′
inverses[]→co-inverses[] i .Inverses[_].invl′ =
  ℰ.Inverses[_].invr′ i
inverses[]→co-inverses[] i .Inverses[_].invr′ =
  ℰ.Inverses[_].invl′ i

co-invertible[]→invertible[]
  : {i : ℬ^op.is-invertible f}
  → ℰ^op.is-invertible[ i ] f′
  → ℰ.is-invertible[ co-invertible→invertible i ] f′
co-invertible[]→invertible[] i .is-invertible[_].inv′ =
  ℰ^op.is-invertible[_].inv′ i
co-invertible[]→invertible[] i .is-invertible[_].inverses′ =
  co-inverses[]→inverses[] (ℰ^op.is-invertible[_].inverses′ i)

invertible[]→co-invertible[]
  : {i : ℬ.is-invertible f}
  → ℰ.is-invertible[ i ] f′
  → ℰ^op.is-invertible[ invertible→co-invertible i ] f′
invertible[]→co-invertible[] i .is-invertible[_].inv′ =
  ℰ.is-invertible[_].inv′ i
invertible[]→co-invertible[] i .is-invertible[_].inverses′ =
  inverses[]→co-inverses[] (ℰ.is-invertible[_].inverses′ i)

co-iso[]→iso[]
  : {f : a ℬ^op.≅ b}
  → a′ ℰ^op.≅[ f ] b′
  → b′ ℰ.≅[ co-iso→iso f ] a′
co-iso[]→iso[] f .to′ =
  ℰ^op.to′ f
co-iso[]→iso[] f .from′ =
  ℰ^op.from′ f
co-iso[]→iso[] f .inverses′ =
  co-inverses[]→inverses[] (ℰ^op.inverses′ f)

iso[]→co-iso[]
  : {f : b ℬ.≅ a}
  → b′ ℰ.≅[ f ] a′
  → a′ ℰ^op.≅[ iso→co-iso f ] b′
iso[]→co-iso[] f .to′ =
  ℰ.to′ f
iso[]→co-iso[] f .from′ =
  ℰ.from′ f
iso[]→co-iso[] f .inverses′ =
  inverses[]→co-inverses[] (ℰ.inverses′ f)
```

We handle the case of vertical isos separately, as the dual of the identity
iso isn't definitionally the identity iso.

```agda
vertical-co-invertible→vertical-invertible
  : ℰ^op.is-invertible↓ f′ → ℰ.is-invertible↓ f′
vertical-co-invertible→vertical-invertible f =
  ℰ.make-invertible↓
    (ℰ^op.is-invertible[_].inv′ f)
    (cast[] (ℰ^op.is-invertible[_].invr′ f))
    (cast[] (ℰ^op.is-invertible[_].invl′ f))

vertical-invertible→vertical-co-invertible
  : ℰ.is-invertible↓ f′ → ℰ^op.is-invertible↓ f′
vertical-invertible→vertical-co-invertible f =
  ℰ^op.make-invertible↓
    (ℰ.is-invertible[_].inv′ f)
    (cast[] (ℰ.is-invertible[_].invr′ f))
    (cast[] (ℰ.is-invertible[_].invl′ f))

vertical-co-iso→vertical-iso : a′ ℰ^op.≅↓ b′ → b′ ℰ.≅↓ a′
vertical-co-iso→vertical-iso f =
  ℰ.make-vertical-iso
    (ℰ^op.to′ f)
    (ℰ^op.from′ f)
    (cast[] (ℰ^op.invr′ f))
    (cast[] (ℰ^op.invl′ f))

vertical-iso→vertical-co-iso : a′ ℰ.≅↓ b′ → b′ ℰ^op.≅↓ a′
vertical-iso→vertical-co-iso f =
  ℰ^op.make-vertical-iso
    (ℰ.to′ f)
    (ℰ.from′ f)
    (cast[] (ℰ.invr′ f))
    (cast[] (ℰ.invl′ f))
```
