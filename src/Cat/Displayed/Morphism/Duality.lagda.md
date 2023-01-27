```agda
open import Cat.Displayed.Base
open import Cat.Displayed.Total.Op
open import Cat.Prelude

import Cat.Morphism
import Cat.Morphism.Duality
import Cat.Displayed.Morphism
import Cat.Displayed.Reasoning

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

  open Displayed ℰ
  open Cat.Morphism.Duality ℬ
  open Cat.Displayed.Reasoning ℰ

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
There is *even less* mathematical content here than the non-displayed
case, just mountains of boilerplate.

We start by showing that displayed monos and epis are dual.

```agda
monic[]^op→epic[]
  : ∀ {f : a ℬ^op.↪ b}
  → a′ ℰ^op.↪[ f ] b′
  → b′ ℰ.↠[ monic^op→epic f ] a′
monic[]^op→epic[] f .Cat.Displayed.Morphism.mor′ =
  ℰ^op.mor′ f
monic[]^op→epic[] f .Cat.Displayed.Morphism.epic′ =
  ℰ^op.monic′ f

epic[]→monic[]^op
  : ∀ {f : b ℬ.↠ a}
  → b′ ℰ.↠[ f ] a′
  → a′ ℰ^op.↪[ epic→monic^op f ] b′
epic[]→monic[]^op f .Cat.Displayed.Morphism.mor′ =
  ℰ.mor′ f
epic[]→monic[]^op f .Cat.Displayed.Morphism.monic′ =
  ℰ.epic′ f

epic[]^op→monic[]
  : ∀ {f : a ℬ^op.↠ b}
  → a′ ℰ^op.↠[ f ] b′
  → b′ ℰ.↪[ epic^op→monic f ] a′
epic[]^op→monic[] f .Cat.Displayed.Morphism.mor′ =
  ℰ^op.mor′ f
epic[]^op→monic[] f .Cat.Displayed.Morphism.monic′ =
  ℰ^op.epic′ f

monic[]→epic[]^op
  : ∀ {f : b ℬ.↪ a}
  → b′ ℰ.↪[ f ] a′
  → a′ ℰ^op.↠[ monic→epic^op f ] b′
monic[]→epic[]^op f .Cat.Displayed.Morphism.mor′ =
  ℰ.mor′ f
monic[]→epic[]^op f .Cat.Displayed.Morphism.epic′ =
  ℰ.monic′ f
```

Next, we show the same for weak monos and weak epis.

```agda
weak-monic→weak-epic^op
  : ∀ {f : ℬ.Hom b a}
  → b′ ℰ.↪[ f ]ʷ a′
  → a′ ℰ^op.↠[ f ]ʷ b′
weak-monic→weak-epic^op f .Cat.Displayed.Morphism.mor′ =
  ℰ.mor′ f
weak-monic→weak-epic^op f .Cat.Displayed.Morphism.weak-epic =
  ℰ.weak-monic f

weak-epic^op→weak-monic
  : ∀ {f : ℬ.Hom b a}
  → a′ ℰ^op.↠[ f ]ʷ b′
  → b′ ℰ.↪[ f ]ʷ a′
weak-epic^op→weak-monic f .Cat.Displayed.Morphism.mor′ =
  ℰ^op.mor′ f
weak-epic^op→weak-monic f .Cat.Displayed.Morphism.weak-monic =
  ℰ^op.weak-epic f

weak-epic→weak-monic^op
  : ∀ {f : ℬ.Hom b a}
  → b′ ℰ.↠[ f ]ʷ a′
  → a′ ℰ^op.↪[ f ]ʷ b′
weak-epic→weak-monic^op f .Cat.Displayed.Morphism.mor′ =
  ℰ.mor′ f
weak-epic→weak-monic^op f .Cat.Displayed.Morphism.weak-monic =
  ℰ.weak-epic f

weak-monic^op→weak-epic
  : ∀ {f : ℬ.Hom b a}
  → a′ ℰ^op.↪[ f ]ʷ b′
  → b′ ℰ.↠[ f ]ʷ a′
weak-monic^op→weak-epic f .Cat.Displayed.Morphism.mor′ =
  ℰ^op.mor′ f
weak-monic^op→weak-epic f .Cat.Displayed.Morphism.weak-epic =
  ℰ^op.weak-monic f
```

Next, sections and retractions.

```agda
section[]^op→retract[]
  : ∀ {s : ℬ^op.has-section f}
  → ℰ^op.has-section[ s ] f′
  → ℰ.has-retract[ section^op→retract s ] f′
section[]^op→retract[] f .Cat.Displayed.Morphism.retract′ =
  ℰ^op.section′ f
section[]^op→retract[] f .Cat.Displayed.Morphism.is-retract′ =
  ℰ^op.is-section′ f

retract[]→section[]^op 
  : ∀ {r : ℬ.has-retract f}
  → ℰ.has-retract[ r ] f′
  → ℰ^op.has-section[ retract→section^op r ] f′
retract[]→section[]^op f .Cat.Displayed.Morphism.section′ =
  ℰ.retract′ f
retract[]→section[]^op f .Cat.Displayed.Morphism.is-section′ =
  ℰ.is-retract′ f

retract[]^op→section[]
  : ∀ {r : ℬ^op.has-retract f}
  → ℰ^op.has-retract[ r ] f′
  → ℰ.has-section[ retract^op→section r ] f′
retract[]^op→section[] f .Cat.Displayed.Morphism.section′ =
  ℰ^op.retract′ f
retract[]^op→section[] f .Cat.Displayed.Morphism.is-section′ =
  ℰ^op.is-retract′ f

section[]→retract[]^op
  : ∀ {s : ℬ.has-section f}
  → ℰ.has-section[ s ] f′
  → ℰ^op.has-retract[ section→retract^op s ] f′
section[]→retract[]^op f .Cat.Displayed.Morphism.retract′ =
  ℰ.section′ f
section[]→retract[]^op f .Cat.Displayed.Morphism.is-retract′ =
  ℰ.is-section′ f
```

We handle vertical sections and retract separately.

```agda
vert-section^op→vert-retract
  : ℰ^op.has-section↓ f′
  → ℰ.has-retract↓ f′
vert-section^op→vert-retract f .Cat.Displayed.Morphism.retract′ =
  ℰ^op.section′ f
vert-section^op→vert-retract f .Cat.Displayed.Morphism.is-retract′ =
  cast[] (ℰ^op.is-section′ f)

vert-retract→vert-section^op
  : ℰ.has-retract↓ f′
  → ℰ^op.has-section↓ f′
vert-retract→vert-section^op f .Cat.Displayed.Morphism.section′ =
  ℰ.retract′ f
vert-retract→vert-section^op f .Cat.Displayed.Morphism.is-section′ =
  cast[] (ℰ.is-retract′ f)

vert-retract^op→vert-section
  : ℰ^op.has-retract↓ f′
  → ℰ.has-section↓ f′
vert-retract^op→vert-section f .Cat.Displayed.Morphism.section′ =
  ℰ^op.retract′ f
vert-retract^op→vert-section f .Cat.Displayed.Morphism.is-section′ =
  cast[] (ℰ^op.is-retract′ f)

vert-section→vert-retract^op
  : ℰ.has-section↓ f′
  → ℰ^op.has-retract↓ f′
vert-section→vert-retract^op f .Cat.Displayed.Morphism.retract′ =
  ℰ.section′ f
vert-section→vert-retract^op f .Cat.Displayed.Morphism.is-retract′ =
  cast[] (ℰ.is-section′ f)
```

Now, on to self-duality for invertible morphisms.

```agda
inverses[]^op→inverses[]
  : {i : ℬ^op.Inverses f g}
  → ℰ^op.Inverses[ i ] f′ g′
  → ℰ.Inverses[ inverses^op→inverses i ] f′ g′
inverses[]^op→inverses[] i .Cat.Displayed.Morphism.Inverses[_].invl′ =
  ℰ^op.Inverses[_].invr′ i
inverses[]^op→inverses[] i .Cat.Displayed.Morphism.Inverses[_].invr′ =
  ℰ^op.Inverses[_].invl′ i

inverses[]→inverses[]^op
  : {i : ℬ.Inverses f g}
  → ℰ.Inverses[ i ] f′ g′
  → ℰ^op.Inverses[ inverses→inverses^op i ] f′ g′
inverses[]→inverses[]^op i .Cat.Displayed.Morphism.Inverses[_].invl′ =
  ℰ.Inverses[_].invr′ i
inverses[]→inverses[]^op i .Cat.Displayed.Morphism.Inverses[_].invr′ =
  ℰ.Inverses[_].invl′ i

invertible[]^op→invertible[]
  : {i : ℬ^op.is-invertible f}
  → ℰ^op.is-invertible[ i ] f′
  → ℰ.is-invertible[ invertible^op→invertible i ] f′
invertible[]^op→invertible[] i .Cat.Displayed.Morphism.is-invertible[_].inv′ =
  ℰ^op.is-invertible[_].inv′ i
invertible[]^op→invertible[] i .Cat.Displayed.Morphism.is-invertible[_].inverses′ =
  inverses[]^op→inverses[] (ℰ^op.is-invertible[_].inverses′ i)

invertible[]→invertible[]^op
  : {i : ℬ.is-invertible f}
  → ℰ.is-invertible[ i ] f′
  → ℰ^op.is-invertible[ invertible→invertible^op i ] f′
invertible[]→invertible[]^op i .Cat.Displayed.Morphism.is-invertible[_].inv′ =
  ℰ.is-invertible[_].inv′ i
invertible[]→invertible[]^op i .Cat.Displayed.Morphism.is-invertible[_].inverses′ =
  inverses[]→inverses[]^op (ℰ.is-invertible[_].inverses′ i)

iso[]^op→iso[]
  : {f : a ℬ^op.≅ b}
  → a′ ℰ^op.≅[ f ] b′
  → b′ ℰ.≅[ iso^op→iso f ] a′
iso[]^op→iso[] f .Cat.Displayed.Morphism.to′ =
  ℰ^op.to′ f
iso[]^op→iso[] f .Cat.Displayed.Morphism.from′ =
  ℰ^op.from′ f
iso[]^op→iso[] f .Cat.Displayed.Morphism.inverses′ =
  inverses[]^op→inverses[] (ℰ^op.inverses′ f)

iso[]→iso[]^op
  : {f : b ℬ.≅ a}
  → b′ ℰ.≅[ f ] a′
  → a′ ℰ^op.≅[ iso→iso^op f ] b′
iso[]→iso[]^op f .Cat.Displayed.Morphism.to′ =
  ℰ.to′ f
iso[]→iso[]^op f .Cat.Displayed.Morphism.from′ =
  ℰ.from′ f
iso[]→iso[]^op f .Cat.Displayed.Morphism.inverses′ =
  inverses[]→inverses[]^op (ℰ.inverses′ f)
```

We handle the case of vertical isos separately, as the dual of the identity
iso isn't definitionally the identity iso.

```agda
vert-invertible^op→vert-invertible : ℰ^op.is-invertible↓ f′ → ℰ.is-invertible↓ f′
vert-invertible^op→vert-invertible f =
  ℰ.make-invertible↓
    (ℰ^op.is-invertible[_].inv′ f)
    (cast[] (ℰ^op.is-invertible[_].invr′ f))
    (cast[] (ℰ^op.is-invertible[_].invl′ f))

vert-invertible→vert-invertible^op : ℰ.is-invertible↓ f′ → ℰ^op.is-invertible↓ f′
vert-invertible→vert-invertible^op f =
  ℰ^op.make-invertible↓
    (ℰ.is-invertible[_].inv′ f)
    (cast[] (ℰ.is-invertible[_].invr′ f))
    (cast[] (ℰ.is-invertible[_].invl′ f))

vert-iso^op→vert-iso : a′ ℰ^op.≅↓ b′ → b′ ℰ.≅↓ a′
vert-iso^op→vert-iso f =
  ℰ.make-vert-iso
    (ℰ^op.to′ f)
    (ℰ^op.from′ f)
    (cast[] (ℰ^op.invr′ f))
    (cast[] (ℰ^op.invl′ f))

vert-iso→vert-iso^op : a′ ℰ.≅↓ b′ → b′ ℰ^op.≅↓ a′
vert-iso→vert-iso^op f =
  ℰ^op.make-vert-iso
    (ℰ.to′ f)
    (ℰ.from′ f)
    (cast[] (ℰ.invr′ f))
    (cast[] (ℰ.invl′ f))
```

