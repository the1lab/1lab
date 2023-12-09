<!--
```agda
open import Cat.Diagram.Pullback.Properties
open import Cat.Prelude

import Cat.Diagram.Pullback as Pb
import Cat.Reasoning as Cat
```
-->

```agda
module Cat.Diagram.Pullback.Along {o ℓ} (C : Precategory o ℓ) where
```

<!--
```agda
open Cat C
open Pb C
```
-->

# header

```agda
record is-pullback-along {P X Y Z} (f : Hom P X) (g : Hom X Z) (h : Hom Y Z) : Type (o ⊔ ℓ) where
  no-eta-equality
  field
    top       : Hom P Y
    has-is-pb : is-pullback f g top h
  open is-pullback has-is-pb public

private unquoteDecl eqv = declare-record-iso eqv (quote is-pullback-along)

opaque
  is-monic→is-pullback-along-is-prop
    : ∀ {P X Y Z} {f : Hom P X} {g : Hom X Z} {h : Hom Y Z}
    → is-monic h
    → is-prop (is-pullback-along f g h)
  is-monic→is-pullback-along-is-prop h-monic = Iso→is-hlevel 1 eqv λ (_ , x) (_ , y) →
    Σ-prop-path! (h-monic _ _ (sym (is-pullback.square x) ∙ is-pullback.square y))

paste-is-pullback-along
  : ∀ {U V W X Y Z : Ob} {h : Hom U X} {k : Hom V Y} {l : Hom W Z} {m : Hom X Y} {n : Hom Y Z} {nm : Hom X Z}
  → is-pullback-along h m k
  → is-pullback-along k n l
  → n ∘ m ≡ nm
  → is-pullback-along h nm l
paste-is-pullback-along p q r = record
  { has-is-pb = subst-is-pullback refl r refl refl (rotate-pullback (pasting-left→outer-is-pullback
    (rotate-pullback (q .is-pullback-along.has-is-pb))
    (rotate-pullback (p .is-pullback-along.has-is-pb))
    (extendl (sym (q .is-pullback-along.square)) ∙ pushr (sym (p .is-pullback-along.square)))))
  }
```
