<!--
```agda
open import Cat.Prelude

import Cat.Internal.Base as Internal
import Cat.Reasoning
```
-->

```agda
module Cat.Internal.Reasoning
  {o ℓ} {C : Precategory o ℓ}
  (ℂ : Internal.Internal-cat C)
  where
```

<!--
```agda
open Cat.Reasoning C
open Internal C
open Internal-cat ℂ public
open Internal-hom
```
-->

# Reasoning in internal categories

The combinators in this module mirror those in the [category reasoning]
module, so we will not comment on them too much.

[category reasoning]: Cat.Reasoning.html

<!--
```agda
private variable
  Γ Δ : Ob
  x x' y y' z z' : Hom Γ C₀
  a b c d f g h i : Homi x y
  σ : Hom Γ Δ
```
-->

## Identity morphisms

```agda
abstract
  id-commi : ∀ {f : Homi x y} → f ∘i idi x ≡ idi y ∘i f
  id-commi {f = f} = idri f ∙ sym (idli f)

  id-comm-symi : ∀ {f : Homi x y} → idi y ∘i f ≡ f ∘i idi x
  id-comm-symi {f = f} = idli f ∙ sym (idri f)

module _ {a : Homi x x} (p : a ≡ idi x) where abstract
  elimli : a ∘i f ≡ f
  elimli {f = f} = ap (_∘i f) p ∙ idli _

  elimri : f ∘i a ≡ f
  elimri {f = f} = ap (f ∘i_) p ∙ idri _

  elim-inneri : f ∘i a ∘i h ≡ f ∘i h
  elim-inneri {f = f} = ap (f ∘i_) elimli

  introli : f ≡ a ∘i f
  introli = sym elimli

  introri : f ≡ f ∘i a
  introri = sym elimri
```

## Reassociations

```agda
module _ (p : a ∘i b ≡ c) where abstract
  pullli : a ∘i (b ∘i f) ≡ c ∘i f
  pullli {f = f} = associ _ _ _ ∙ ap (_∘i f) p

  pullri : (f ∘i a) ∘i b ≡ f ∘i c
  pullri {f = f} = sym (associ _ _ _) ∙ ap (f ∘i_) p

module _ (p : c ≡ a ∘i b) where abstract
  pushli : c ∘i f ≡ a ∘i (b ∘i f)
  pushli = sym (pullli (sym p))

  pushri : f ∘i c ≡ (f ∘i a) ∘i b
  pushri = sym (pullri (sym p))

module _ (p : f ∘i h ≡ g ∘i i) where abstract
  extendli : f ∘i (h ∘i b) ≡ g ∘i (i ∘i b)
  extendli {b = b} =
    associ _ _ _
    ·· ap (_∘i b) p
    ·· sym (associ _ _ _)

  extendri : (a ∘i f) ∘i h ≡ (a ∘i g) ∘i i
  extendri {a = a} =
    sym (associ _ _ _)
    ·· ap (a ∘i_) p
    ·· associ _ _ _

  extend-inneri : a ∘i f ∘i h ∘i b ≡ a ∘i g ∘i i ∘i b
  extend-inneri {a = a} = ap (a ∘i_) extendli
```

## Cancellation

```agda
module _ (inv : h ∘i i ≡ idi _) where
  cancelli : h ∘i (i ∘i f) ≡ f
  cancelli = pullli inv ∙ idli _

  cancelri : (f ∘i h) ∘i i ≡ f
  cancelri = pullri inv ∙ idri _

  insertli : f ≡ h ∘i (i ∘i f)
  insertli = sym cancelli

  insertri : f ≡ (f ∘i h) ∘i i
  insertri = sym cancelri

  deleteli : h ∘i (i ∘i f) ∘i g ≡ f ∘i  g
  deleteli = pullli cancelli

  deleteri : (f ∘i g ∘i h) ∘i i ≡ f ∘i g
  deleteri = pullri cancelri
```

## Substitutions

```agda

sub-id : ∀ {f : Homi x y} → PathP (λ i → Homi (idr x i) (idr y i)) (f [ id ]) f
sub-id = Internal-hom-pathp (idr _) (idr _) (idr _)
```

## Generalized morphisms

```agda
∘i-ihom
  : ∀ {f : Homi y z} {f' : Homi y' z'} {g : Homi x y} {g' : Homi x' y'}
  → x ≡ x' → y ≡ y' → z ≡ z'
  → f .ihom ≡ f' .ihom
  → g .ihom ≡ g' .ihom
  → (f ∘i g) .ihom ≡ (f' ∘i g') .ihom
∘i-ihom {z = z} {x = x} {f = f} {f'} {g} {g'} px py pz q r i = ∘i-ihom-filler i .ihom
  where
    ∘i-ihom-filler : (i : I) → Homi (px i) (pz i)
    ∘i-ihom-filler i =
      (Internal-hom-pathp {f = f} {g = f'} py pz q i)
      ∘i (Internal-hom-pathp {f = g} {g = g'} px py r i)
```
