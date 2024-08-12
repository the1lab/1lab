<!--
```agda
open import Cat.Prelude

import Cat.Reasoning
```
-->

```agda
module Cat.Diagram.Pushout where
```

# Pushouts {defines="pushout"}

<!--
```agda
module _ {o ℓ} (C : Precategory o ℓ) where
  open Cat.Reasoning C
  private variable
    Q X Y Z : Ob
    h i₁' i₂' : Hom X Y
```
-->

A **pushout** $Y +_X Z$ of $f : X \to Y$ and $g : X \to Z$ is the
dual construction to the [[pullback]]. Much like the [[pullback]] is a
subobject of the [[product]], the pushout is a quotient object of the
[coproduct]. The maps $f$ and $g$ tell us which parts of the [coproduct]
to identify.

[pullback]: Cat.Diagram.Pullback.html
[coproduct]: Cat.Diagram.Coproduct.html

```agda
  record is-pushout {P} (f : Hom X Y) (i₁ : Hom Y P) (g : Hom X Z) (i₂ : Hom Z P)
    : Type (o ⊔ ℓ) where
      field
        square     : i₁ ∘ f ≡ i₂ ∘ g
```

The most important part of the pushout is a commutative square of the
following shape:

~~~{.quiver}
\[\begin{tikzcd}
  X & Z \\
  Y & P
  \arrow["f"', from=1-1, to=2-1]
  \arrow["{i_1}", from=2-1, to=2-2]
  \arrow["g", from=1-1, to=1-2]
  \arrow["{i_2}"', from=1-2, to=2-2]
\end{tikzcd}\]
~~~

This can be thought of as providing "gluing instructions".
The injection maps $i_1$ and $i_2$ embed $Y$ and $Z$ into $P$,
and the maps $f$ and $g$ determine what parts of $Y$ and $Z$ we
ought to identify in $P$.

The universal property ensures that we only perform the minimal number
of identifications required to make the aforementioned square commute.

```agda
        universal : ∀ {Q} {i₁' : Hom Y Q} {i₂' : Hom Z Q}
                   → i₁' ∘ f ≡ i₂' ∘ g → Hom P Q
        universal∘i₁ : {p : i₁' ∘ f ≡ i₂' ∘ g} → universal p ∘ i₁ ≡ i₁'
        universal∘i₂ : {p : i₁' ∘ f ≡ i₂' ∘ g} → universal p ∘ i₂ ≡ i₂'

        unique : {p : i₁' ∘ f ≡ i₂' ∘ g} {colim' : Hom P Q}
               → colim' ∘ i₁ ≡ i₁'
               → colim' ∘ i₂ ≡ i₂'
               → colim' ≡ universal p

      unique₂
        : {p : i₁' ∘ f ≡ i₂' ∘ g} {colim' colim'' : Hom P Q}
        → colim' ∘ i₁ ≡ i₁' → colim' ∘ i₂ ≡ i₂'
        → colim'' ∘ i₁ ≡ i₁' → colim'' ∘ i₂ ≡ i₂'
        → colim' ≡ colim''
      unique₂ {p = o} p q r s = unique {p = o} p q ∙ sym (unique r s)
```

We provide a convenient packaging of the pushout and the injection
maps:

```agda
  record Pushout (f : Hom X Y) (g : Hom X Z) : Type (o ⊔ ℓ) where
    field
      {coapex} : Ob
      i₁       : Hom Y coapex
      i₂       : Hom Z coapex
      has-is-po  : is-pushout f i₁ g i₂

    open is-pushout has-is-po public
```

# Categories with all pushouts

```agda
record Pushouts {o ℓ} (C : Precategory o ℓ) : Type (o ⊔ ℓ) where
  no-eta-equality
  open Cat.Reasoning C
  field
    Po : ∀ {X Y Z} → Hom X Y → Hom X Z → Ob
    i₁ : ∀ {X Y Z} (f : Hom X Y) (g : Hom X Z) → Hom Y (Po f g)
    i₂ : ∀ {X Y Z} (f : Hom X Y) (g : Hom X Z) → Hom Z (Po f g)
    cosquare
      : ∀ {X Y Z} {f : Hom X Y} {g : Hom X Z}
      → i₁ f g ∘ f ≡ i₂ f g ∘ g
    po
      : ∀ {P X Y Z} {f : Hom X Y} {g : Hom X Z}
      → (i1 : Hom Y P) (i2 : Hom Z P)
      → i1 ∘ f ≡ i2 ∘ g
      → Hom (Po f g) P
    po∘i₁
      : ∀ {P X Y Z} {f : Hom X Y} {g : Hom X Z}
      → {i1 : Hom Y P} {i2 : Hom Z P}
      → {sq : i1 ∘ f ≡ i2 ∘ g}
      → po i1 i2 sq ∘ i₁ f g ≡ i1
    po∘i₂
      : ∀ {P X Y Z} {f : Hom X Y} {g : Hom X Z}
      → {i1 : Hom Y P} {i2 : Hom Z P}
      → {sq : i1 ∘ f ≡ i2 ∘ g}
      → po i1 i2 sq ∘ i₂ f g ≡ i2
    po-unique
      : ∀ {P X Y Z} {f : Hom X Y} {g : Hom X Z}
      → {i1 : Hom Y P} {i2 : Hom Z P}
      → {sq : i1 ∘ f ≡ i2 ∘ g}
      → {other : Hom (Po f g) P}
      → other ∘ i₁ f g ≡ i1
      → other ∘ i₂ f g ≡ i2
      → other ≡ po i1 i2 sq
```

<!--
```agda
  pushout : ∀ {X Y Z} (f : Hom X Y) (g : Hom X Z) → Pushout C f g
  pushout f g .Pushout.coapex = Po f g
  pushout f g .Pushout.i₁ = i₁ f g
  pushout f g .Pushout.i₂ = i₂ f g
  pushout f g .Pushout.has-is-po .is-pushout.square = cosquare
  pushout f g .Pushout.has-is-po .is-pushout.universal = po _ _
  pushout f g .Pushout.has-is-po .is-pushout.universal∘i₁ = po∘i₁
  pushout f g .Pushout.has-is-po .is-pushout.universal∘i₂ = po∘i₂
  pushout f g .Pushout.has-is-po .is-pushout.unique = po-unique

  private module pushout {X Y Z} {f : Hom X Y} {g : Hom X Z} = Pushout (pushout f g)
  open pushout
    renaming (unique₂ to po-unique₂)
    using (has-is-po)
    public

module _ {o ℓ} {C : Precategory o ℓ} where
  open Precategory C

  all-pushouts→pushouts
    : (∀ {X Y Z} (f : Hom X Y) (g : Hom X Z) → Pushout C f g)
    → Pushouts C
  all-pushouts→pushouts all-pushouts = pushouts where
    module po {X Y Z} {f : Hom X Y} {g : Hom X Z} = Pushout (all-pushouts f g)

    pushouts : Pushouts C
    pushouts .Pushouts.Po f g = po.coapex {f = f} {g = g}
    pushouts .Pushouts.i₁ _ _ = po.i₁
    pushouts .Pushouts.i₂ _ _ = po.i₂
    pushouts .Pushouts.cosquare = po.square
    pushouts .Pushouts.po _ _ = po.universal
    pushouts .Pushouts.po∘i₁ = po.universal∘i₁
    pushouts .Pushouts.po∘i₂ = po.universal∘i₂
    pushouts .Pushouts.po-unique = po.unique

  has-pushouts→pushouts
    : {Po : ∀ {X Y Z} (f : Hom X Y) (g : Hom X Z) → Ob}
    → {i₁ : ∀ {X Y Z} (f : Hom X Y) (g : Hom X Z) → Hom Y (Po f g)}
    → {i₂ : ∀ {X Y Z} (f : Hom X Y) (g : Hom X Z) → Hom Z (Po f g)}
    → (∀ {X Y Z} (f : Hom X Y) (g : Hom X Z) → is-pushout C f (i₁ f g) g (i₂ f g))
    → Pushouts C
  has-pushouts→pushouts {Po = Po} {i₁} {i₂} has-pushouts = pushouts where
    module po {X Y Z} {f : Hom X Y} {g : Hom X Z} = is-pushout (has-pushouts f g)

    pushouts : Pushouts C
    pushouts .Pushouts.Po = Po
    pushouts .Pushouts.i₁ = i₁
    pushouts .Pushouts.i₂ = i₂
    pushouts .Pushouts.cosquare = po.square
    pushouts .Pushouts.po _ _ = po.universal
    pushouts .Pushouts.po∘i₁ = po.universal∘i₁
    pushouts .Pushouts.po∘i₂ = po.universal∘i₂
    pushouts .Pushouts.po-unique = po.unique
```
-->
