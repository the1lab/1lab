<!--
```agda
open import Cat.Prelude
```
-->

```agda
module Cat.Diagram.Pushout {o ℓ} (C : Precategory o ℓ) where

```

# Pushouts {defines="pushout"}

<!--
```agda
open Precategory C
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
      i₁∘universal : {p : i₁' ∘ f ≡ i₂' ∘ g} → universal p ∘ i₁ ≡ i₁'
      i₂∘universal : {p : i₁' ∘ f ≡ i₂' ∘ g} → universal p ∘ i₂ ≡ i₂'

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
