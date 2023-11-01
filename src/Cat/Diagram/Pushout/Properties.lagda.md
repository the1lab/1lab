<!--
```agda
open import Cat.Prelude

import Cat.Diagram.Pushout
import Cat.Reasoning
```
-->

```agda
module Cat.Diagram.Pushout.Properties {o ℓ} {C : Precategory o ℓ} where
```

<!--
```agda
open Cat.Diagram.Pushout C
open Cat.Reasoning C
open is-pushout

```
-->

## Epimorphisms

$f : A \to B$ is an epimorphism iff. the square below is a pushout

~~~{.quiver}
\[\begin{tikzcd}
  a && b \\
  \\
  b && b
  \arrow["{\mathrm{id}}", from=1-3, to=3-3]
  \arrow["{\mathrm{id}}"', from=3-1, to=3-3]
  \arrow["f", from=1-1, to=1-3]
  \arrow["f"', from=1-1, to=3-1]
\end{tikzcd}\]
~~~

```agda
module _ {a b} {f : Hom a b} where
  is-epic→is-pushout : is-epic f → is-pushout f id f id
  is-epic→is-pushout epi .square = refl
  is-epic→is-pushout epi .universal {i₁' = i₁'} p = i₁'
  is-epic→is-pushout epi .i₁∘universal = idr _
  is-epic→is-pushout epi .i₂∘universal {p = p} = idr _ ∙ epi _ _ p
  is-epic→is-pushout epi .unique p q = intror refl ∙ p

  is-pushout→is-epic : is-pushout f id f id → is-epic f
  is-pushout→is-epic pb g h p = sym (pb .i₁∘universal {p = p}) ∙ pb .i₂∘universal
```

Pushout additionally preserve epimorphisms, as shown below:

```agda
is-epic→pushout-is-epic
  : ∀ {x y z} {f : Hom x y} {g : Hom x z} {p} {i₁ : Hom y p} {i₂ : Hom z p}
  → is-epic f
  → is-pushout f i₁ g i₂
  → is-epic i₂
is-epic→pushout-is-epic {f = f} {g} {i₁ = i₁} {i₂} epi pb h j p = eq
  where
    module pb = is-pushout pb

    q : (h ∘ i₁) ∘ f  ≡ (j ∘ i₁) ∘ f
    q =
      (h ∘ i₁) ∘ f ≡⟨ extendr pb.square ⟩
      (h ∘ i₂) ∘ g ≡⟨ ap (_∘ g) p ⟩
      (j ∘ i₂) ∘ g ≡˘⟨ extendr pb.square ⟩
      (j ∘ i₁) ∘ f ∎

    r : h ∘ i₁ ≡ j ∘ i₁
    r = epi _ _ q

    eq : h ≡ j
    eq = pb.unique₂ {p = extendr pb.square} r p refl refl
```
