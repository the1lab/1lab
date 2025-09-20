<!--
```agda
open import Cat.Diagram.Pushout
open import Cat.Prelude

import Cat.Reasoning
```
-->

```agda
module Cat.Diagram.Pushout.Properties where
```

<!--
```agda
module _ {o ℓ} {C : Precategory o ℓ} where
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
    is-epic→is-pushout : is-epic f → is-pushout C f id f id
    is-epic→is-pushout epi .square = refl
    is-epic→is-pushout epi .universal {i₁' = i₁'} p = i₁'
    is-epic→is-pushout epi .universal∘i₁ = idr _
    is-epic→is-pushout epi .universal∘i₂ {p = p} = idr _ ∙ epi _ _ p
    is-epic→is-pushout epi .unique p q = intror refl ∙ p

    is-pushout→is-epic : is-pushout C f id f id → is-epic f
    is-pushout→is-epic po g h p = sym (po .universal∘i₁ {p = p}) ∙ po .universal∘i₂
```

Pushout additionally preserve epimorphisms, as shown below:

```agda
  is-epic→pushout-is-epic
    : ∀ {x y z} {f : Hom x y} {g : Hom x z} {p} {i₁ : Hom y p} {i₂ : Hom z p}
    → is-epic f
    → is-pushout C f i₁ g i₂
    → is-epic i₂
  is-epic→pushout-is-epic {f = f} {g} {i₁ = i₁} {i₂} epi po h j p = eq
    where
      module po = is-pushout po

      q : (h ∘ i₁) ∘ f  ≡ (j ∘ i₁) ∘ f
      q =
        (h ∘ i₁) ∘ f ≡⟨ extendr po.square ⟩
        (h ∘ i₂) ∘ g ≡⟨ ap (_∘ g) p ⟩
        (j ∘ i₂) ∘ g ≡˘⟨ extendr po.square ⟩
        (j ∘ i₁) ∘ f ∎

      r : h ∘ i₁ ≡ j ∘ i₁
      r = epi _ _ q

      eq : h ≡ j
      eq = po.unique₂ {p = extendr po.square} r p refl refl
```
## Identity is pushout

If $\iota_1=\iota_2$, then the identity is a pushout.

~~~{.quiver}
\[\begin{tikzcd}
	a & b \\
	b & {b\sqcup_a b} \\
	& {} & b
	\arrow["f", from=1-1, to=1-2]
	\arrow["f"', from=1-1, to=2-1]
	\arrow["{\iota_1}", from=1-2, to=2-2]
	\arrow["{\mathrm{id}}", curve={height=-18pt}, from=1-2, to=3-3]
	\arrow["{\iota_2}"', from=2-1, to=2-2]
	\arrow["{\mathrm{id}}"', curve={height=18pt}, from=2-1, to=3-3]
	\arrow["\lrcorner"{anchor=center, pos=0.125, rotate=180}, draw=none, from=2-2, to=1-1]
\end{tikzcd}\]
~~~

```agda
  module _ {x y} {f : Hom x y} {p} {i₁ : Hom y p} {i₂ : Hom y p}
      (po : is-pushout C f i₁ f i₂) (eq : i₁ ≡ i₂) where
    private
      module po = is-pushout po
    injections-eq→id-is-pushout : is-pushout C f id f id
    injections-eq→id-is-pushout .square = refl
    injections-eq→id-is-pushout .universal p  = po .universal p ∘ i₁
    injections-eq→id-is-pushout .universal∘i₁ = idr _ ∙ po .universal∘i₁
    injections-eq→id-is-pushout .universal∘i₂ = idr _ ∙ ap (_ ∘_) eq
      ∙ po .universal∘i₂
    injections-eq→id-is-pushout .unique {a} {f'} {g'} {p = sq} {c} p₁ p₂  =
      c                    ≡⟨ insertr i⁻¹∘i₁≡id ⟩
      (c ∘ i⁻¹) ∘ i₁       ≡⟨ po .unique {colim' = c ∘ i⁻¹} (pullr i⁻¹∘i₁≡id ∙ p₁) (pullr i⁻¹∘i₂≡id ∙ p₂) ⟩∘⟨refl ⟩
      po.universal sq ∘ i₁ ∎
      where i⁻¹ : Hom p y
            i⁻¹ = universal po $ idl f ∙ sym (idl f)
            i⁻¹∘i₁≡id : i⁻¹ ∘ i₁ ≡ id
            i⁻¹∘i₁≡id = po.universal∘i₁
            i⁻¹∘i₂≡id : i⁻¹ ∘ i₂ ≡ id
            i⁻¹∘i₂≡id = ap (i⁻¹ ∘_) (sym eq) ∙ i⁻¹∘i₁≡id

    injections-eq→is-epic : is-epic f
    injections-eq→is-epic = is-pushout→is-epic injections-eq→id-is-pushout
```
