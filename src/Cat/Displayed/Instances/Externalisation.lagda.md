<!--
```agda
open import Cat.Displayed.Base
open import Cat.Prelude

open import Cat.Internal.Base using (Internal-cat)

import Cat.Internal.Base
import Cat.Internal.Reasoning
import Cat.Reasoning
```
-->

```agda


module Cat.Displayed.Instances.Externalisation
  {o ℓ} (B : Precategory o ℓ) (ℂ : Internal-cat B)
  where

```

<!--
```agda
open Cat.Reasoning B
open Cat.Internal.Base B
open Cat.Internal.Reasoning ℂ
open Displayed
open Internal-hom
```
-->

# Externalisation of internal categories

Every [internal category] in $\cB$ gives rise to a fibration over $\cB$,
known as the *externalisation* of the internal category.

[internal category]: Cat.Internal.Base.html

```agda
Externalize : Displayed B ℓ ℓ
Externalize = disp where
```

The core idea of externalisation is that the space of objects over
some $\Gamma : \cB$ will be the type of *generalized* objects
$\cB(\Gamma, C_0)$. This is extremely similar to the [family fibration],
but with $\cB$ playing the role of the category of sets.

Morphisms over $u : \cB(\Delta, \Gamma)$ are given by commuting diagrams
of the following form:

~~~{.quiver}
\begin{tikzcd}
  && \Delta \\
  &&& \Gamma \\
  {C_0} && {C_1} && {C_0}
  \arrow["u", from=1-3, to=2-4]
  \arrow["y", from=2-4, to=3-5]
  \arrow["f"', from=1-3, to=3-3]
  \arrow["tgt"', from=3-3, to=3-5]
  \arrow["src"', from=3-3, to=3-1]
  \arrow["x"', from=1-3, to=3-1]
\end{tikzcd}
~~~

The intuition here is that a generalized object $\cB(\Gamma, C_1)$
can be seen as a $\Gamma$-indexed family of morphisms in the internal
category. To display one of these families over a map
$u : \Delta \to \Gamma$, we simply precompose $u$ with the domain of the
internal morphism; this yields something that mirrors the morphisms in
the family fibration.

The identity morphism of families can *almost* be given by the
identity morphism, though we run into definitional equality issues.
A similar situation occurs for composition, though luckily these
issues aren't too hard to work around.

[family fibration]: Cat.Displayed.Instances.Family.html

```agda
  idi′ : ∀ {Γ} {x : Hom Γ C₀} → Homi x (x ∘ id)
  idi′ {x = x} .ihom = idi x .ihom
  idi′ {x = x} .has-src = idi x .has-src
  idi′ {x = x} .has-tgt = idi x .has-tgt ∙ sym (idr _)

  _∘i′_
    : ∀ {Γ Δ Ψ} {x : Hom Γ C₀} {y : Hom Δ C₀} {z : Hom Ψ C₀}
    → {u : Hom Δ Ψ} {v : Hom Γ Δ}
    → Homi y (z ∘ u) → Homi x (y ∘ v) → Homi x (z ∘ u ∘ v)
  _∘i′_ {u = u} {v = v} f g .ihom =  (f [ v ] ∘i g) .ihom
  _∘i′_ {u = u} {v = v} f g .has-src = (f [ v ] ∘i g) .has-src
  _∘i′_ {u = u} {v = v} f g .has-tgt = (f [ v ] ∘i g) .has-tgt ∙ sym (assoc _ _ _)

  disp : Displayed B ℓ ℓ
  disp .Ob[_] Γ = Hom Γ C₀
  disp .Hom[_] u x y = Homi x (y ∘ u)
  disp .Hom[_]-set _ _ _ = Internal-hom-set
  disp .id′ = idi′
  disp ._∘′_ = _∘i′_
```

<details>
<summary>The equations are pretty painful due to Proof Assistant Reasons.
Associativity is particularly nasty!
</summary>

```agda
  disp .idr′ f =
    Internal-hom-pathp refl (ap (_ ∘_) (idr _)) $
    (f [ id ] ∘i idi′) .ihom ≡⟨ ∘i-ihom refl (idr _) (idr _) (idr _) refl ⟩
    (f ∘i idi _) .ihom       ≡⟨ ap ihom (idri _) ⟩
    f .ihom                  ∎
  disp .idl′ {f = u} f =
    Internal-hom-pathp refl (ap (_ ∘_) (idl _)) $
      (idi′ [ u ] ∘i f) .ihom ≡⟨ ∘i-ihom refl refl (ap (_∘ _) (idr _)) (ap ihom (idi-nat u)) refl ⟩
      (idi _ ∘i f) .ihom      ≡⟨ ap ihom (idli _) ⟩
      f .ihom                 ∎
  disp .assoc′ {w = a} {b} {c} {d} {f = u} {g = v} {h = w} f g h =
    Internal-hom-pathp refl (ap (_ ∘_) (assoc _ _ _)) $
    (f [ v ∘ w ] ∘i (g ∘i′ h)) .ihom ≡⟨ ∘i-ihom refl refl refl refl (∘i-ihom refl refl (sym (assoc _ _ _)) g-path refl) ⟩
    (f [ v ∘ w ] ∘i g' ∘i h) .ihom   ≡⟨ ap ihom (associ _ _ _) ⟩
    ((f [ v ∘ w ] ∘i g') ∘i h) .ihom ≡⟨ ∘i-ihom refl refl reassoc inner refl ⟩
    ((f ∘i′ g) [ w ] ∘i h) .ihom     ∎
    where
      g' : Homi (b ∘ w) (c ∘ v ∘ w)
      g' = coe1→0 (λ i → Homi (b ∘ w) (assoc c v w i)) (g [ w ])

      g-path : g .ihom ∘ w ≡ g' .ihom
      g-path = sym (transport-refl _)

      reassoc : (d ∘ u) ∘ (v ∘ w) ≡ (d ∘ u ∘ v) ∘ w
      reassoc = pulll (sym (assoc _ _ _))

      inner : (f [ v ∘ w ] ∘i g') .ihom ≡ (f [ v ] ∘i g) .ihom ∘ w
      inner =
        (f [ v ∘ w ] ∘i g') .ihom          ≡⟨ ∘i-ihom refl (assoc _ _ _) (assoc _ _ _) (assoc _ _ _) (transport-refl _) ⟩
        ((f [ v ]) [ w ] ∘i g [ w ]) .ihom ≡˘⟨ ap ihom (∘i-nat (f [ v ]) g w) ⟩
        (f [ v ] ∘i g) .ihom ∘ w           ∎
```
</details>
