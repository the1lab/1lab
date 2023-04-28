<!--
```agda
open import Cat.Displayed.Base
open import Cat.Displayed.Cartesian

open import Cat.Prelude

open import Cat.Internal.Base using (Internal-cat)

import Cat.Internal.Base
import Cat.Internal.Reasoning
import Cat.Internal.Morphism
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
open Cat.Internal.Morphism ℂ
open Displayed
open Internal-hom
```
-->

# Externalisation of internal categories

Every [internal category] in $\cB$ gives rise to a fibration over $\cB$,
known as the *externalisation* of the internal category.

[internal category]: Cat.Internal.Base.html

```agda
Externalise : Displayed B ℓ ℓ
Externalise = disp
  module Externalisation where
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

## Cartesian Maps

To really hammer home that point that the externalisation of an
internal category is the internal version of the family fibration,
we show that the cartesian morphisms are *precisely* the internal
isomorphisms.

The forward direction looks almost identical to the proof that
pointwise isomorphisms are cartesian morphisms in the family fibration.

```agda
internal-iso→cartesian
  : ∀ {Γ Δ : Ob} {u : Hom Γ Δ} {x : Hom Γ C₀} {y : Hom Δ C₀}
  → (f : Homi x (y ∘ u))
  → is-invertiblei f
  → is-cartesian Externalise u f
internal-iso→cartesian {Γ} {Δ} {u} {x} {y} f f-inv = cart where
  open is-cartesian
  module f-inv = is-invertiblei f-inv
  open f-inv using (invi)

  cart : is-cartesian _ _ _
  cart .universal {u′ = u′} m h′ =
    invi [ m ] ∘i coe0→1 (λ i → Homi u′ (assoc y u m i)) h′
  cart .commutes {u′ = u′} m h′ = Internal-hom-path $
    (f [ m ] ∘i invi [ m ] ∘i _) .ihom                ≡⟨ ap ihom (pullli (sym (∘i-nat f invi m))) ⟩
    (⌜ f ∘i invi ⌝ [ m ] ∘i _) .ihom                  ≡⟨ ap! f-inv.invli ⟩
    (⌜ idi _ [ m ] ⌝ ∘i _) .ihom                      ≡⟨ ap! (idi-nat m) ⟩
    (idi _ ∘i _) .ihom                                ≡⟨ ap ihom (idli _) ⟩
    (coe0→1 (λ i → Homi u′ (assoc y u m i)) h′) .ihom ≡⟨ transport-refl _ ⟩
    h′ .ihom ∎
  cart .unique {u′ = u′} {m = m} {h′ = h′} m′ p =
    Internal-hom-path $
    m′ .ihom                                                        ≡⟨ ap ihom (introli (Internal-hom-path (ap ihom (idi-nat m)))) ⟩
    (⌜ idi _ [ m ] ⌝ ∘i m′) .ihom                                   ≡⟨ ap! (ap (λ e → e [ m ]) (sym (f-inv.invri)) ∙ ∘i-nat _ _ _) ⟩
    ((invi [ m ] ∘i f [ m ]) ∘i m′) .ihom                           ≡⟨ ap ihom (pullri (Internal-hom-path (ap ihom p ∙ sym (transport-refl _)))) ⟩
    (invi [ m ] ∘i coe0→1 (λ i → Homi u′ (assoc y u m i)) h′) .ihom ∎
```

The reverse direction also mirrors the family fibration; we use the same
trick of factorizating the identity morphism.

```agda
cartesian→internal-iso
  : ∀ {Γ Δ : Ob} {u : Hom Γ Δ} {x : Hom Γ C₀} {y : Hom Δ C₀}
  → (f : Homi x (y ∘ u))
  → is-cartesian Externalise u f
  → is-invertiblei f
cartesian→internal-iso {Γ} {Δ} {u} {x} {y} f f-cart = f-inv where
  open is-cartesian f-cart
  open is-invertiblei
  open Inversesi
  open Externalisation

  f-inv : is-invertiblei f
  f-inv .invi =
    coe0→1 (λ i → Homi (y ∘ (idr u i)) (idr x i)) (universal id (idi _))
  f-inv .inversesi .invli =
    Internal-hom-path $
      (f ∘i f-inv .invi) .ihom                 ≡⟨ ∘i-ihom (ap (_ ∘_) (sym (idr _))) (sym (idr _)) (sym (idr _)) (sym (idr _)) (transport-refl _) ⟩
      (f [ id ] ∘i universal id (idi _)) .ihom ≡⟨ ap ihom (commutes id (idi _)) ⟩
      idi (y ∘ ⌜ u ∘ id ⌝) .ihom               ≡⟨ ap! (idr _) ⟩
      idi (y ∘ u) .ihom ∎
```

Unfortunately, the right inverse requires some nightmare transports.

```agda
  f-inv .inversesi .invri =
    Internal-hom-path $ {!!}
      -- (f-inv .invi ∘i f) .ihom                                     ≡⟨ ∘i-ihom refl refl (sym (idr _)) refl refl ⟩
      -- (f⁻¹∘f) .ihom                                                ≡⟨ ap ihom (unique f⁻¹∘f unique1) ⟩
      -- universal id f* .ihom ≡˘⟨ ap ihom (unique idi′ {!!}) ⟩
      -- idi x .ihom ∎
    where
      f⁻¹∘f : Homi x (x ∘ id)
      f⁻¹∘f = {!!}
      -- coe0→1 (λ i → Homi (y ∘ idr u i) (x ∘ id)) (universal id (idi _)) ∘i f

      -- f* : Homi x (y ∘ u ∘ id)
      -- f* = coe1→0 (λ i → Homi x (y ∘ (idr u i))) f

      -- id* : Homi (y ∘ u) (y ∘ u ∘ id)
      -- id* = coe1→0 (λ i → Homi (y ∘ u) (y ∘ idr u i)) (idi _)

      -- id*-ihom : id* .ihom ≡ idi (y ∘ u ∘ id) .ihom
      -- id*-ihom =
      --   id* .ihom                  ≡⟨ transport-refl _ ⟩
      --   idi (y ∘ u) .ihom          ≡˘⟨ idr _ ⟩
      --   idi (y ∘ u) .ihom ∘ id     ≡⟨ ap ihom (idi-nat id) ⟩
      --   idi ⌜ (y ∘ u) ∘ id ⌝ .ihom ≡⟨ ap! (sym (assoc _ _ _)) ⟩
      --   idi (y ∘ u ∘ id) .ihom ∎

      -- unique1 : f ∘i′ f⁻¹∘f ≡ f*
      -- unique1 = Internal-hom-path $
      --   (f [ id ] ∘i f⁻¹∘f) .ihom             ≡⟨ ∘i-ihom refl {!!} {!!} {!!} {!!} ⟩
      --   ((f ∘i′ universal id id*) ∘i f) .ihom  ≡⟨ ap (λ e → (e ∘i f) .ihom) (commutes _ _) ⟩
      --   (id* ∘i f) .ihom                       ≡⟨ ∘i-ihom refl (sym (ap (y ∘_) (idr u))) refl id*-ihom (sym (transport-refl _)) ⟩
      --   (idi _ ∘i f*) .ihom                    ≡⟨ ap ihom (idli _) ⟩
      --   f* .ihom ∎
```
