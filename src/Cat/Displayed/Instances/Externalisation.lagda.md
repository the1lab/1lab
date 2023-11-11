<!--
```agda
open import Cat.Displayed.GenericObject
open import Cat.Displayed.Cartesian
open import Cat.Displayed.Base
open import Cat.Internal.Base using (Internal-cat)
open import Cat.Prelude

import Cat.Internal.Reasoning
import Cat.Internal.Morphism
import Cat.Internal.Base
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

Every [internal category] $\bC$ in $\cB$ gives rise to a fibration over
$\cB$, known as the **externalisation** of $\bC$. The core idea is
almost the same as that of the [family fibration], but with $\bB$
playing the role of $\Sets$: The space of objects over $\cB$ will be the
_generalised objects_ $\cB(\Gamma, \bC_0)$.

[internal category]: Cat.Internal.Base.html

```agda
Externalise : Displayed B ℓ ℓ
Externalise = disp module Externalisation where
  disp : Displayed B ℓ ℓ
  disp .Ob[_] Γ = Hom Γ C₀
```

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
  disp .Hom[_] u x y = Homi x (y ∘ u)
  disp .Hom[_]-set _ _ _ = Internal-hom-set
  disp .id' = adjusti refl (sym (idr _)) (idi _)
  disp ._∘'_ {f = u} {g = v} f g = adjusti refl (sym (assoc _ _ _)) (f [ v ] ∘i g)
```

<details>
<summary>Unfortunately, proof assistants make establishing the axioms
fairly nasty. Associativity is especially bad.
</summary>

```agda
  disp .idr' f =
    Internal-hom-pathp refl (ap (_ ∘_) (idr _)) $
      (f [ id ] ∘i adjusti _ _ (idi _)) .ihom ≡⟨ ∘i-ihom refl (idr _) (idr _) (idr _) refl ⟩
      (f ∘i idi _) .ihom                      ≡⟨ ap ihom (idri _) ⟩
      f .ihom ∎
  disp .idl' {f = u} f =
    Internal-hom-pathp refl (ap (_ ∘_) (idl _)) $
      (adjusti _ _ (idi _) [ u ] ∘i f) .ihom ≡⟨ ∘i-ihom refl refl (ap (_∘ _) (idr _)) (ap ihom (idi-nat u)) refl ⟩
      (idi _ ∘i f) .ihom                     ≡⟨ ap ihom (idli _) ⟩
      f .ihom                                ∎
  disp .assoc' {w = a} {b} {c} {d} {f = u} {g = v} {h = w} f g h =
    Internal-hom-pathp refl (ap (_ ∘_) (assoc _ _ _)) $
    (f [ v ∘ w ] ∘i adjusti _ _ (g [ w ] ∘i h)) .ihom ≡⟨ ∘i-ihom refl refl refl refl (∘i-ihom refl refl (sym (assoc _ _ _)) g-path refl) ⟩
    (f [ v ∘ w ] ∘i g' ∘i h) .ihom                    ≡⟨ ap ihom (associ _ _ _) ⟩
    ((f [ v ∘ w ] ∘i g') ∘i h) .ihom                  ≡⟨ ∘i-ihom refl refl reassoc inner refl ⟩
    (adjusti _ _ (f [ v ] ∘i g) [ w ] ∘i h) .ihom     ∎
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

## Cartesian maps

To really hammer home that point that the externalisation of an internal
category is the internal version of the family fibration, we show that
the [[cartesian morphisms]] are *precisely* the internal isomorphisms.

The forward direction looks almost identical to the proof that pointwise
isomorphisms are cartesian morphisms in the family fibration.

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
  cart .universal {u' = u'} m h' =
    invi [ m ] ∘i adjusti refl (assoc y u m) h'
  cart .commutes {u' = u'} m h' =
    Internal-hom-path $
    (f [ m ] ∘i invi [ m ] ∘i _) .ihom      ≡⟨ ap ihom (pullli (sym (∘i-nat f invi m))) ⟩
    (⌜ f ∘i invi ⌝ [ m ] ∘i _) .ihom        ≡⟨ ap! f-inv.invli ⟩
    (⌜ idi _ [ m ] ⌝ ∘i _) .ihom            ≡⟨ ap! (idi-nat m) ⟩
    (idi _ ∘i _) .ihom                      ≡⟨ ap ihom (idli _) ⟩
    h' .ihom                                ∎
  cart .unique {u' = u'} {m = m} {h' = h'} m' p =
    Internal-hom-path $
    m' .ihom                                ≡⟨ ap ihom (introli (Internal-hom-path (ap ihom (idi-nat m)))) ⟩
    (⌜ idi _ [ m ] ⌝ ∘i m') .ihom           ≡⟨ ap! (ap (λ e → e [ m ]) (sym (f-inv.invri)) ∙ ∘i-nat _ _ _) ⟩
    ((invi [ m ] ∘i f [ m ]) ∘i m') .ihom   ≡⟨ ap ihom (pullri (Internal-hom-path (ap ihom p))) ⟩
    (invi [ m ] ∘i adjusti _ _ h') .ihom    ∎
```

The reverse direction also mirrors the corresponding construction for
the family fibration: we use the same trick of factoring the identity
morphism.

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
    adjusti (ap (y ∘_) (idr u)) (idr x) (universal id (idi _))
  f-inv .inversesi .invli =
    Internal-hom-path $
      (f ∘i f-inv .invi) .ihom                 ≡⟨ ∘i-ihom (ap (_ ∘_) (sym (idr _))) (sym (idr _)) (sym (idr _)) (sym (idr _)) refl ⟩
      (f [ id ] ∘i universal id (idi _)) .ihom ≡⟨ ap ihom (commutes id (idi _)) ⟩
      idi (y ∘ ⌜ u ∘ id ⌝) .ihom               ≡⟨ ap! (idr _) ⟩
      idi (y ∘ u) .ihom ∎
  f-inv .inversesi .invri =
    Internal-hom-path $
      (f-inv .invi ∘i f) .ihom               ≡⟨ ∘i-ihom refl refl (sym (idr _)) refl refl ⟩
      (adjusti _ _ (f-inv .invi) ∘i f) .ihom ≡⟨ ap ihom (unique (adjusti refl (sym (idr _)) (f-inv .invi) ∘i f) f∘f⁻¹∘f≡f*) ⟩
      universal id (adjusti _ _ f) .ihom     ≡˘⟨ ap ihom (unique (adjusti refl (sym (idr _)) (idi _)) f∘id≡f*) ⟩
      idi x .ihom ∎
```
<details>
<summary>The right inverse case needs some nightmare re-adjustments.
Unfold this at your own risk!
</summary>

```agda
    where
      f∘f⁻¹∘f≡f*
        : adjusti _ _ (f [ id ] ∘i adjusti _ _ (f-inv .invi) ∘i f)
        ≡ adjusti refl (ap (_ ∘_) (sym (idr _))) f
      f∘f⁻¹∘f≡f* = Internal-hom-path $
        (f [ id ] ∘i adjusti _ _ (f-inv .invi) ∘i f) .ihom
          ≡⟨ ap ihom (associ _ _ _) ⟩
        ((f [ id ] ∘i adjusti _ _ (f-inv .invi)) ∘i f) .ihom
          ≡⟨ ∘i-ihom refl (ap (y ∘_) (sym (idr _))) (sym (assoc _ _ _)) (∘i-ihom (ap (y ∘_) (sym (idr _))) refl refl refl refl) refl ⟩
        (adjusti refl (sym (assoc _ _ _)) (f [ id ] ∘i universal id (idi _)) ∘i adjusti refl (ap (y ∘_) (sym (idr _))) f) .ihom
          ≡⟨ ∘i-ihom refl refl refl (ap ihom (commutes id (idi _))) refl ⟩
        (idi _ ∘i adjusti refl (ap (y ∘_) (sym (idr _))) f) .ihom ≡⟨ ap ihom (idli _) ⟩
        f .ihom                                                                       ∎
      f∘id≡f* : adjusti _ _ (f [ id ] ∘i adjusti _ _ (idi x)) ≡ adjusti _ _ f
      f∘id≡f* = Internal-hom-path $
        (f [ id ] ∘i adjusti _ _ (idi x)) .ihom ≡⟨ ∘i-ihom refl (idr _) (idr _) (idr _) refl ⟩
        (f ∘i idi _) .ihom                      ≡⟨ ap ihom (idri _) ⟩
        f .ihom ∎
```
</details>

Finally, we show that the externalisation is a fibration. As per usual,
the argument proceeds in the same manner as for the family fibration.
Given a generalized object $y : \cB(\Delta C_0)$ and a morphism $u :
\cB(\Gamma, \Delta)$, we can take the pullback of $y$ to be $y \circ u$;
the lift of $u$ is then simply the (internal) identity morphism.

```agda
Externalisation-fibration : Cartesian-fibration Externalise
Externalisation-fibration .Cartesian-fibration.has-lift u y = cart-lift where
  open Cartesian-lift

  cart-lift : Cartesian-lift Externalise u y
  cart-lift .x' = y ∘ u
  cart-lift .lifting = idi _
  cart-lift .cartesian .is-cartesian.universal m h' =
    adjusti refl (assoc _ _ _) h'
  cart-lift .cartesian .is-cartesian.commutes m h' =
    Internal-hom-path $
      (⌜ idi _ [ m ] ⌝ ∘i _) .ihom ≡⟨ ap! (idi-nat m) ⟩
      (idi _ ∘i _) .ihom           ≡⟨ ap ihom (idli _) ⟩
      h' .ihom ∎
  cart-lift .cartesian .is-cartesian.unique {m = m} {h' = h'} m' p =
    Internal-hom-path $
      m' .ihom                  ≡˘⟨ ap ihom (idli _) ⟩
      (⌜ idi _ ⌝ ∘i m') .ihom   ≡⟨ ap! (sym (idi-nat m)) ⟩
      (idi _ [ m ] ∘i m') .ihom ≡⟨ ap ihom p ⟩
      h' .ihom                  ∎
```

## Generic objects

The externalisation is always globally small. We shall use the object of
objects $C_0$ as the base for our generic object, and the identity
morphism $id : C_0 \to C_0$ as the upstairs portion. Classifying maps
in the base are given by interpreting using a object $\cC(\Gamma, C_0)$ in
the externalisation as a morphism in the base, and the displayed
classifying map is the internal identity morphism, which is always
cartesian.

```agda
Externalisation-globally-small : Globally-small Externalise
Externalisation-globally-small = small where
  open Globally-small
  open Generic-object
  open is-cartesian

  small : Globally-small Externalise
  small .U = C₀
  small .Gen = id
  small .has-generic-ob .classify x = x
  small .has-generic-ob .classify' x =
    adjusti refl (sym (idl _)) (idi _)
```

<details>
<summary>However, showing the internal identity morphism needs to
be transported around a bit, so showing that it is cartesian requires
some tedious calculations.
</summary>

```agda
  small .has-generic-ob .classify-cartesian x' .universal m h' =
    adjusti refl (idl _) h'
  small .has-generic-ob .classify-cartesian x' .commutes m h' =
    Internal-hom-path $
      ∘i-ihom refl
        (sym (idl _))
        (sym (assoc _ _ _))
        (ap ihom (idi-nat _) ∙ ap (λ ϕ → idi ϕ .ihom) (sym (idl _)))
        refl
      ∙ ap ihom (idli h')
  small .has-generic-ob .classify-cartesian x' .unique {m = m} m' p =
    Internal-hom-path $
      sym (ap ihom (idli m'))
      ·· ∘i-ihom refl refl (ap (_∘ m) (sym (idl _))) (sym (ap ihom (idi-nat m))) refl
      ·· ap ihom p
```
</details>
